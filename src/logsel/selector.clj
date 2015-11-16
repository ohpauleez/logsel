(ns logsel.selector
  (:require [clojure.walk :as walk]
            [clojure.string :as string]
            [clojure.core.logic :as logic]))

;; Declarative selectors and operations
;; --------------------------------------
;;
;; This is an illustration of how you can use core.logic to solve generic
;; tree-oriented problems.  One such problem is applying modifications using
;; CSS-like selections of some data structure (which is tree-like or list-like).
;; This solution can be expanded or extrapolated to solve other similar problems.

;; While `core.logic` offers a very rich foundation for logic programming,
;; unification provides the necessary functionality to solve most tree-oriented
;; logic-backed solutions.  Always start with unification and evolve outward
;; when it is not enough.

;; ### The problem
;; Given a data structure like:

(def test-data {:node-type :div
                :id "root"
                :contents [{:node-type :ul
                            :contents [{:node-type :li
                                        :class "odd row"
                                        :contents "foo"}
                                       {:node-type :li
                                        :class "even row"
                                        :contents "bar"}]}]})

;; ... we want declarative selection of sub-maps/nodes based on:
;;
;; * id
;; * class
;; * node type and count
;; * node children (all elements contained in some node)
;;
;; ... and then perform data modifications at those locations.

;; Some auxiliary functions for working with the selector strings:

(defn starts-with? [s v]
  (= (subs s 0 (count v)) v))

(defn ends-with? [s v]
  (= (subs s (- (count s) (count v))) v))

;; First, normalize all "syntax" into a data structure.  The goal here is to
;; translate something declarative that humans can reason about, into something
;; data-described that computers/programs can reason about.
;; All selectors are normalized into a sequence of maps
;; with an `:op` key and a `:val` for that particular op.  Multiple maps within
;; the sequences represent multiple steps for a selection (ie: sub-selections).
;; This format will allow us to dispatch functionality based on `:op`, which
;; will allow the system to be open for extension.

(defn parse-selector [sel]
  (cond
    (keyword? sel) [{:op :node-type :val sel}]
    (vector? sel) (do (assert (every? keyword? sel) (str "Path contains non-keyword: " sel))
                      (mapv #(hash-map :op :attr :val %) sel))
    (and (string? sel)
         (starts-with? sel ".")) [{:op :class :val (subs sel 1)}]
    (and (string? sel)
         (starts-with? sel "#")) [{:op :id :val (subs sel 1)}]
    (and (string? sel)
         (ends-with? sel ">")) (into
                                 (parse-selector (subs sel 0 (dec (count sel))))
                                 [{:op :contents}])
    (and (string? sel)
         (starts-with? sel "[")
         (ends-with? sel "]")) [{:op :attr
                                 :val (keyword (subs sel 1 (- (count sel) 1)))}]
    (string? sel) [{:op :node-type :val (keyword sel)}]
    (number? sel) [{:op :idx :val sel}]
    :else (assert false (str "can't parse selector " (pr-str sel)))))


(comment
  (parse-selector "#root")
  (parse-selector :div)
  (parse-selector "ul>")
  (parse-selector ".even")
  (parse-selector [:ul :li]))

;; From here, there are a few options:
;;
;; * Walk or match directly on the tree
;; * Normalize all nodes in the tree and unify per node
;;
;; The first one doesn't require any logic programming and should be straight
;; forward for most Clojure programmers.
;; Another option is normalizing all nodes of the tree into vectors,
;; and unifying across those vectors to match on the selector.  This approach
;; ends up looking very similar to Datomic's datalog query.
;;
;; #### So which one should we pick?
;; If you only want to do selections, walking the tree is very acceptable.
;; It's easy to write, easy to read, and extracts data as expected.
;;
;; If you want to perform operations on the tree as you go, walking won't work
;; because as you modify the tree, all further sections are broken (you changed
;; the tree).
;; To get around this, we can normalize the tree nodes, represent the updates
;; as new normalize nodes, and collapse all the normalized nodes (`reduce` and
;; build the tree back up).

;; Let's see a limited version of the naive walk-only/query-only solution first:

(defmulti walked-op
  (fn [sel node] (:op sel)))

(defmethod walked-op :id
  [sel node]
  (when (= (:id node)
           (:val sel))
    node))

(defmethod walked-op :node-type
  [sel node]
  (when (= (:node-type node)
           (:val sel))
    node))

(defmethod walked-op :class
  [sel node]
  (when (re-find (re-pattern (:val sel)) (or (:class node) ""))
    node))

(defmethod walked-op :default
  [sel node]
  (get node (:op sel)))

(defn walked-select
  ([selection data]
   ;; We have to special-case the `tree-seq` to our data structure
   (walked-select selection data :contents :contents))
  ([selection data branch? children]
   (let [sels (parse-selector selection)
         tree-nodes (tree-seq branch? children data)]
     (keep (fn [node]
             (reduce (fn [acc sel]
                       (if acc
                         (walked-op sel acc)
                         (reduced acc)))
                     node
                     sels))
           tree-nodes))))

(comment
  (walked-select "#root" test-data)
  (walked-select :li test-data)
  (walked-select ".even" test-data)
  (walked-select "#none" test-data)
  (walked-select "ul>" test-data))


;; Let's look at the node normalization approach.  To start, we need to turn
;; all nodes into Datoms (more or less)

(defn make-id []
  (gensym "id_"))

(declare map-tx)
(defn attr-tx
  "Return a new tx vector that contains the datoms needed to assert [id a v].
  If v is a map, create a sub entity. If v is a vector/seq create multiple datoms,
  one for each values in the collection."
  ([tx-data tx-id attr v]
   (cond
     (and (string? v)
          (= attr :class)) (reduce (fn [tx cls]
                                     (conj tx [tx-id attr cls]))
                                   tx-data
                                   (string/split v #" "))
     (and (coll? v)
          (empty? v)) tx-data

     (map? v) (let [tid (make-id)]
                (-> tx-data
                    (map-tx tid v)
                    (conj [tx-id attr tid])))

     (vector? v) (let [vid (make-id)]
                   (-> (reduce (fn [tx-data v-idx]
                                 (let [tid (make-id)
                                       new-v (get v v-idx)]
                                   (-> tx-data
                                       (attr-tx vid v-idx new-v))))
                               tx-data
                               (range (count v)))
                       (conj [tx-id attr vid])))

     :else (conj tx-data [tx-id attr v]))))

(defn map-tx
  "Call attr-tx for every k/v pair in `data` set (a hashmap),
  and build upon a vector/seq of tx-data."
  ([tx-data tx-id data]
   (reduce (fn [tx-data [attr-name v]]
             (attr-tx tx-data tx-id attr-name v))
           tx-data
           data)))

(def conj-set (fnil conj #{}))

(defn to-db [data]
  (let [root (make-id)
        datoms (map-tx [] root data)]
    {:datoms datoms
     :root root
     :index   {:eav (reduce
                      (fn [acc [e a v]]
                        (update-in acc [e a] conj-set v))
                      {}
                      datoms)
               :ave (reduce
                      (fn [acc [e a v]]
                        (update-in acc [a v] conj-set e))
                      {}
                      datoms)
               :vea (reduce
                      (fn [acc [e a v]]
                        (update-in acc [v e] conj-set a))
                      {}
                      datoms)}}))

(comment
  (:datoms (to-db test-data)))

;; Now we can unify against the datoms we just created

(def ground? (complement logic/lvar?))

(defn datom [db datom-vec]
  (let [[e a v] datom-vec
        {:keys [index datoms]} db
        {:keys [eav ave vea]} index]
    (fn [s]
      (let [e (logic/walk* s e) ;; If you move to CLJS, replace these w/ `-walk`
            a (logic/walk* s a)
            v (logic/walk* s v)]
        (condp = [(ground? e)
                  (ground? a)
                  (ground? v)]
          [true true true] (when (= (get-in eav [e a v]) v)
                             [s])
          [false true true] (for [e' (get-in ave [a v])]
                              (logic/unify s e e'))
          [true false false] (for [[a' vs] (get eav e)
                                   v' vs]
                               (logic/unify s [a v] [a' v']))
          [true false true] (for [a' (get-in vea [v e])]
                              (logic/unify s a a'))
          [true true false] (for [v' (get-in eav [e a])]
                              (logic/unify s v v'))
          [false false false] (for [datom datoms]
                                (logic/unify s [e a v] datom))
          [false false true] (for [[e' as] (get vea v)
                                   a' as]
                               (logic/unify s [e a] [e' a']))
          [false true false] (for [[v' es] (get ave a)
                                   e' es]
                               (logic/unify s [v e] [v' e'])))))))

(comment
  ;; We now have a function that we can use in `logic/fresh`
  (datom (to-db test-data) [(logic/lvar) :node-type :div]))

;; We need a way to convert specific datoms to paths into the origin tree of data

(defn path-to [db id]
  (let [{:keys [index root]} db]
    (loop [path []
           id id]
      (if (or (= id root)
              (nil? id))
        (reverse path)
        (let [idx (get-in index [:vea id])
              parent (ffirst idx)]
          (recur (conj path (first (get idx parent))) parent))))))

(comment
  (let [db (to-db test-data)
        [random-id :as random-datom] (rand-nth (:datoms db))
        path (path-to db random-id)]
    (println random-datom)
    (println path)
    (get-in test-data path)))

;; And now we can reduce through the datoms, building up a map
;; We'll walk through that map, patching up references as we go
;; As a final step, we'll convert "collections" (maps with numerical keys) to vectors

(defn datoms-id [datoms id]
  (filter #(= (first %) id) datoms))

(defn datoms->map [db]
  (let [{:keys [datoms root]} db
        id-map (reduce (fn [acc-map [id attr v :as datom]]
                         (if (id acc-map)
                           (cond
                             ;; We need to group together multi-string values
                             (string? v) (update-in acc-map [id attr] #(if (re-find (re-pattern v) %)
                                                                         %
                                                                         (str v " " %)))
                             :else acc-map)
                           (assoc acc-map id (apply hash-map
                                                    (mapcat rest (datoms-id datoms id))))))
                       {}
                       datoms)
        root-node (id-map root)
        resolved-map (walk/prewalk (fn [form]
                                     (if (symbol? form) (id-map form) form))
                                   root-node)]
    (walk/postwalk (fn [form]
                     (if (and (map? form)
                              (every? number? (keys form)))
                       (vec (vals form))
                       form))
                   resolved-map)))

(comment
  (let [db (to-db test-data)
        normalized-map (datoms->map db)]
    (prn normalized-map)
    (= normalized-map test-data)))

;; We can also just manipulate the datoms directly.
;; Let's turn the root node into a `span`, by adding an additional datom

(comment
  (let [{:keys [datoms root] :as db} (to-db test-data)
        new-datoms (conj datoms [root :node-type :span])
        normalized-map (datoms->map (assoc db :datoms new-datoms))]
    (prn normalized-map)
    (= normalized-map test-data)))

