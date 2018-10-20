(ns foppl-compiler.symbolic-simplify
  (:require [anglican.runtime]
            [foppl-compiler.primitives :refer [append]]))

(def whitelist {'rest rest
                'first first
                'second second
                'last last
                'nth nth
                'conj conj
                'cons cons
                'vector vector
                'get get
                'append append
                })


(defn anglican-distribution? [sym]
  (when-let [v ((ns-publics 'anglican.runtime)
                (symbol (str "map->"
                             (name sym)
                             "-distribution")))]
    (extends? anglican.runtime/distribution
              (type (v {})))))

(comment
  (anglican-distribution? 'normals))


(defn dispatch-simplify [exp]
  (cond (and (list? exp)
             (= (first exp) 'let))
        :let

        (and (list? exp)
             (= (first exp) 'if))
        :if

        (and (list? exp)
             (= (first exp) 'defn))
        :defn

        (and (list? exp)
             (whitelist
              (first exp)))
        :application

        (and (list? exp)
             (anglican-distribution? (first exp)))
        :anglican-application

        (and (list? exp)
             (#{'sample 'observe} (first exp)))
        :anglican-application

        (list? exp)
        :list

        (vector? exp)
        :vector

        (map? exp)
        :map

        (seq? exp)
        :seq

        :else
        :unrelated))


(defmulti symbolic-simplify dispatch-simplify)

(defmethod symbolic-simplify :let
  [exp]
  (let [[_ bindings & body] exp]
    (apply list
           (concat (list 'let (vec
                               (mapcat (fn [[s v]] [s (symbolic-simplify v)])
                                       (partition 2 bindings))))
                   (map symbolic-simplify body)))))


(defmethod symbolic-simplify :if
  [exp]
  (let [[_ condition then else] exp
        new-cond (symbolic-simplify condition)]
    (cond (true? new-cond)
          (symbolic-simplify then)

          (false? new-cond)
          (symbolic-simplify else)

          :else
          (list 'if new-cond
                (symbolic-simplify then)
                (symbolic-simplify else)))))

(defmethod symbolic-simplify :defn
  [exp]
  (let [[_ name bindings & body] exp]
    (apply list (concat (list 'defn name bindings)
                        (map symbolic-simplify body)))))

(defmethod symbolic-simplify :application
  [exp]
  (try
    (let [f (symbolic-simplify (first exp))]
      (if-not (list? (symbolic-simplify (second exp)))
        ;; HACK captures cases were index (2nd arg) is symbol
        (if-let [res (apply (whitelist f) (map symbolic-simplify (rest exp)))]
          res
          (apply list
                 (conj (map symbolic-simplify (rest exp))
                       (first exp))))
        (apply list
               (conj (map symbolic-simplify (rest exp))
                     (first exp)))))
    (catch Exception _
      (try
        (apply list
               (conj (map symbolic-simplify (rest exp))
                     (first exp)))
        (catch Exception _
          exp)))))

(defmethod symbolic-simplify :anglican-application
  [exp]
  (apply list (conj (map symbolic-simplify (rest exp))
                    (first exp))))

(defmethod symbolic-simplify :vector
  [exp]
  (mapv symbolic-simplify exp))

(defmethod symbolic-simplify :list
  [exp]
  (apply list
         (map symbolic-simplify exp)))

(defmethod symbolic-simplify :seq
  [exp]
  (map symbolic-simplify exp))

(defmethod symbolic-simplify :map
  [exp]
  (into {}
        (map (fn [[k v]]
               [(symbolic-simplify k)
                (symbolic-simplify v)])
             exp)))

(defmethod symbolic-simplify :unrelated
  [exp]
  exp)



