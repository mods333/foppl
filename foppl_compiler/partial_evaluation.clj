(ns foppl-compiler.partial-evaluation
  (:require [foppl-compiler.substitute :refer [substitute]]
            [foppl-compiler.symbolic-simplify :refer [symbolic-simplify]]
            [anglican.runtime]))


(defn deterministic? [exp]
  (let [stochastic-exp? (fn [e]
                          (and ((assoc (ns-map 'anglican.runtime)
                                       'sample :sample ;; TODO
                                       'observe :observe)
                                e)
                               (not ((ns-map 'clojure.core)
                                     e))))]
    (cond (or (seq? exp)
              (vector? exp)
              (map? exp))
          (zero? (count (filter stochastic-exp?
                                (flatten exp))))

          (stochastic-exp? exp)
          false

          :else
          true)))

(defn dispatch-partial-evaluation [exp]
  (cond (and (list? exp)
             (= (first exp) 'let))
        :let

        (and (list? exp)
             (= (first exp) 'defn))
        :defn

        (and (list? exp)
             (not ((ns-map 'clojure.core)
                   (first exp))))
        :unapplication

        (and (list? exp)
             (= (first exp) 'if))
        :if

        (list? exp)
        :application

        (seq? exp)
        :seq

        (map? exp)
        :map

        (vector? exp)
        :vector

        :else
        :unrelated))

(defmulti partial-evaluation dispatch-partial-evaluation)

(defmethod partial-evaluation :let
  [exp]
  (try
    (eval exp)
    (catch Exception _
      (let [[_ bindings & body] exp
            evaled-bindings (vec
                             (mapcat (fn [[s v]] [s (partial-evaluation v)])
                                     (partition 2 bindings)))]
        (apply list
               (concat (list 'let evaled-bindings)
                       (map (fn [exp]
                              (partial-evaluation exp)
                              ;; TODO more aggressive inlining
                              #_(if (deterministic? exp)
                                (let [sub-exp (reduce (fn [exp [s v]]
                                                        (substitute exp s v))
                                                      exp
                                                      (partition 2 evaled-bindings))]
                                  (partial-evaluation sub-exp))
                                (partial-evaluation exp)))
                            body)))))))

(defmethod partial-evaluation :defn
  [exp]
  (let [[_ name bindings & body] exp]
    (apply list (concat (list 'defn name bindings)
                        (map partial-evaluation body)))))

(defmethod partial-evaluation :unapplication
  [exp]
  (apply list (conj (map partial-evaluation (rest exp))
                    (first exp))))


(defmethod partial-evaluation :if
  [exp]
  (let [[_ cond then else] exp
        eval-cond (partial-evaluation cond)]
    (cond (true? eval-cond)
          (partial-evaluation then)

          (false? eval-cond)
          (partial-evaluation else)

          :else
          (list 'if eval-cond
                (partial-evaluation then)
                (partial-evaluation else)))))

(defmethod partial-evaluation :application
  [exp]
  (try
    (eval exp)
    (catch Exception _
      (apply list
             (conj (map partial-evaluation (rest exp))
                   (first exp))))))

(defmethod partial-evaluation :seq
  [exp]
  (map partial-evaluation exp))

(defmethod partial-evaluation :vector
  [exp]
  (mapv partial-evaluation exp))

(defmethod partial-evaluation :unrelated
  [exp]
  exp)

(defmethod partial-evaluation :map
  [exp]
  (->> (interleave (map partial-evaluation (keys exp))
                 (map partial-evaluation (vals exp)))
     (partition 2)
     (map vec)
     (into {})))


(defn fixed-point-simplify [exp]
  (loop [exp exp]
    (let [new-exp (-> exp
                      partial-evaluation
                      symbolic-simplify)]
      (if (= new-exp exp)
        exp
        (recur new-exp)))))
