(ns foppl-compiler.core
  "This namespace contains an implementation of a FOPPL compiler following chapter
  3.1 of 'An Introduction to Probabilistic Programming' by van de Meent et al."
  (:require [clojure.set :as set]
            [anglican.runtime :refer :all]
            [foppl-compiler.desugar :refer [desugar]]
            [foppl-compiler.substitute :refer [substitute]]
            [foppl-compiler.partial-evaluation :refer [partial-evaluation]]
            [foppl-compiler.symbolic-simplify :refer [symbolic-simplify]]
            [foppl-compiler.primitives :refer :all]
            [foppl-compiler.analyze :refer [analyze empty-env empty-graph]]
            [foppl-compiler.free-vars :refer [free-vars]]))


(defn invert-graph [G]
  (reduce (fn [acc m] (merge-with set/union acc m))
          {}
          (for [[p children] G
                c children]
            {c #{p}})))


(defn topo-sort [{:keys [V A P]}]
  (let [terminals
        (loop [terminals []
               A A
               V V]
          (let [ts (filter (comp empty? (invert-graph A)) V)
                V (set/difference V (set ts))]
            (if (empty? V)
              (into terminals ts)
              (recur (into terminals ts)
                     (select-keys A V)
                     V))))]
    terminals))


(defn graph->instructions [[rho G E]]
  (conj
   (vec
    (for [t (topo-sort G)]
      [t ((:P G) t)]))
   [:return E]))

(defn eval-instructions [instructions]
  (reduce (fn [acc [s v]]
            (let [scope (list 'let (vec (apply concat acc))
                              v)]
              (binding [*ns* (find-ns 'foppl-compiler.core)]
                (conj acc [s (eval scope)]))))
          []
          instructions))

(defn program->graph [p]
  (reduce (fn [[rho G E] exp]
            (analyze rho true exp))
          [empty-env empty-graph nil]
          p))

(defn count-vertices [G]
  (count (:V G)))

(defn count-edges [G]
  (count (apply concat (vals (:A G)))))

(defn sample-from-prior [G]
  (-> G
     graph->instructions
     eval-instructions))

(defn observes->samples [instructions]
  (reduce (fn [acc ix]
            (let [[sym v] ix]
              (if (re-find #"observe\d+" (name sym))
                (if (= (first v) 'if)
                  (let [[_ cond [_ dist _] _] v]
                    (binding [*ns* (find-ns 'foppl-compiler.core)]
                      (if (eval (list 'let (vec (apply concat acc))
                                      cond))
                        (conj acc [sym (list 'sample* dist)])
                        acc)))
                  (let [[_ dist _] v]
                    (conj acc [sym (list 'sample* dist)])))
                (conj acc ix))))
          []
          instructions))

(defn sample-from-joint [G]
  (-> G
     graph->instructions
     observes->samples
     eval-instructions))

(defn bind-free-variables [G])

(defn get_graph [code]
  (->> code
       (map partial-evaluation)
             (map symbolic-simplify)
             (map desugar)
             program->graph
       )
  )


(defn count-graph [code]
  (let [G
        (->> code
             (map partial-evaluation)
             (map symbolic-simplify)
             (map desugar)
             program->graph
             second
             )]
    [(count-vertices G) (count-edges G)]))

(comment
  (->> '((defn observe-data [_ data slope bias]
         (let [xn (first data)
               yn (second data)
               zn (+ (* slope xn) bias)]
           (observe (normal zn 1.0) yn)
           (rest (rest data))))

       (let [slope (sample (normal 0.0 10.0))
             bias  (sample (normal 0.0 10.0))
             data (vector 1.0 2.1 2.0 3.9 3.0 5.3
                          4.0 7.7 5.0 10.2 6.0 12.9)]
         (loop 6 data observe-data slope bias)
         (vector slope bias)))
     (map partial-evaluation)
     (map symbolic-simplify)
     (map desugar)
     program->graph
     graph->instructions
     #_observes->samples
     #_eval-instructions
     )



  (->> '((let [a (sample (normal 0 1))
             b (sample (normal 0 1))
             c (sample (normal (second [(normal 0 1) b]) 1))]
         (observe (normal 0 1) 3)
         c))
     (map partial-evaluation)
     (map symbolic-simplify)
     (map desugar)
     program->graph
     graph->instructions
     observes->samples
     eval-instructions
     )


  (->> '((let [x (sample (normal 0 1))
             y (sample (normal 1 2))]
         (observe (normal x (+ 1 5)) 5)))
     (map partial-evaluation)
     (map symbolic-simplify)
     (map desugar)
     program->graph
     #_graph->instructions
     #_eval-instructions
     sample-from-prior)


  (analyze empty-env true '(loop 10 nil loop-iter a b))

  (analyze empty-env true '(if (sample (normal 0 1)) 2 3))


   ;; TODO improve fixed-point-simplify

  (count-graph
   '((defn observe-data [_ data slope bias]
       (let [xn (first data)
             yn (second data)
             zn (+ (* slope xn) bias)]
         (observe (normal zn 1.0) yn)
         (rest (rest data))))
     (let [slope (sample (normal 0.0 10.0))
           bias  (sample (normal 0.0 10.0))
           data (vector 1.0 2.1 2.0 3.9 3.0 5.3
                        4.0 7.7 5.0 10.2 6.0 12.9)]
       (loop 6 data observe-data slope bias)
       (vector slope bias))))

  (count-graph
   '((defn hmm-step [t states data trans-dists likes]
       (let [z (sample (get trans-dists
                            (last states)))]
         (observe (get likes z)
                  (get data t))
         (append states z)))
     (let [data [0.9 0.8 0.7 0.0 -0.025 -5.0 -2.0 -0.1
                 0.0 0.13 0.45 6 0.2 0.3 -1 -1]
           trans-dists [(discrete [0.10 0.50 0.40])
                        (discrete [0.20 0.20 0.60])
                        (discrete [0.15 0.15 0.70])]
           likes [(normal -1.0 1.0)
                  (normal 1.0 1.0)
                  (normal 0.0 1.0)]
           states [(sample (discrete [0.33 0.33 0.34]))]]
       (loop 16 states hmm-step data trans-dists likes))))


  (->> '((defn hmm-step [t states data trans-dists likes]
         (let [z (sample (get trans-dists
                              (last states)))]
           (observe (get likes z)
                    (get data t))
           (append states z)))
       (let [data [0.9 0.8 0.7 0.0 -0.025 -5.0 -2.0 -0.1
                   0.0 0.13 0.45 6 0.2 0.3 -1 -1]
             trans-dists [(discrete [0.10 0.50 0.40])
                          (discrete [0.20 0.20 0.60])
                          (discrete [0.15 0.15 0.70])]
             likes [(normal -1.0 1.0)
                    (normal 1.0 1.0)
                    (normal 0.0 1.0)]
             states [(sample (discrete [0.33 0.33 0.34]))]]
         (loop 16 states hmm-step data trans-dists likes)))
     (map partial-evaluation)
     (map symbolic-simplify)
     (map desugar)
     program->graph
     #_program->graph
     #_graph->instructions
     #_observes->samples
     #_eval-instructions)


  (->> '((let [weight-prior (normal 0 1)
      W_0 (foreach 10 []
            (foreach 1 [] (sample weight-prior)))
      W_1 (foreach 10 []
            (foreach 10 [] (sample weight-prior)))
      W_2 (foreach 1 []
            (foreach 10 [] (sample weight-prior)))

      b_0 (foreach 10 []
            (foreach 1 [] (sample weight-prior)))
      b_1 (foreach 10 []
            (foreach 1 [] (sample weight-prior)))
      b_2 (foreach 1 []
            (foreach 1 [] (sample weight-prior)))

      x   (mat-transpose [[1] [2] [3] [4] [5]])
      y   [[1] [4] [9] [16] [25]]
      h_0 (mat-tanh (mat-add (mat-mul W_0 x)
                             (mat-repmat b_0 1 5)))
      h_1 (mat-tanh (mat-add (mat-mul W_1 h_0)
                             (mat-repmat b_1 1 5)))
      mu  (mat-transpose
            (mat-tanh (mat-add (mat-mul W_2 h_1)
                               (mat-repmat b_2 1 5))))]
(foreach 5 [y_r y
            mu_r mu]
   (foreach 1 [y_rc y_r
               mu_rc mu_r]
      (observe (normal mu_rc 1) y_rc)))
[W_0 b_0 W_1 b_1]))
     #_count-graph
     (map partial-evaluation)
     (map symbolic-simplify)
     (map desugar)
     program->graph
     graph->instructions
     #_observes->samples
     eval-instructions
     )


  )



