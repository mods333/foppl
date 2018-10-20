(ns foppl-compiler.metropolis-hasting
  (:require [clojure.set :as set]
            [anglican.runtime :refer :all]
            [clojure.walk :refer :all]
            [foppl-compiler.core :refer :all]
            )
  (:use [anglican core runtime emit stat])
  )




(def test1 '((let [mu (sample (normal 1 (sqrt 5)))
                   sigma (sqrt 2)
                   lik (normal mu sigma)]
               (observe lik 8)
               (observe lik 9)
               mu)))

(def test2 '((defn observe-data [_ data slope bias]
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

(def test3 '((let [data [1.1 2.1 2.0 1.9 0.0 -0.1 -0.05]
                   likes (foreach 3 []
                                  (let [mu (sample (normal 0.0 10.0))
                                        sigma (sample (gamma 1.0 1.0))]
                                    (normal mu sigma)))
                   pi (sample (dirichlet [1.0 1.0 1.0]))
                   z-prior (discrete pi)
                   z (foreach 7 [y data]
                              (let [z (sample z-prior)]
                                (observe (get likes z) y)))]
               (= (first z) (second z)))))

(def test4 '((let [sprinkler true
                   wet-grass true
                   is-cloudy (sample (flip 0.5))

                   is-raining (if (= is-cloudy true )
                                (sample (flip 0.8))
                                (sample (flip 0.2)))
                   sprinkler-dist (if (= is-cloudy true)
                                    (flip 0.1)
                                    (flip 0.5))
                   wet-grass-dist (if (and (= sprinkler true)
                                           (= is-raining true))
                                    (flip 0.99)
                                    (if (and (= sprinkler false)
                                             (= is-raining false))
                                      (flip 0.0)
                                      (if (or (= sprinkler true)
                                              (= is-raining true))
                                        (flip 0.9))))]
               (observe sprinkler-dist sprinkler)
               (observe wet-grass-dist wet-grass)
               is-raining)))

(def test5 '((let [x (sample (normal 0 10))
                   y (sample (normal 0 10))]
               (observe (dirac (+ x y)) 7)
               [x y])))


(def test_code_hs test2)
(def iterations 5000)
(def compiled_graph (get_graph test_code_hs))
(def graph (second compiled_graph))

(defn append [& args] (apply conj args))



(defn get_sample_instr [x]
;;   (println x)
  (let [instr (reduce
                (fn [acc x]
;;                   (println (= (first (second x)) 'sample*))
                  (if (= (first (second x)) 'sample*)
                    (append acc x)
                    acc
                    )
                  )
                []
                x
                )
        ]

    instr
    )

  )

(defn get_observe_instr [x]
  (let [instr (reduce
                (fn [acc [ix_var ix_exp]]
                  (if (= (first ix_exp) 'observe*)
                    (append acc [ix_var ix_exp])
                    acc
                    )
                  )
                []
                x
                )
        ]
    instr
    )

  )


(defn create_qmap [X]
  (let  [q (reduce
             (fn [result a]
               (append result {(first a) (second a)})
               )
             {}
             X
             )]
    (dissoc q ':return)
    )

  )


(defn get_init [X]

  (let [x0 (reduce
             (fn [acc x]

               (let [eval_exp (eval (postwalk-replace acc (second x)))]
                 (if (seq? eval_exp)
                   (append acc {(first x) (into [] eval_exp)})
                   (append acc {(first x) eval_exp})
                   )
                 )

               )
             {}
             X
             )]
    x0
    )
  )



(defn log_prob [q x]
;;   (println q)
  (eval (read-string (str "(" 'observe* " " q " " x ")")))
  )

;; (log_prob '(normal 0 1) '1)

(defn get_joint [q_map Vx]
  (reduce
    (fn [acc [ix_var ix_exp]]
      (if (contains? Vx ix_var)
        (+ acc (eval ix_exp))
        acc
        )
      )
    0
    q_map
    )
  )

(defn get_joint_sample [q_map Vx X]
  (reduce
    (fn [acc [ix_var ix_exp]]
      (if (contains? Vx ix_var)
        (+ acc (log_prob ix_exp (get X ix_var)))
        acc
        )
      )
    0
    q_map
    )
  )

(defn accept [x X X_new q_sample q_observe]
  ;; x: the name of the varible updating
  ;; X: the old set of values assigned to variable
  ;; X_new : varible assignments with updated value for x
  ;; q_sample: the q_map for sample variables
  ;; q_observe: the q_map for observe variables

  (let [Vx   (get (get graph :A) x)
        pv1 (get_joint (postwalk-replace X q_observe) Vx)
        pv2 (get_joint (postwalk-replace X_new q_observe) Vx )
        pv1s (get_joint_sample (postwalk-replace X q_sample) Vx X)
        pv2s (get_joint_sample (postwalk-replace X_new q_sample) Vx X_new)
        ]
;;     (println x)
;;     (println (get graph :A))
    (exp (- pv2 pv1))
    )
  )

(defn sub_value [x_prev q_map x_var]
  (let [
         eval_exp (eval (postwalk-replace x_prev (get q_map x_var)))
        ]
    (if (seq? eval_exp)
      (into [] eval_exp)
      eval_exp
      )
    )
  )

(defn gibbs_step [x_init q_map q_observe X]

  (loop [i 0
         x_prev x_init
         ]

    (if (< i (count q_map))
      (let [x_var (first (get X i))
;;             q (postwalk-replace x_prev (get q_map x_var)) ;; get the expresiion for the variable and replace already computed varaible
;;             x_new (assoc x_prev x_var (eval q))  ;; X' : the gibbs step
            q (sub_value x_prev q_map x_var)
            x_new (assoc x_prev x_var q)
            alpha (accept x_var x_prev x_new q_map q_observe) ;; decide if X' should be accepted
            u (sample* (uniform-continuous 0 1))
            ]
;;         (println "the variable name is " x_var)
        (if (< u alpha)
          (recur (inc i) x_new)
          (recur (inc i) x_prev)
          )
        )
      x_prev
      )
    )

  )


(defn gibbs [x_init X q_sample q_observe s]

  ;;x_init is an initialization of all the varibles in X by sampling from prior
  ;; X has all the sample variable in it as a list sorted in topological order
  ;; s is the number of iterations
;;   (println (last [x_init]))
  (loop [i 0
         result [x_init]
         ]
    (if (< i s)
      (recur (inc i) (append result (gibbs_step (last result) q_sample q_observe X)))
      result
      )
    )

  )






;; (clojure.pprint/pprint (get_graph test4))
;; (clojure.pprint/pprint (get_instructions test2))
(defn get_sum [output]
   (reduce (fn [acc x]
            (merge-with + acc x)
            ) {} output)
  )

(defn div_count [output]
  (reduce (fn [acc [x_key x_val]]
          (assoc acc x_key (/ x_val iterations))
          )
        {}
        output
        )
  )


(defn get_mean [output]
  (->> output
       get_sum
       div_count
       )
  )



(time (let [x (graph->instructions compiled_graph)
            return_exp (second (last x))
      sample_instr (get_sample_instr (drop-last  x))
      observe_instr (get_observe_instr (drop-last x))
      q_sample (create_qmap sample_instr)
      q_observe (create_qmap observe_instr)
      z (get_init sample_instr)
;;       output (gibbs z sample_instr q_sample q_observe iterations)
       ]

        (clojure.pprint/pprint return_exp)
;;      (clojure.pprint/pprint (get_mean output))
;;    (clojure.pprint/pprint output)
;;   (clojure.pprint/pprint x)
;;  (clojure.pprint/pprint  (nth compiled_graph 1))

  ;;   (clojure.pprint/pprint (create_qmap x))

  ))


;; (sample* (discrete [0.015411096749137689 0.7918805924376423 0.19270831081322007]))


;; (clojure.pprint/pprint (get_graph test_code_hs))
