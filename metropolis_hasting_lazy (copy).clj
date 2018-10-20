(ns foppl-compiler.metropolis-hasting-lazy
  (:require [clojure.set :as set]
            [anglican.runtime :refer :all]
            [clojure.walk :refer :all]
            [foppl-compiler.core :refer :all]
            )
  (:use [anglican core runtime emit stat])
  )




(def test1 '((let [mu (sample (normal 1 (sqrt 5))  )
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
                                                                 (observe (get likes z) y)
                                                                 z))]
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


(def test_code_hs test3)
(def iterations 20)
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
  (if-not (nil? q)
    (eval (read-string (str "(" 'observe* " " (second q) " " x ")")))
    0
    )

  )


(defn get_joint [q_map Vx]
;;  (println Vx)

  (reduce
    (fn [acc ix]
;;       (println ix)
    (let [q (get q_map ix)]
      (if-not (nil? q)
      (+ acc  (eval q))
      acc
      ))


      )
    0
    Vx
    )


  )



(defn map-kv [m f X]
  (reduce-kv #(assoc %1 %2 (f X %3)) {} m))

(defn get_joint_sample [q_map Vx X]
;;   (println q_map)
  (reduce
    (fn [acc ix]
;;       (println ix)
        (+ acc (log_prob (get q_map ix) (get X ix)))
      )
    0
    Vx
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
;;         pv1s (get_joint_sample (postwalk-replace X q_sample) Vx X)
        pv1s  (get_joint_sample (map-kv q_sample postwalk-replace X) Vx X)
        pv2s (get_joint_sample (postwalk-replace X_new q_sample) Vx X_new)
        ]
;;     (println x)
;;     (println (get graph :A))
    (exp (- (+ pv2 pv2s) (+ pv1 pv1s)))
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
            alpha (accept x_var x_prev x_new q_map q_observe);; decide if X' should be accepted
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


;; (defn gibbs [x_init X q_sample q_observe s]

;;   ;;x_init is an initialization of all the varibles in X by sampling from prior
;;   ;; X has all the sample variable in it as a list sorted in topological order
;;   ;; s is the number of iterations
;; ;;   (println (last [x_init]))
;;   (loop [i 0
;;          result [x_init]
;;          ]
;;     (if (< i s)
;;       (recur (inc i) (append result (gibbs_step (last result) q_sample q_observe X)))
;;       result
;;       )
;;     )

;;   )


(defn gibbs [x_init X q_sample q_observe return_exp]
  (let [x_new (gibbs_step x_init q_sample q_observe X)
        new_return_val (eval (postwalk-replace x_new return_exp))
        ]
    (lazy-seq (cons new_return_val (gibbs x_new X q_sample q_observe return_exp)))

    )
  )


(postwalk-replace {'x 1} 'x)

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



;; (time (let [x (graph->instructions compiled_graph)
;;             return_exp (second (last x))
;;       sample_instr (get_sample_instr (drop-last  x))
;;       observe_instr (get_observe_instr (drop-last x))
;;       q_sample (create_qmap sample_instr)
;;       q_observe (create_qmap observe_instr)
;;       z (get_init sample_instr)
;; ;;       output (gibbs z sample_instr q_sample q_observe return_exp)
;;        ]

;; ;;         (clojure.pprint/pprint (second (last x)))
;; ;;         (clojure.pprint/pprint return_exp)
;; ;;         (clojure.pprint/pprint (take 10 output))
;; ;;         (let [foppl (->> output
;; ;;                                      (drop 500)
;; ;;                                      (take 2500)

;; ;;                                      )]
;; ;;           (println (mean foppl))
;; ;;           (println (std foppl))
;; ;;           )

;; ;;         (let [foppl (->> output
;; ;;                                     (drop 500)
;; ;;                                     (take 1000)
;; ;;                                     (map (fn [x]
;; ;;                                            (if (true? x)
;; ;;                                              1
;; ;;                                              0
;; ;;                                              )
;; ;;                                            )))]
;; ;;           (println (mean foppl))
;; ;;           (println (std foppl))
;; ;;           )
;; ;;      (clojure.pprint/pprint (get_mean output))
;; ;;    (clojure.pprint/pprint output)
;; ;;   (clojure.pprint/pprint x)
;; ;;  (clojure.pprint/pprint  (nth compiled_graph 1))

;;   ;;   (clojure.pprint/pprint (create_qmap x))

;;   ))





;; (let [anglican (->>
;;                       (doquery :smc
;;                                (query []
;;                                       (let [sprinkler true
;;                                             wet-grass true
;;                                             is-cloudy (sample (flip 0.5))

;;                                             is-raining (if (= is-cloudy true )
;;                                                          (sample (flip 0.8))
;;                                                          (sample (flip 0.2)))
;;                                             sprinkler-dist (if (= is-cloudy true)
;;                                                              (flip 0.1)
;;                                                              (flip 0.5))
;;                                             wet-grass-dist (if (and (= sprinkler true)
;;                                                                     (= is-raining true))
;;                                                              (flip 0.99)
;;                                                              (if (and (= sprinkler false)
;;                                                                       (= is-raining false))
;;                                                                (flip 0.0)
;;                                                                (if (or (= sprinkler true)
;;                                                                        (= is-raining true))
;;                                                                  (flip 0.9))))]
;;                                         (observe sprinkler-dist sprinkler)
;;                                         (observe wet-grass-dist wet-grass)
;;                                         is-raining)

;;                                       )
;;                                []
;;                                :number-of-particles 10000)
;;                       (drop 10000)
;;                       (map :result)
;;                       (take 100000)

;;                  )]
;;         (println anglican)
;; ;;         (println (std anglican))
;;   )

(defn build-prop-map [P]

  (->> P
       (filter (lambda [[k v]] (re-find #"sample\d+" (name k))))
       (map (lambda [[k v]] [(keyword k) (list 'lambda [] (second v))]))
       (into {})
       )
  )

(defn build-prop [graph]
  `(~'lambda [{:syms ~(vec (:V graph))} x#]
             ((get ~(build-prop-map (:P graph)) (keyword x#)))))
