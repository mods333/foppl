(ns foppl-compiler.hmc
  (:require [clojure.set :as set]
            [clojure.core.matrix :as m]
            [anglican.runtime :refer :all]
            [clojure.walk :refer :all]
            [foppl-compiler.core :refer :all]
            [foppl-compiler.free-vars :refer [free-vars]]
            [foppl-compiler.reverse-diff :refer [reverse-diff* normal-pdf]]
            )
  (:use [anglican core runtime emit stat])
  )

(defn mat-mul [& args] (apply m/mmul args))
(defn mat-inv [& args] (apply m/inverse args))
(defn mat-transpose [& args] (apply m/transpose args))

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

(def test3 '((let [x (sample (normal 0 10))
                   y (sample (normal 0 10))]
               (observe (dirac (+ x y)) 7)
               [x y])))


(def ^:dynamic *primitive-procedures*
  "primitive procedures for Anglican semantics" ;; TODO check implications of this choice
  (let [;; higher-order procedures cannot be primitive
        exclude '#{loop
                   map reduce
                   filter keep keep-indexed remove
                   repeatedly
                   every? not-any? some
                   every-pred some-fn
                   comp juxt partial}
        ;; runtime namespaces
        runtime-namespaces '[clojure.core anglican.runtime foppl-compiler.primitives]]
    (set (keep (fn [[k v]]
                 (when (and (not (exclude k))
                            (fn? (var-get v)))
                   k))
               (mapcat ns-publics runtime-namespaces)))))

(def ^:dynamic *bound*
  (into *primitive-procedures* ['if 'let 'normal-pdf]))



(def test_hmc test1)
(def total_graph (get_graph test_hmc))
(def graph (second total_graph))

(defn append [& args] (apply conj args))

(defn create_return_exp [expr]
  (let [fn_arg (into [] (free-vars expr *bound*))]
    [(eval (list 'fn fn_arg expr)) fn_arg]
    )
  )

(defn sample_uniform []
  (sample* (uniform-continuous 0 1))
  )

(defn instr->map [x]
  (->> x
       (filter (fn [[k v]] (re-find #"sample\d+" (name k))))
       (reduce (fn [acc [k v]] (assoc acc k v)) {} )
       )


  )

(defn y-map->let-binding [y-map]
  (into [] (flatten (reduce-kv
                      (fn [m k v]
                        (append m [k v])
                        )
                      []
                      y-map
                      )))
  )


(defn p-map->free-vars [p-map]

  (into [] (distinct (flatten (reduce-kv
                                (fn [m k v]
                                  (append m (into [] (free-vars v *bound*)))
                                  )
                                []
                                p-map
                                ))))

  )

(p-map->free-vars '{x (normal 0 zkj) y (normal adsfk 2) z (normal dafksjfkl 3)})

(defn p-map->let-body [p-map]

  (reduce-kv
    (fn [m k v]
      (if (empty? m)
        v
        (list '+ m v)
        )
      )
    ()
    p-map
    )
  )

(defn dist->pdf [p-map]
  (reduce-kv
    (fn [m k v]
      (if (re-find #"sample\d+" (name k))
        (let [distr (second v)]
          (assoc m k (list (read-string (str (first distr) '-pdf)) k (second distr) (nth distr 2)))
          )
        (let [distr (second v)]
          (assoc m k (list (read-string (str (first distr) '-pdf)) (nth v 2) (second distr) (nth distr 2) ))
          )

        )
      )
    {}
    p-map
    )
  )




(defn graph->program [graph]

  (let [modified-p-map (dist->pdf (:P graph))
        fn_args (p-map->free-vars modified-p-map)
        let_body (p-map->let-body modified-p-map)
        ]
    (list 'fn fn_args let_body)
  )
  )

(def u-program (graph->program graph))
(def u-args (second u-program ))
(def grad-vector (eval (reverse-diff* (second u-program) (nth u-program 2))))


(defn get_R [M]
  (sample* (mvn (into [] (repeat (count u-args) 0)) M))
  )


;; (def rtest '(fn [x] (if (> x 5)
;;                       (if (> x 10)
;;                         (* 3 x)
;;                         (* 2 x))
;;                       (+ x 18)
;;                       )))

;; (let [output  (reverse-diff* (second rtest) (nth rtest 2))]
;;   (clojure.pprint/pprint output)
;;   )



;; (clojure.pprint/pprint graph)
;; (time (let [program (graph->program graph)
;;       grad_vector (time (eval (reverse-diff* (second program) (nth program 2))))
;;       eval_program (time (apply grad_vector [1 1]))
;;       eval_value (first eval_program)
;;       grad_program (apply (second eval_program) [1])
;;       ]
;;   (clojure.pprint/pprint program)
;; ;;   (println eval_value)
;;   (println grad_program)
;;   ))


;; (println u-args)
(defn get-U-grad [X]
  (apply (second (apply grad-vector X)) [1])
  )



(defn get-k [R M]
  (m/mul (/ 1 2) (mat-mul (mat-transpose R) (mat-inv M) R))
  )

(defn get-u [X]
  (first (apply grad-vector X))
  )

(defn get-H [X R M]
  (m/add (get-u X) (get-k R M))
  )


(defn update_xr [X R T eps]
  (loop [i 0
         X' X
         R' R
         ]
    (if (< i T)
      (let [X_new (m/add X' (m/mul eps R'))
            R_new (m/sub R' (m/mul eps (get-U-grad X_new)))
            ]
        (recur (inc i) X_new R_new)
        )
      [X' R']
      )

    )

  )

(defn leap-frog [X R T eps]

  (let [R_half (m/sub R (m/mul (/ eps 2) (get-U-grad X)))
        [X' R'] (update_xr X R_half T eps)
        X_new (m/add X' (m/mul eps R'))
        R_new (m/sub R (m/mul (/ eps 2) (get-U-grad X_new)))
        ]
    [X_new R_new]
    )
  )

(defn hmc [X T eps M]

  (let [R (apply get_R [M])
        [X' R'] (leap-frog X R T eps)
        u (apply sample_uniform [])
        ]
    (if (< u (exp (- (apply get-H [X R M]) (apply get-H [X' R' M]))))
      (lazy-seq (cons X' (hmc X' T eps M)))
      (lazy-seq (cons X (hmc X T eps M)))
      )
    )

  )

(let [x (graph->instructions total_graph)
      z (instr->map (eval-instructions x))
      z_vect (postwalk-replace z u-args)
      M (m/diagonal-matrix (repeat (count u-args) 1))
      T 10
      eps 0.000001
      output (hmc z_vect T eps M)
       ]
 (time  (let [foppl (->> output
                                     (drop 10000)
                                     (take 50000)

                                     )]
          (println (mean foppl))
          ))
)
(m/mul [1 2] [2 2])
