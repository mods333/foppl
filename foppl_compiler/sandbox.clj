(ns compiler.test
 (:require [anglican.stat :as s])
 (:use clojure.repl
       [anglican core runtime emit
        [inference :only [collect-by]]]))

(defquery code3
 (let [mu (sample (normal 1 (sqrt 5)))
          sigma (sqrt 2)
          lik (normal mu sigma)]
      (observe lik 8)
      (observe lik 9)
      mu)
)

(->>(doquery :lmh code3 [])
   (take 10000000)
   (map :result ))
