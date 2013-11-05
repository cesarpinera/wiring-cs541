(ns wiring.core
  (:require [clojure.string :refer [split]]
            [clojure.java.io :refer [writer]])
  (:import [org.sat4j.specs ISolver]
           [org.sat4j.minisat SolverFactory]
           [org.sat4j.core VecInt])
  (:gen-class))

(defn all-atoms
  [size]
  (into []
        (for [c ["L" "R" "C" "W"]
              i (range 1 (inc size))
              j (range 1 (inc size))]
          (str c i j)))
  )

(comment
  (all-atoms 2)
  )

(defn position
  "The numeric position (base 1) of the atom"
  [atoms atom]
  (inc (.indexOf atoms atom)))

(comment
  (position (all-atoms 2) "C12") ; 10
  (position (all-atoms 2) "W22") ; 16
  )

(defn ->or
  "Generates an or for an atom"
  [atoms atom]
  (position atoms atom))

(defn ->not-or
  "Generates a ¬ or for an atom"
  [atoms atom]
  (* -1 (position atoms atom)))

(comment
  (let [atoms (all-atoms 2)]
    (->or atoms "C11") ; 9
    )
  (let [atoms (all-atoms 2)]
    (->not-or atoms "C22") ; -12
    )
  )

(defn clause
  "Creates a clause"
  [& xs]
  (into [] xs))

(comment
  (let [atoms (all-atoms 2)]
    (clause 
     (->or atoms "C11")
     (->or atoms "W21")
     (->not-or atoms "L21"))
    )
  ;; [9 15 -3]
  )


(defn existence
  [atoms size side]
  (into []
        (map (fn [i]
               (into [] (flatten (for [j (range 1 (inc size))]
                                   (clause (->or atoms (str (case side
                                                              :left "L"
                                                              :right "R")
                                                            i j)))))))
             (range 1 (inc size)))))

(comment
  (let [r [[true false]
           [true false]]
        atoms (all-atoms (count r))]
    (existence atoms (count r) :left))
  ;; [[1 2] [3 4]]
  
  )

(defn clauses
  "Create the clauses for the wiring problem
    restrictions <- vector of vectors with boolean values"
  [atoms restrictions]
  (let [size (count restrictions)]
    (concat []
            ;; ∀i . ∃j . Lij
            (existence atoms size :left)
            ;; ∀i . ∃j . Rij
            (existence atoms size :right)
            
            ;; ∀ijk . (i ̸= j) → ¬Lik ∨ ¬Ljk
            (for  [i (range 1 (inc size))
                   j (range 1 (inc size))
                   k (range 1 (inc size))
                   :let [lik (str "L" i k)
                         ljk (str "L" j k)
                         rik (str "R" i k)
                         rjk (str "R" j k)]
                   :when (not (= i j))]
              (clause (->not-or atoms lik) (->not-or atoms ljk)))

            ;; ∀ijk . (i ̸= j) → ¬Rik ∨ ¬Rjk
            (for  [i (range 1 (inc size))
                   j (range 1 (inc size))
                   k (range 1 (inc size))
                   :let [lik (str "L" i k)
                         ljk (str "L" j k)
                         rik (str "R" i k)
                         rjk (str "R" j k)]
                   :when (not (= i j))]
              (clause (->not-or atoms rik) (->not-or atoms rjk)))

            ;; ∀hijk . ¬Lhj ∨ ¬Rik ∨ ¬Chi ∨ Wjk
            (for  [h (range 1 (inc size))
                   i (range 1 (inc size))
                   j (range 1 (inc size))
                   k (range 1 (inc size))
                   :let [lhj (str "L" h j)
                         rik (str "R" i k)
                         chi (str "C" h i)
                         wjk (str "W" j k)]]
              (clause (->not-or atoms lhj) (->not-or atoms rik) (->not-or atoms chi) (->or atoms wjk)))

            ;; ∀hijk . ¬Lhj ∨ ¬Rik ∨ ¬Wjk ∨ Chi
            (for  [h (range 1 (inc size))
                   i (range 1 (inc size))
                   j (range 1 (inc size))
                   k (range 1 (inc size))
                   :let [lhj (str "L" h j)
                         rik (str "R" i k)
                         chi (str "C" h i)
                         wjk (str "W" j k)]]
              (clause (->not-or atoms lhj) (->not-or atoms rik) (->not-or atoms wjk) (->or atoms chi)))

            ;; ∀ijkm.(k<i)∧(m>j)→¬Wij ∨¬Wkm
            (for  [i (range 1 (inc size))
                   j (range 1 (inc size))
                   k (range 1 (inc size))
                   m (range 1 (inc size))
                   :let [wik (str "W" i j)
                         wkm (str "W" k m)]
                   :when (and (< k i)
                              (> m j))]
              (clause (->not-or atoms wik) (->not-or atoms wkm)))

            ;; ∀ijkm . (k > i) ∧ (m < j) → ¬Wij ∨ ¬Wkm
            (for  [i (range 1 (inc size))
                   j (range 1 (inc size))
                   k (range 1 (inc size))
                   m (range 1 (inc size))
                   :let [wij (str "W" i j)
                         wkm (str "W" k m)]
                   :when (and (> k i)
                              (< m j))]
              (clause (->not-or atoms wij) (->not-or atoms wkm)))

            ;; You will also need to encode the constraints Cij that specify the connections to be made.
            ;; These are just singleton clauses.
            ;; Encode the negative cases ¬Cij as well as the positive ones.
            (for  [i (range 1 (inc size))
                   j (range 1 (inc size))
                   :let [cij (str "C" i j)
                         r (get (get restrictions (dec i)) (dec j))]]
              (if r
                (clause (->or atoms cij))
                (clause (->not-or atoms cij)))))))

(comment
  (def r [[false true false]
          [false true false]
          [true true true]])

  (clauses (all-atoms (count r)) r)
  )

(comment
  (let [r [[false true false]
           [false true false]
           [true true true]]
        atoms (all-atoms (count r))]
    (create-sat atoms (clauses atoms r) "test.sat")
    (dump-atoms atoms "test.atoms"))


  (let [r [[true]]
        atoms (all-atoms (count r))]
    (create-sat atoms (clauses atoms r) "test2.sat")
    (dump-atoms atoms "test2.atoms"))

  (let [r [[true false]
           [true false]]
        atoms (all-atoms (count r))]
    (create-sat atoms (clauses atoms r) "test3.sat")
    (dump-atoms atoms "test3.atoms"))

  )

(defn atoms-for-position
  "Assume a sequence of atoms in the form [L|R]ij (e.g. L12, R23)
   Find all those atoms for which j (i.e. the last character) is position"
  [atoms position]
  (filter #(.endsWith % (str position)) atoms))

(defn connectors-at-position
  "Finds the pair of connectors (left and right) at a given position from a list of atoms"
  [atoms position]
  (let [a (atoms-for-position atoms position)
        left (first (filter #(= \L (.charAt % 0)) a))
        right (first (filter #(= \R  (.charAt % 0)) a))]
    [(read-string (str (.charAt left 1)))
     (read-string (str (.charAt right 2)))]
    )
  )

(comment
  (atoms-for-position ["L12" "L23" "L31" "R11" "R23" "R32"] 1)
  ;; ("L31" "R11")
  (connectors-at-position ["L12" "L23" "L31" "R11" "R23" "R32"] 1)
  )

;; Use SAT4J to solve the problem
(defn solve
  [restrictions]
  (let [atoms (all-atoms (count restrictions))
        cs (clauses atoms restrictions)
        solver (SolverFactory/newDefault)]
    (.newVar solver (count atoms))
    (doseq [c cs]
      (.addClause solver (VecInt. (int-array c))))
    (when (.isSatisfiable solver)
      (let [model (.model solver)
            positive-atoms (map #(nth atoms (dec %))
                                (take (* 2 (count restrictions)) (filter pos? model)))]
        ;; Show those that are true
        (for [i (range 1 (inc (count restrictions)))]
          (connectors-at-position positive-atoms i))))))

(defn output-solution
  [solution]
  (doseq [l solution]
    (println (first l) (second l))))

(comment
  (let [r [[false true false]
           [false true false]
           [true true true]]]
    (output-solution (solve r)))
  )

(defn parse-restriction
  "Take a string with f or t characters represeting logical restrictions.
   Returns a vector with equivalent true/false values"
  [s]
  (into []
        (for [c s]
          (if (= \t c) true false))))

(defn parse-problem
  "Parses a problem as specified in the homework into a vector of restrictions"
  [filename]
  (let [unparsed (split (slurp filename) #"\n")]
    (into []
          (for [l unparsed]
            (parse-restriction l)))))

(comment
  (parse-restriction "ftt")
  ;; (false true true)
  (parse-problem "http://svcs.cs.pdx.edu/circuit-wiring/inst-1.txt")
  ;; [[false true true] [false false true] [true true false]]
  )

(defn -main
  "Find a solution to the problem and print the output"
  [& args]
  ;; work around dangerous default behaviour in Clojure
  (alter-var-root #'*read-eval* (constantly false))
  (let [filename (first args)
        s (solve (parse-problem filename))]
    (if s
      (output-solution s)
      (println "No solution found"))))

(comment
  (-main "http://svcs.cs.pdx.edu/circuit-wiring/inst-1.txt")

  )


