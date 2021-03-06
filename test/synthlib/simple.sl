;; the background theory is linear integer arithmetic
(set-logic LIA)

;; Name the function to be synthesize
;; Define its sort (type) and the sort of its variables
(synth-fun max2 ((x Int) (y Int)) Int

	   ;; Define the grammar for allowed expressions for max2
	   ((Start Int (x y 0 1
			  (+ Start Start)
			  (- Start Start)
			  (ite StartBool Start Start)))

	    (StartBool Bool ((and StartBool StartBool)
			     (or StartBool StartBool)
			     (not StartBool)
			     (<= Start Start)
			     (= Start Start)
			     (>= Start Start)))))

(declare-var x Int)
(declare-var y Int)

;; Define the formula Phi specifying the constraints
;; on the function max2 to be synthesized.

(constraint (>= (max2 x y) x))
(constraint (>= (max2 x y) y))
(constraint (or (= x (max2 x y)) (= y (max2 x y))))

;; Execute
(check-synth)
