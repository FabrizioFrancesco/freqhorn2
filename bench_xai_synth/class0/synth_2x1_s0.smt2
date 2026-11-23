(declare-var counter Real)
(declare-var counter_prime Real)
(declare-var x0 Real)
(declare-var x1 Real)
(declare-var x0_prime Real)
(declare-var x1_prime Real)
(declare-var w0 (Array Real (Array Real Real)))
(declare-var w1 (Array Real (Array Real Real)))
(declare-var w0_prime (Array Real (Array Real Real)))
(declare-var w1_prime (Array Real (Array Real Real)))
(declare-var b0 (Array Real Real))
(declare-var b1 (Array Real Real))
(declare-var b0_prime (Array Real Real))
(declare-var b1_prime (Array Real Real))
(define-fun max ((a Real) (b Real)) Real (ite (> a b) a b))
(define-fun ReLU ((a Real) (b Real) (c Real)) Real (ite (= c 1) a (max a b)))
(declare-rel inv ((Real)(Real) (Real) (Array Real (Array Real Real)) (Array Real (Array Real Real)) (Array Real Real) (Array Real Real)))
(declare-rel fail ())

(rule
	(=>
		(and
			(= x0 0.2335)
			(= x1 0.5004)
			(= counter 0)
			(= (select (select w0 0) 0) 1.0014)
			(= (select (select w0 1) 0) 0.9837)
			(= (select (select w1 0) 0) -0.6521)
			(= (select (select w1 1) 0) -0.9494)
			(= (select (select w0 0) 1) 0.495)
			(= (select (select w0 1) 1) 1.0249)
			(= (select (select w1 0) 1) 0)
			(= (select (select w1 1) 1) 0)
			(= (select b0 0) 0.0502)
			(= (select b1 0) 0.0276)
			(= (select b0 1) -0.5123)
			(= (select b1 1) 0)
		)
		(inv counter x0 x1 w0 w1 b0 b1)
	)
)

(rule
	(=>
		(and
			(inv counter x0 x1 w0 w1 b0 b1)
			(= x0_prime (ReLU (+ (* (select (select w0 0) counter) x0) (* (select (select w0 1) counter) x1) (select b0 counter)) 0 counter))
			(= x1_prime (ReLU (+ (* (select (select w1 0) counter) x0) (* (select (select w1 1) counter) x1) (select b1 counter)) 0 counter))
			(= w0_prime w0)
			(= w1_prime w1)
			(= b0_prime b0)
			(= b1_prime b1)
			(= counter_prime (+ counter 1))
			(or (= counter 0) (= counter 1))
		)
		(inv counter_prime x0_prime x1_prime w0_prime w1_prime b0_prime b1_prime)
	)
)

(rule
	(=>
		(and
			(inv counter x0 x1 w0 w1 b0 b1)
			(not (< x0 0))
			(>= counter 2)
		)
		fail
	)
)

(query fail)
