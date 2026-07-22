(in-package "GPOLY")
(include-book "mul")
(include-book "../../field/pfield-adapter")

; Generate the exact-arity PFIELD adapter boundary from the same templates as
; the generic theory and concrete instances.  The constrained modulus keeps
; these definitions logical adapters rather than directly executable code.
(def-normalize-eval-instance
  pfield-fix-coefficients pfield-trim-trailing-zeros
  pfield-normalize pfield-eval
  gfield::pfield-fix gfield::pfield-zero
  gfield::pfield-add gfield::pfield-mul)

(defun pfield-coefficient-list-p (xs)
  (if (atom xs) (null xs)
    (and (gfield::pfield-element-p (car xs))
         (pfield-coefficient-list-p (cdr xs)))))
(defun pfield-polynomial-p (xs) (pfield-coefficient-list-p xs))

(defthm pfield-normalize-preserves-eval-from-generic
  (equal (pfield-eval (pfield-normalize poly) x)
         (pfield-eval poly x))
  :hints (("Goal" :by (:functional-instance
                        eval-of-normalize
                        (gfield::field-element-p gfield::pfield-element-p)
                        (gfield::field-fix gfield::pfield-fix)
                        (gfield::field-zero gfield::pfield-zero)
                        (gfield::field-one gfield::pfield-one)
                        (gfield::field-add gfield::pfield-add)
                        (gfield::field-mul gfield::pfield-mul)
                        (gfield::field-neg gfield::pfield-neg)
                        (gfield::field-inv gfield::pfield-inv)
                        (fix-coefficients pfield-fix-coefficients)
                        (trim-trailing-zeros pfield-trim-trailing-zeros)
                        (normalize pfield-normalize)
                         (eval pfield-eval)))))

(def-add-instance pfield-raw-add pfield-poly-add pfield-fix-coefficients
                  pfield-normalize gfield::pfield-add)
(def-scale-instance pfield-raw-scale pfield-poly-scale pfield-normalize
                    gfield::pfield-fix gfield::pfield-mul)
(def-mul-instance pfield-raw-mul pfield-poly-mul pfield-raw-add
                  pfield-raw-scale pfield-normalize gfield::pfield-zero)

(defthm pfield-eval-of-poly-scale-from-generic
  (equal (pfield-eval (pfield-poly-scale a poly) x)
         (gfield::pfield-mul a (pfield-eval poly x)))
  :hints (("Goal" :by (:functional-instance
                        eval-of-poly-scale
                        (gfield::field-element-p gfield::pfield-element-p)
                        (gfield::field-fix gfield::pfield-fix)
                        (gfield::field-zero gfield::pfield-zero)
                        (gfield::field-one gfield::pfield-one)
                        (gfield::field-add gfield::pfield-add)
                        (gfield::field-mul gfield::pfield-mul)
                        (gfield::field-neg gfield::pfield-neg)
                        (gfield::field-inv gfield::pfield-inv)
                        (fix-coefficients pfield-fix-coefficients)
                        (trim-trailing-zeros pfield-trim-trailing-zeros)
                        (normalize pfield-normalize)
                        (eval pfield-eval)
                        (raw-scale pfield-raw-scale)
                        (poly-scale pfield-poly-scale)))))

(defthm pfield-eval-of-raw-scale-from-generic
  (equal (pfield-eval (pfield-raw-scale a poly) x)
         (gfield::pfield-mul a (pfield-eval poly x)))
  :hints (("Goal" :by (:functional-instance
                        eval-of-raw-scale
                        (gfield::field-element-p gfield::pfield-element-p)
                        (gfield::field-fix gfield::pfield-fix)
                        (gfield::field-zero gfield::pfield-zero)
                        (gfield::field-one gfield::pfield-one)
                        (gfield::field-add gfield::pfield-add)
                        (gfield::field-mul gfield::pfield-mul)
                        (gfield::field-neg gfield::pfield-neg)
                        (gfield::field-inv gfield::pfield-inv)
                        (fix-coefficients pfield-fix-coefficients)
                        (trim-trailing-zeros pfield-trim-trailing-zeros)
                        (normalize pfield-normalize)
                        (eval pfield-eval)
                        (raw-scale pfield-raw-scale)
                        (poly-scale pfield-poly-scale)))))

(defthm pfield-eval-of-raw-add-from-generic
  (equal (pfield-eval (pfield-raw-add x y) a)
         (gfield::pfield-add (pfield-eval x a) (pfield-eval y a)))
  :hints (("Goal" :induct (pfield-raw-add x y)
           :in-theory (enable gfield::pfield-mul-left-distributive
                              gfield::pfield-add-associative))))

(defthm pfield-eval-of-add-from-generic
  (equal (pfield-eval (pfield-poly-add x y) a)
         (gfield::pfield-add (pfield-eval x a) (pfield-eval y a)))
  :hints (("Goal"
           :use ((:instance pfield-normalize-preserves-eval-from-generic
                            (poly (pfield-raw-add (pfield-normalize x)
                                                  (pfield-normalize y)))
                            (x a))
                 (:instance pfield-normalize-preserves-eval-from-generic
                            (poly x) (x a))
                 (:instance pfield-normalize-preserves-eval-from-generic
                            (poly y) (x a))
                 (:instance pfield-eval-of-raw-add-from-generic
                            (x (pfield-normalize x))
                            (y (pfield-normalize y))))
           :in-theory (disable pfield-normalize-preserves-eval-from-generic
                               pfield-eval-of-raw-add-from-generic))))


(defthm pfield-eval-of-raw-mul-from-generic
  (equal (pfield-eval (pfield-raw-mul f g) x)
         (gfield::pfield-mul (pfield-eval f x) (pfield-eval g x)))
  :hints (("Goal" :by (:functional-instance
                        eval-of-raw-mul
                        (gfield::field-element-p gfield::pfield-element-p)
                        (gfield::field-fix gfield::pfield-fix)
                        (gfield::field-zero gfield::pfield-zero)
                        (gfield::field-one gfield::pfield-one)
                        (gfield::field-add gfield::pfield-add)
                        (gfield::field-mul gfield::pfield-mul)
                        (gfield::field-neg gfield::pfield-neg)
                        (gfield::field-inv gfield::pfield-inv)
                        (fix-coefficients pfield-fix-coefficients)
                        (trim-trailing-zeros pfield-trim-trailing-zeros)
                        (normalize pfield-normalize)
                        (eval pfield-eval)
                        (raw-add pfield-raw-add)
                        (poly-add pfield-poly-add)
                        (raw-scale pfield-raw-scale)
                        (poly-scale pfield-poly-scale)
                        (raw-mul pfield-raw-mul)
                        (poly-mul pfield-poly-mul)))))

(defthm pfield-eval-of-poly-mul-from-generic
  (equal (pfield-eval (pfield-poly-mul f g) x)
         (gfield::pfield-mul (pfield-eval f x) (pfield-eval g x)))
  :hints (("Goal"
           :use ((:instance pfield-normalize-preserves-eval-from-generic
                            (poly (pfield-raw-mul (pfield-normalize f)
                                                  (pfield-normalize g)))
                            (x x))
                 (:instance pfield-normalize-preserves-eval-from-generic
                            (poly f) (x x))
                 (:instance pfield-normalize-preserves-eval-from-generic
                            (poly g) (x x))
                 (:instance pfield-eval-of-raw-mul-from-generic
                            (f (pfield-normalize f))
                            (g (pfield-normalize g))))
           :in-theory (disable pfield-normalize-preserves-eval-from-generic
                               pfield-eval-of-raw-mul-from-generic))))

(defthm pfield-raw-add-commutative-from-generic
  (equal (pfield-raw-add x y) (pfield-raw-add y x))
  :hints (("Goal" :by (:functional-instance
                        raw-add-commutative
                        (gfield::field-element-p gfield::pfield-element-p)
                        (gfield::field-fix gfield::pfield-fix)
                        (gfield::field-zero gfield::pfield-zero)
                        (gfield::field-one gfield::pfield-one)
                        (gfield::field-add gfield::pfield-add)
                        (gfield::field-mul gfield::pfield-mul)
                        (gfield::field-neg gfield::pfield-neg)
                        (gfield::field-inv gfield::pfield-inv)
                        (fix-coefficients pfield-fix-coefficients)
                        (raw-add pfield-raw-add)))))

; Ordinary executable F_7 DEFUNs generated from the same templates as the
; abstract algorithms.  Use :TRANS1 on this event to inspect the expansion.
(def-normalize-eval-instance
  f7-fix-coefficients f7-trim-trailing-zeros f7-normalize f7-eval
  gfield::f7-fix gfield::f7-zero gfield::f7-add gfield::f7-mul)

(defthm f7-normalize-preserves-eval-from-generic
  (equal (f7-eval (f7-normalize poly) x)
         (f7-eval poly x))
  :hints (("Goal" :by (:functional-instance
                        pfield-normalize-preserves-eval-from-generic
                        (gfield::pfield-modulus (lambda () 7))
                        (gfield::pfield-element-p gfield::f7-element-p)
                        (gfield::pfield-fix gfield::f7-fix)
                        (gfield::pfield-zero gfield::f7-zero)
                        (gfield::pfield-one gfield::f7-one)
                        (gfield::pfield-add gfield::f7-add)
                        (gfield::pfield-mul gfield::f7-mul)
                        (gfield::pfield-neg gfield::f7-neg)
                        (gfield::pfield-inv gfield::f7-inv)
                        (pfield-fix-coefficients f7-fix-coefficients)
                        (pfield-trim-trailing-zeros f7-trim-trailing-zeros)
                        (pfield-normalize f7-normalize)
                        (pfield-eval f7-eval))
           :in-theory (enable dm::primep))))
(def-add-instance f7-raw-add f7-poly-add f7-fix-coefficients f7-normalize
                  gfield::f7-add)
(def-neg-sub-instance f7-raw-neg f7-poly-neg f7-poly-sub f7-poly-add
                      f7-normalize gfield::f7-neg)
(def-scale-instance f7-raw-scale f7-poly-scale f7-normalize
                    gfield::f7-fix gfield::f7-mul)
(def-mul-instance f7-raw-mul f7-poly-mul f7-raw-add f7-raw-scale
                  f7-normalize gfield::f7-zero)

(defthm f7-eval-of-poly-add-from-generic
  (equal (f7-eval (f7-poly-add x y) a)
         (gfield::f7-add (f7-eval x a) (f7-eval y a)))
  :hints (("Goal" :by (:functional-instance
                        pfield-eval-of-add-from-generic
                        (gfield::pfield-modulus (lambda () 7))
                        (gfield::pfield-element-p gfield::f7-element-p)
                        (gfield::pfield-fix gfield::f7-fix)
                        (gfield::pfield-zero gfield::f7-zero)
                        (gfield::pfield-one gfield::f7-one)
                        (gfield::pfield-add gfield::f7-add)
                        (gfield::pfield-mul gfield::f7-mul)
                        (gfield::pfield-neg gfield::f7-neg)
                        (gfield::pfield-inv gfield::f7-inv)
                        (pfield-fix-coefficients f7-fix-coefficients)
                        (pfield-trim-trailing-zeros f7-trim-trailing-zeros)
                        (pfield-normalize f7-normalize)
                        (pfield-eval f7-eval)
                        (pfield-raw-add f7-raw-add)
                        (pfield-poly-add f7-poly-add))
           :in-theory (enable dm::primep))))

(defthm f7-eval-of-poly-scale-from-generic
  (equal (f7-eval (f7-poly-scale a poly) x)
         (gfield::f7-mul a (f7-eval poly x)))
  :hints (("Goal" :by (:functional-instance
                        pfield-eval-of-poly-scale-from-generic
                        (gfield::pfield-modulus (lambda () 7))
                        (gfield::pfield-element-p gfield::f7-element-p)
                        (gfield::pfield-fix gfield::f7-fix)
                        (gfield::pfield-zero gfield::f7-zero)
                        (gfield::pfield-one gfield::f7-one)
                        (gfield::pfield-add gfield::f7-add)
                        (gfield::pfield-mul gfield::f7-mul)
                        (gfield::pfield-neg gfield::f7-neg)
                        (gfield::pfield-inv gfield::f7-inv)
                        (pfield-fix-coefficients f7-fix-coefficients)
                        (pfield-trim-trailing-zeros f7-trim-trailing-zeros)
                        (pfield-normalize f7-normalize)
                        (pfield-eval f7-eval)
                        (pfield-raw-scale f7-raw-scale)
                        (pfield-poly-scale f7-poly-scale))
           :in-theory (enable dm::primep))))

(defthm f7-eval-of-poly-mul-from-generic
  (equal (f7-eval (f7-poly-mul f g) x)
         (gfield::f7-mul (f7-eval f x) (f7-eval g x)))
  :hints (("Goal" :by (:functional-instance
                        pfield-eval-of-poly-mul-from-generic
                        (gfield::pfield-modulus (lambda () 7))
                        (gfield::pfield-element-p gfield::f7-element-p)
                        (gfield::pfield-fix gfield::f7-fix)
                        (gfield::pfield-zero gfield::f7-zero)
                        (gfield::pfield-one gfield::f7-one)
                        (gfield::pfield-add gfield::f7-add)
                        (gfield::pfield-mul gfield::f7-mul)
                        (gfield::pfield-neg gfield::f7-neg)
                        (gfield::pfield-inv gfield::f7-inv)
                        (pfield-fix-coefficients f7-fix-coefficients)
                        (pfield-trim-trailing-zeros f7-trim-trailing-zeros)
                        (pfield-normalize f7-normalize)
                        (pfield-eval f7-eval)
                        (pfield-raw-add f7-raw-add)
                        (pfield-poly-add f7-poly-add)
                        (pfield-raw-scale f7-raw-scale)
                        (pfield-poly-scale f7-poly-scale)
                        (pfield-raw-mul f7-raw-mul)
                        (pfield-poly-mul f7-poly-mul))
           :in-theory (enable dm::primep))))

(assert-event (equal (f7-normalize '(1 2 0 0)) '(1 2)))
(assert-event (equal (f7-normalize '(0 0 0)) nil))
(assert-event (equal (f7-eval '(1 2 3) 2) 3))
(assert-event (equal (f7-eval '(6 6) 6) 0))
(assert-event (equal (f7-eval (f7-normalize '(1 2 3 0 0)) 2)
                     (f7-eval '(1 2 3 0 0) 2)))
(assert-event (equal (f7-poly-add '(1 2) '(2 3)) '(3 5)))
(assert-event (equal (f7-poly-add '(6 6) '(2 3)) '(1 2)))
(assert-event (equal (f7-poly-add '(1) '(2 3)) '(3 3)))
(assert-event (equal (f7-poly-add '(1 2) '(2 5)) '(3)))
(assert-event (equal (f7-poly-add '(1 2) '(6 5)) nil))
(assert-event (equal (f7-poly-neg '(1 2)) '(6 5)))
(assert-event (equal (f7-poly-sub '(1 2) '(2 3)) '(6 6)))
(assert-event (equal (f7-poly-sub '(1 2) '(1 2)) nil))
(assert-event (equal (f7-eval (f7-poly-add '(1 2) '(2 3)) 2) 6))
(assert-event (equal (f7-eval (f7-poly-neg '(1 2)) 2) 2))
(assert-event (equal (f7-eval (f7-poly-sub '(1 2) '(2 3)) 2) 4))
(assert-event
 (equal (f7-poly-add (f7-poly-add '(1 2) '(2 3)) '(4 5))
        (f7-poly-add '(1 2) (f7-poly-add '(2 3) '(4 5)))))
(assert-event (equal (f7-poly-scale 3 '(1 2 3)) '(3 6 2)))
(assert-event (equal (f7-poly-scale 0 '(1 2 3)) nil))
(assert-event (equal (f7-poly-scale 1 '(1 2 0 0)) '(1 2)))
(assert-event (equal (f7-poly-scale 2 '(1 0 4)) '(2 0 1)))
(assert-event (equal (f7-poly-scale 7 '(1 0 4)) nil))
(assert-event (equal (f7-poly-scale 2 '(1 . 4)) '(2)))
(assert-event (equal (f7-eval (f7-poly-scale 3 '(1 2 3)) 2)
                     (gfield::f7-mul 3 (f7-eval '(1 2 3) 2))))
(assert-event
 (equal (f7-poly-scale 2 (f7-poly-scale 3 '(1 2 3)))
        (f7-poly-scale (gfield::f7-mul 2 3) '(1 2 3))))
(assert-event
 (equal (f7-poly-scale 3 (f7-poly-add '(1 2) '(3 4)))
        (f7-poly-add (f7-poly-scale 3 '(1 2))
                     (f7-poly-scale 3 '(3 4)))))
(assert-event (equal (f7-poly-mul nil '(1 2)) nil))
(assert-event (equal (f7-poly-mul '(1 2) nil) nil))
(assert-event (equal (f7-poly-mul '(1) '(1 2)) '(1 2)))
(assert-event (equal (f7-poly-mul '(1 2) '(1)) '(1 2)))
(assert-event (equal (f7-poly-mul '(3) '(1 2)) '(3 6)))
; (1+2X)(3+4X) = 3+3X+X^2 over F_7.
(assert-event (equal (f7-poly-mul '(1 2) '(3 4)) '(3 3 1)))
(assert-event (equal (f7-poly-mul '(1 0 4) '(2 0 2)) '(2 0 3 0 1)))
(assert-event (equal (f7-poly-mul '(7 14) '(1 2)) nil))
(assert-event (equal (f7-poly-mul '(1 2 0 0) '(3 4 0)) '(3 3 1)))
(assert-event (equal (f7-poly-mul '(1 . bad-tail) '(3 4)) '(3 4)))
(assert-event
 (equal (f7-eval (f7-poly-mul '(1 2) '(3 4)) 2)
        (gfield::f7-mul (f7-eval '(1 2) 2) (f7-eval '(3 4) 2))))
