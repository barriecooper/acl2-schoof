(in-package "GPOLY")
(include-book "add")
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

(defun pfield-raw-add (x y)
  (cond ((atom x) (pfield-fix-coefficients y))
        ((atom y) (pfield-fix-coefficients x))
        (t (cons (gfield::pfield-add (car x) (car y))
                 (pfield-raw-add (cdr x) (cdr y))))))
(defun pfield-poly-add (x y)
  (pfield-normalize
   (pfield-raw-add (pfield-normalize x) (pfield-normalize y))))

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
(defun f7-raw-add (x y)
  (cond ((atom x) (f7-fix-coefficients y))
        ((atom y) (f7-fix-coefficients x))
        (t (cons (gfield::f7-add (car x) (car y))
                 (f7-raw-add (cdr x) (cdr y))))))
(defun f7-poly-add (x y)
  (f7-normalize (f7-raw-add (f7-normalize x) (f7-normalize y))))
(defun f7-raw-neg (x)
  (if (atom x) nil
    (cons (gfield::f7-neg (car x)) (f7-raw-neg (cdr x)))))
(defun f7-poly-neg (x)
  (f7-normalize (f7-raw-neg (f7-normalize x))))
(defun f7-poly-sub (x y) (f7-poly-add x (f7-poly-neg y)))

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
