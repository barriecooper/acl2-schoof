(in-package "GPOLY")

(include-book "../polynomial/generic/pfield-instance")
(include-book "../field/examples/f11")

; The minimum ordinary-DEFUN polynomial instance: no polynomial arithmetic or
; power boundary is generated for this fixture.
(def-normalize-eval-instance
  f11-fix-coefficients f11-trim-trailing-zeros f11-normalize f11-eval
  gfield::f11-fix gfield::f11-zero gfield::f11-add gfield::f11-mul)

(defthm f11-normalize-preserves-eval
  (equal (f11-eval (f11-normalize poly) x) (f11-eval poly x))
  :hints (("Goal" :by (:functional-instance
                        pfield-normalize-preserves-eval-from-generic
                        (gfield::pfield-modulus (lambda () 11))
                        (gfield::pfield-element-p gfield::f11-element-p)
                        (gfield::pfield-fix gfield::f11-fix)
                        (gfield::pfield-zero gfield::f11-zero)
                        (gfield::pfield-one gfield::f11-one)
                        (gfield::pfield-add gfield::f11-add)
                        (gfield::pfield-mul gfield::f11-mul)
                        (pfield-fix-coefficients f11-fix-coefficients)
                        (pfield-trim-trailing-zeros f11-trim-trailing-zeros)
                        (pfield-normalize f11-normalize)
                        (pfield-eval f11-eval))
           :in-theory (enable dm::primep))))

(defun f11-coefficient-list-p (xs)
  (if (atom xs) (null xs)
    (and (gfield::f11-element-p (car xs))
         (f11-coefficient-list-p (cdr xs)))))
(defun f11-canonical-polynomial-p (xs)
  (equal (f11-normalize xs) xs))

(defthm f11-canonical-polynomial-p-of-normalize
  (f11-canonical-polynomial-p (f11-normalize xs))
  :hints (("Goal" :in-theory (enable f11-canonical-polynomial-p
                                      f11-normalize
                                      f11-fix-coefficients
                                      f11-trim-trailing-zeros))))

(defthm f11-element-p-of-eval
  (gfield::f11-element-p (f11-eval poly x)))

(defun f11-golden-cubic () '(6 1 0 1))

(defun f11-golden-curve-rhs (x)
  (f11-eval (f11-golden-cubic) x))

(defthm f11-golden-curve-rhs-explicit
  (equal (f11-golden-curve-rhs x)
         (gfield::f11-add
          (gfield::f11-mul (gfield::f11-mul x x) x)
          (gfield::f11-add x 6)))
  :hints (("Goal" :in-theory (enable f11-golden-curve-rhs
                                      f11-golden-cubic f11-eval))))

(defun f11-golden-curve-point-p (pair)
  (and (true-listp pair)
       (equal (len pair) 2)
       (equal (gfield::f11-mul (cadr pair) (cadr pair))
              (f11-golden-curve-rhs (car pair)))))

(defun f11-golden-enumerate-y (x y)
  (declare (xargs :measure (nfix (- 11 y))))
  (if (or (not (natp y)) (<= 11 y)) nil
    (if (f11-golden-curve-point-p (list x y))
        (cons (list x y) (f11-golden-enumerate-y x (+ 1 y)))
      (f11-golden-enumerate-y x (+ 1 y)))))

(defun f11-golden-enumerate-x (x)
  (declare (xargs :measure (nfix (- 11 x))))
  (if (or (not (natp x)) (<= 11 x)) nil
    (append (f11-golden-enumerate-y x 0)
            (f11-golden-enumerate-x (+ 1 x)))))

(defun f11-golden-affine-points () (f11-golden-enumerate-x 0))

(defconst *f11-golden-expected-affine-points*
  '((2 4) (2 7) (3 5) (3 6) (5 2) (5 9)
    (7 2) (7 9) (8 3) (8 8) (10 2) (10 9)))

; Independent executable regressions: validate the literal, and separately
; compare it with exhaustive traversal of all 121 canonical affine pairs.
(defun f11-golden-all-points-p (xs)
  (if (atom xs) (null xs)
    (and (f11-golden-curve-point-p (car xs))
         (f11-golden-all-points-p (cdr xs)))))

(assert-event (f11-golden-all-points-p *f11-golden-expected-affine-points*))
(assert-event (equal (f11-golden-affine-points)
                     *f11-golden-expected-affine-points*))
(assert-event (equal (len (f11-golden-affine-points)) 12))
(assert-event (equal (+ 1 (len (f11-golden-affine-points))) 13))

; Concrete characteristic-11 nonsingularity check: 4*1^3 + 27*6^2 /= 0.
(defun f11-golden-nonsingular-check ()
  (not (equal
        (gfield::f11-add
         (gfield::f11-mul 4 (gfield::f11-mul (gfield::f11-mul 1 1) 1))
         (gfield::f11-mul 27 (gfield::f11-mul 6 6)))
        (gfield::f11-zero))))
(assert-event (f11-golden-nonsingular-check))

(verify-guards f11-fix-coefficients)
(verify-guards f11-trim-trailing-zeros)
(verify-guards f11-normalize)
(verify-guards f11-eval)
(verify-guards f11-golden-cubic)
(verify-guards f11-golden-curve-rhs)
(verify-guards f11-golden-curve-point-p)
(verify-guards f11-golden-enumerate-y)
(verify-guards f11-golden-enumerate-x)
(verify-guards f11-golden-affine-points)
(verify-guards f11-golden-all-points-p)
(verify-guards f11-golden-nonsingular-check)
