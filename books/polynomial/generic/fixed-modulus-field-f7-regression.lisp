(in-package "GPOLY")
(include-book "fixed-modulus-field")
(include-book "f7-irreducible-modular-inverse")

; Concrete F7 regression for simultaneous fixed-modulus-field instantiation.
(defun f7-fixed-modulus-field-regression-modulus ()
  (f7-monomial (gfield::f7-one) 1))

(local (defthm f7-fixed-modulus-field-regression-modulus-canonical
         (f7-canonical-polynomial-p (f7-fixed-modulus-field-regression-modulus))
         :hints (("Goal" :in-theory (enable f7-fixed-modulus-field-regression-modulus)))))
(local (defthm f7-fixed-modulus-field-regression-modulus-degree
         (equal (f7-poly-degree (f7-fixed-modulus-field-regression-modulus)) 1)
         :hints (("Goal" :in-theory (enable f7-fixed-modulus-field-regression-modulus)))))

(local (defthm f7-fixed-modulus-field-regression-canonical-degree-one-poly-irreducible
  (implies (and (f7-canonical-polynomial-p poly)
                (equal (f7-poly-degree poly) 1))
           (f7-poly-irreducible-p poly))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:functional-instance
      canonical-degree-one-poly-irreducible
      (gfield::field-element-p gfield::f7-element-p)
      (gfield::field-fix gfield::f7-fix)
      (gfield::field-zero gfield::f7-zero)
      (gfield::field-one gfield::f7-one)
      (gfield::field-add gfield::f7-add)
      (gfield::field-mul gfield::f7-mul)
      (gfield::field-neg gfield::f7-neg)
      (gfield::field-inv gfield::f7-inv)
      (fix-coefficients f7-fix-coefficients)
      (trim-trailing-zeros f7-trim-trailing-zeros)
      (normalize f7-normalize)
      (coefficient-list-p f7-coefficient-list-p)
      (polynomial-p f7-polynomial-p)
      (canonical-polynomial-p f7-canonical-polynomial-p)
      (raw-add f7-raw-add) (poly-add f7-poly-add)
      (raw-neg f7-raw-neg) (poly-neg f7-poly-neg)
      (poly-sub f7-poly-sub)
      (raw-scale f7-raw-scale) (poly-scale f7-poly-scale)
      (raw-mul f7-raw-mul) (poly-mul f7-poly-mul)
      (zero-prefix f7-zero-prefix) (poly-shift f7-poly-shift)
      (monomial f7-monomial) (poly-degree f7-poly-degree)
      (poly-leading-coefficient f7-poly-leading-coefficient)
      (poly-unit-p f7-poly-unit-p)
      (poly-reducible-p f7-poly-reducible-p)
      (poly-reducible-p-witness f7-poly-reducible-p-witness)
      (poly-irreducible-p f7-poly-irreducible-p)))
    :in-theory (disable f7-poly-irreducible-p f7-fixed-modulus-field-regression-modulus))
   ("Subgoal 29" :use (f7-poly-reducible-p-full-witness-constraint-for-instantiation
          (:instance f7-poly-irreducible-p-definition)
          (:instance f7-poly-degree-semantics-from-pfield))
    :in-theory (e/d (f7-normalize) nil))
   ("Subgoal 28" :use f7-poly-reducible-p-full-witness-constraint-for-instantiation)
   ("Subgoal 25.2" :use gfield::f7-mul-inverse-right)
   ("Subgoal 22.4" :use ((:instance f7-mul-fixed-congruence-for-divmod-instantiation
                                    (x1 gfield::x1) (x2 gfield::x2)
                                    (y1 gfield::y1) (y2 gfield::y2))))
   ("Subgoal 21.11" :use ((:instance f7-add-fixed-congruence-for-divmod-instantiation
                                     (x1 gfield::x1) (x2 gfield::x2)
                                     (y1 gfield::y1) (y2 gfield::y2))))
   ("Subgoal 19.2.1'" :in-theory (enable mod))
   ("Subgoal 18.2.1''" :in-theory (enable mod))
   ("Subgoal 18.2.1'" :in-theory (enable mod))
   ("Subgoal 17.2.1''" :in-theory (enable mod))
   ("Subgoal 2.1" :use ((:instance f7-canonical-polynomial-p-implies-last-nonzero (p xs))))))
)

(defthm f7-fixed-modulus-field-regression-modulus-irreducible
  (f7-poly-irreducible-p (f7-fixed-modulus-field-regression-modulus))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f7-fixed-modulus-field-regression-canonical-degree-one-poly-irreducible
                                   (poly (f7-fixed-modulus-field-regression-modulus)))
                         f7-fixed-modulus-field-regression-modulus-canonical
                         f7-fixed-modulus-field-regression-modulus-degree)
            :in-theory (disable f7-fixed-modulus-field-regression-modulus
                                f7-poly-irreducible-p))))

(defun f7-fixed-modulus-field-regression-element-p (x) (equal (f7-poly-remainder x (f7-fixed-modulus-field-regression-modulus)) x))
(defun f7-fixed-modulus-field-regression-fix (x) (f7-poly-remainder x (f7-fixed-modulus-field-regression-modulus)))
(defun f7-fixed-modulus-field-regression-zero () nil)
(defun f7-fixed-modulus-field-regression-one () (f7-poly-reduced-one (f7-fixed-modulus-field-regression-modulus)))
(defun f7-fixed-modulus-field-regression-add (x y) (f7-poly-reduced-add x y (f7-fixed-modulus-field-regression-modulus)))
(defun f7-fixed-modulus-field-regression-neg (x) (f7-poly-reduced-neg x (f7-fixed-modulus-field-regression-modulus)))
(defun f7-fixed-modulus-field-regression-sub (x y) (f7-poly-reduced-sub x y (f7-fixed-modulus-field-regression-modulus)))
(defun f7-fixed-modulus-field-regression-mul (x y) (f7-poly-reduced-mul x y (f7-fixed-modulus-field-regression-modulus)))
(defun f7-fixed-modulus-field-regression-inv (x)
  (let ((fixed-x (f7-fixed-modulus-field-regression-fix x)))
    (if (equal fixed-x (f7-fixed-modulus-field-regression-zero))
        (f7-fixed-modulus-field-regression-zero)
      (f7-poly-modular-inverse fixed-x (f7-fixed-modulus-field-regression-modulus)))))

(defthm f7-fixed-modulus-field-regression-mul-associative
  (equal (f7-fixed-modulus-field-regression-mul (f7-fixed-modulus-field-regression-mul x y) z)
         (f7-fixed-modulus-field-regression-mul x (f7-fixed-modulus-field-regression-mul y z)))
  :hints (("Goal" :use ((:functional-instance
    fixed-modulus-field-mul-associative
    (gfield::field-element-p gfield::f7-element-p)
    (gfield::field-fix gfield::f7-fix)
    (gfield::field-zero gfield::f7-zero)
    (gfield::field-one gfield::f7-one)
    (gfield::field-add gfield::f7-add)
    (gfield::field-mul gfield::f7-mul)
    (gfield::field-neg gfield::f7-neg)
    (gfield::field-inv gfield::f7-inv)
    (gfield::field-div gfield::f7-div)
    (fix-coefficients f7-fix-coefficients)
    (trim-trailing-zeros f7-trim-trailing-zeros)
    (normalize f7-normalize)
    (coefficient-list-p f7-coefficient-list-p)
    (polynomial-p f7-polynomial-p)
    (canonical-polynomial-p f7-canonical-polynomial-p)
    (raw-add f7-raw-add) (poly-add f7-poly-add)
    (raw-neg f7-raw-neg) (poly-neg f7-poly-neg)
    (poly-sub f7-poly-sub)
    (raw-scale f7-raw-scale) (poly-scale f7-poly-scale)
    (raw-mul f7-raw-mul) (poly-mul f7-poly-mul)
    (const f7-const) (polynomial-one f7-polynomial-one)
    (zero-prefix f7-zero-prefix) (poly-shift f7-poly-shift)
    (monomial f7-monomial) (poly-degree f7-poly-degree)
    (poly-leading-coefficient f7-poly-leading-coefficient)
    (poly-monic-normalize f7-poly-monic-normalize)
    (poly-division-step-core f7-poly-division-step-core)
    (poly-division-step f7-poly-division-step)
    (poly-division-step-term f7-poly-division-step-term)
    (poly-division-step-next f7-poly-division-step-next)
    (poly-divmod-core f7-poly-divmod-core)
    (poly-divmod f7-poly-divmod)
    (poly-remainder f7-poly-remainder)
    (poly-reduced-p (lambda (x modulus)
                      (equal (f7-poly-remainder x modulus) x)))
    (poly-reduced-add f7-poly-reduced-add)
    (poly-reduced-neg f7-poly-reduced-neg)
    (poly-reduced-sub f7-poly-reduced-sub)
    (poly-reduced-mul f7-poly-reduced-mul)
    (poly-reduced-one f7-poly-reduced-one)
    (poly-euclidean-gcd f7-poly-euclidean-gcd)
    (poly-monic-euclidean-gcd f7-poly-monic-euclidean-gcd)
    (poly-extended-euclidean-gcd f7-poly-extended-euclidean-gcd)
    (poly-monic-extended-euclidean-gcd f7-poly-monic-extended-euclidean-gcd)
    (poly-modular-inverse f7-poly-modular-inverse)
    (poly-unit-p f7-poly-unit-p)
    (poly-reducible-p f7-poly-reducible-p)
    (poly-reducible-p-witness f7-poly-reducible-p-witness)
    (poly-irreducible-p f7-poly-irreducible-p)
    (fixed-modulus-field-modulus f7-fixed-modulus-field-regression-modulus)
    (fixed-modulus-field-element-p f7-fixed-modulus-field-regression-element-p) (fixed-modulus-field-fix f7-fixed-modulus-field-regression-fix)
    (fixed-modulus-field-zero f7-fixed-modulus-field-regression-zero) (fixed-modulus-field-one f7-fixed-modulus-field-regression-one)
    (fixed-modulus-field-add f7-fixed-modulus-field-regression-add) (fixed-modulus-field-neg f7-fixed-modulus-field-regression-neg)
    (fixed-modulus-field-sub f7-fixed-modulus-field-regression-sub) (fixed-modulus-field-mul f7-fixed-modulus-field-regression-mul)
    (fixed-modulus-field-inv f7-fixed-modulus-field-regression-inv))))
          ("Subgoal 5" :use (f7-fixed-modulus-field-regression-modulus-irreducible
             (:instance f7-poly-irreducible-p-definition (poly (f7-fixed-modulus-field-regression-modulus))))
           :in-theory (disable f7-fixed-modulus-field-regression-modulus f7-poly-irreducible-p
                               f7-poly-reducible-p
                               (:executable-counterpart f7-poly-irreducible-p)
                               (:executable-counterpart f7-poly-reducible-p)))
          ("Subgoal 4.9.1'" :use ((:instance f7-poly-divmod-core)))))

(defthm f7-fixed-modulus-field-regression-mul-inverse-left
  (implies (not (equal (f7-fixed-modulus-field-regression-fix x) (f7-fixed-modulus-field-regression-zero)))
           (equal (f7-fixed-modulus-field-regression-mul (f7-fixed-modulus-field-regression-inv x) x)
                  (f7-fixed-modulus-field-regression-one)))
  :rule-classes nil
  :hints (("Goal" :use ((:functional-instance
    fixed-modulus-field-mul-inverse-left
    (gfield::field-element-p gfield::f7-element-p)
    (gfield::field-fix gfield::f7-fix)
    (gfield::field-zero gfield::f7-zero)
    (gfield::field-one gfield::f7-one)
    (gfield::field-add gfield::f7-add)
    (gfield::field-mul gfield::f7-mul)
    (gfield::field-neg gfield::f7-neg)
    (gfield::field-inv gfield::f7-inv)
    (gfield::field-div gfield::f7-div)
    (fix-coefficients f7-fix-coefficients)
    (trim-trailing-zeros f7-trim-trailing-zeros)
    (normalize f7-normalize)
    (coefficient-list-p f7-coefficient-list-p)
    (polynomial-p f7-polynomial-p)
    (canonical-polynomial-p f7-canonical-polynomial-p)
    (raw-add f7-raw-add) (poly-add f7-poly-add)
    (raw-neg f7-raw-neg) (poly-neg f7-poly-neg)
    (poly-sub f7-poly-sub)
    (raw-scale f7-raw-scale) (poly-scale f7-poly-scale)
    (raw-mul f7-raw-mul) (poly-mul f7-poly-mul)
    (const f7-const) (polynomial-one f7-polynomial-one)
    (zero-prefix f7-zero-prefix) (poly-shift f7-poly-shift)
    (monomial f7-monomial) (poly-degree f7-poly-degree)
    (poly-leading-coefficient f7-poly-leading-coefficient)
    (poly-monic-normalize f7-poly-monic-normalize)
    (poly-division-step-core f7-poly-division-step-core)
    (poly-division-step f7-poly-division-step)
    (poly-division-step-term f7-poly-division-step-term)
    (poly-division-step-next f7-poly-division-step-next)
    (poly-divmod-core f7-poly-divmod-core)
    (poly-divmod f7-poly-divmod)
    (poly-remainder f7-poly-remainder)
    (poly-reduced-p (lambda (x modulus)
                      (equal (f7-poly-remainder x modulus) x)))
    (poly-reduced-add f7-poly-reduced-add)
    (poly-reduced-neg f7-poly-reduced-neg)
    (poly-reduced-sub f7-poly-reduced-sub)
    (poly-reduced-mul f7-poly-reduced-mul)
    (poly-reduced-one f7-poly-reduced-one)
    (poly-euclidean-gcd f7-poly-euclidean-gcd)
    (poly-monic-euclidean-gcd f7-poly-monic-euclidean-gcd)
    (poly-extended-euclidean-gcd f7-poly-extended-euclidean-gcd)
    (poly-monic-extended-euclidean-gcd f7-poly-monic-extended-euclidean-gcd)
    (poly-modular-inverse f7-poly-modular-inverse)
    (poly-unit-p f7-poly-unit-p)
    (poly-reducible-p f7-poly-reducible-p)
    (poly-reducible-p-witness f7-poly-reducible-p-witness)
    (poly-irreducible-p f7-poly-irreducible-p)
    (fixed-modulus-field-modulus f7-fixed-modulus-field-regression-modulus)
    (fixed-modulus-field-element-p f7-fixed-modulus-field-regression-element-p) (fixed-modulus-field-fix f7-fixed-modulus-field-regression-fix)
    (fixed-modulus-field-zero f7-fixed-modulus-field-regression-zero) (fixed-modulus-field-one f7-fixed-modulus-field-regression-one)
    (fixed-modulus-field-add f7-fixed-modulus-field-regression-add) (fixed-modulus-field-neg f7-fixed-modulus-field-regression-neg)
    (fixed-modulus-field-sub f7-fixed-modulus-field-regression-sub) (fixed-modulus-field-mul f7-fixed-modulus-field-regression-mul)
    (fixed-modulus-field-inv f7-fixed-modulus-field-regression-inv))))
          ("Subgoal 2.2" :use ((:instance
            f7-poly-extended-euclidean-gcd-nonzero-second)))
          ("Subgoal 3" :use ((:instance
            f7-poly-extended-euclidean-gcd-zero-second)))))

; Ground executions exercise the total wrapper boundary.  They are evidence
; about concrete execution only, not substitutes for the symbolic instances
; above.
(local
 (defthm f7-fixed-modulus-field-regression-zero-execution
   (and (equal (list (f7-fixed-modulus-field-regression-fix nil)
                     (f7-fixed-modulus-field-regression-element-p
                      (f7-fixed-modulus-field-regression-fix nil))
                     (f7-fixed-modulus-field-regression-add nil '(1))
                     (f7-fixed-modulus-field-regression-mul nil '(1))
                     (f7-fixed-modulus-field-regression-neg nil)
                     (f7-fixed-modulus-field-regression-inv nil))
               '(nil t (1) nil nil nil))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-add nil '(1)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-mul nil '(1)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-neg nil))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-inv nil)))
   :rule-classes nil))

(local
 (defthm f7-fixed-modulus-field-regression-one-execution
   (and (equal (list (f7-fixed-modulus-field-regression-fix '(1))
                     (f7-fixed-modulus-field-regression-element-p
                      (f7-fixed-modulus-field-regression-fix '(1)))
                     (f7-fixed-modulus-field-regression-add '(1) '(1))
                     (f7-fixed-modulus-field-regression-mul '(1) '(1))
                     (f7-fixed-modulus-field-regression-neg '(1))
                     (f7-fixed-modulus-field-regression-inv '(1)))
               '((1) t (2) (1) (6) (1)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-add '(1) '(1)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-mul '(1) '(1)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-neg '(1)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-inv '(1))))
   :rule-classes nil))

(local
 (defthm f7-fixed-modulus-field-regression-three-execution
   (and (equal (list (f7-fixed-modulus-field-regression-fix '(3))
                     (f7-fixed-modulus-field-regression-element-p
                      (f7-fixed-modulus-field-regression-fix '(3)))
                     (f7-fixed-modulus-field-regression-add '(3) '(1))
                     (f7-fixed-modulus-field-regression-mul '(3) '(1))
                     (f7-fixed-modulus-field-regression-neg '(3))
                     (f7-fixed-modulus-field-regression-inv '(3)))
               '((3) t (4) (3) (4) (5)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-add '(3) '(1)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-mul '(3) '(1)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-neg '(3)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-inv '(3))))
   :rule-classes nil))

(local
 (defthm f7-fixed-modulus-field-regression-noncanonical-execution
   (and (equal (list (f7-fixed-modulus-field-regression-fix '(8 1))
                     (f7-fixed-modulus-field-regression-element-p
                      (f7-fixed-modulus-field-regression-fix '(8 1)))
                     (f7-fixed-modulus-field-regression-add '(8 1) '(1))
                     (f7-fixed-modulus-field-regression-mul '(8 1) '(1))
                     (f7-fixed-modulus-field-regression-neg '(8 1))
                     (f7-fixed-modulus-field-regression-inv '(8 1)))
               '((1) t (2) (1) (6) (1)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-add '(8 1) '(1)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-mul '(8 1) '(1)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-neg '(8 1)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-inv '(8 1))))
   :rule-classes nil))

(local
 (defthm f7-fixed-modulus-field-regression-atom-execution
   (and (equal (list (f7-fixed-modulus-field-regression-fix 'bad)
                     (f7-fixed-modulus-field-regression-element-p
                      (f7-fixed-modulus-field-regression-fix 'bad))
                     (f7-fixed-modulus-field-regression-add 'bad '(1))
                     (f7-fixed-modulus-field-regression-mul 'bad '(1))
                     (f7-fixed-modulus-field-regression-neg 'bad)
                     (f7-fixed-modulus-field-regression-inv 'bad))
               '(nil t (1) nil nil nil))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-add 'bad '(1)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-mul 'bad '(1)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-neg 'bad))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-inv 'bad)))
   :rule-classes nil))

(local
 (defthm f7-fixed-modulus-field-regression-improper-list-execution
   (and (equal (list (f7-fixed-modulus-field-regression-fix '(1 1 . bad))
                     (f7-fixed-modulus-field-regression-element-p
                      (f7-fixed-modulus-field-regression-fix '(1 1 . bad)))
                     (f7-fixed-modulus-field-regression-add '(1 1 . bad) '(1))
                     (f7-fixed-modulus-field-regression-mul '(1 1 . bad) '(1))
                     (f7-fixed-modulus-field-regression-neg '(1 1 . bad))
                     (f7-fixed-modulus-field-regression-inv '(1 1 . bad)))
               '((1) t (2) (1) (6) (1)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-add '(1 1 . bad) '(1)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-mul '(1 1 . bad) '(1)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-neg '(1 1 . bad)))
        (f7-fixed-modulus-field-regression-element-p
         (f7-fixed-modulus-field-regression-inv '(1 1 . bad))))
   :rule-classes nil))
