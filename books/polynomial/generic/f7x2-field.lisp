(in-package "GPOLY")
(include-book "fixed-modulus-field")
(include-book "f7-irreducible-modular-inverse")
(include-book "f7x2-arithmetic")
(include-book "f7x2-inverse")

; Public field packaging for the concrete F7X2 presentation.  All operations stay
; executable definitions from the representation, arithmetic, and inverse books.
(local (defun f7x2-field-modulus ()
         '(1 0 1)))

(local
 (defthm f7x2-field-modulus-irreducible
   (f7-poly-irreducible-p
    (f7x2-field-modulus))
   :rule-classes nil
   :hints (("Goal"
            :use f7-x-squared-plus-one-is-irreducible
            :in-theory
            (disable f7-poly-irreducible-p
                     f7-poly-reducible-p)))))

(defthm f7x2-mul-inverse-left
  (implies (not (equal (f7x2-fix x) (f7x2-zero)))
           (equal (f7x2-mul (f7x2-inv x) x)
                  (f7x2-one)))
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
    (fixed-modulus-field-modulus f7x2-field-modulus)
    (fixed-modulus-field-element-p f7x2-element-p) (fixed-modulus-field-fix f7x2-fix)
    (fixed-modulus-field-zero f7x2-zero) (fixed-modulus-field-one f7x2-one)
    (fixed-modulus-field-add f7x2-add) (fixed-modulus-field-neg f7x2-neg)
    (fixed-modulus-field-sub f7x2-sub) (fixed-modulus-field-mul f7x2-mul)
    (fixed-modulus-field-inv f7x2-inv))))
          ("Subgoal 38" :use (f7x2-field-modulus-irreducible
             (:instance f7-poly-irreducible-p-definition (poly (f7x2-field-modulus))))
           :in-theory (disable f7x2-field-modulus f7-poly-irreducible-p
                               f7-poly-reducible-p
                               (:executable-counterpart f7-poly-irreducible-p)
                               (:executable-counterpart f7-poly-reducible-p)))
          ("Subgoal 36" :use f7-poly-reducible-p-full-witness-constraint-for-instantiation)
          ("Subgoal 33.2" :use gfield::f7-mul-inverse-right)
          ("Subgoal 30.9" :use ((:instance f7-mul-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
          ("Subgoal 30.4" :use ((:instance f7-mul-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
          ("Subgoal 29.11" :use ((:instance f7-add-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
          ("Subgoal 29.6" :use ((:instance f7-add-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
          ("Subgoal 26.2.1" :use gfield::f7-element-p-of-f7-fix
           :in-theory (enable gfield::f7-fix gfield::f7-element-p))
          ("Subgoal 26.2.1'''" :in-theory (enable mod))
          ("Subgoal 26.2.1'" :in-theory (enable mod))
          ("Subgoal 25.2.1'" :in-theory (enable mod))
          ("Subgoal 13.9.1'" :use ((:instance f7-poly-divmod-core)))
          ("Subgoal 10.9.1'" :use ((:instance f7-poly-divmod-core)))
          ("Subgoal 6.3'" :use f7-trim-change-implies-last-zero-for-divmod-instantiation)
          ("Subgoal 6.1" :use ((:instance f7-canonical-polynomial-p-implies-last-nonzero (p xs))))
          ("Subgoal 12.2.1'" :in-theory (enable mod))
          ("Subgoal 8.9.1'" :use ((:instance f7-poly-divmod-core)))
          ("Subgoal 2.2" :use ((:instance
            f7-poly-extended-euclidean-gcd-nonzero-second)))
          ("Subgoal 3" :use ((:instance
            f7-poly-extended-euclidean-gcd-zero-second)))))


; Exact GFIELD constraint shapes not already exported by the representation and
; arithmetic books.  Closure plus the canonical fixer gives the fixing laws.
(defthm f7x2-field-booleanp-of-element-p
  (booleanp (f7x2-element-p x))
  :hints (("Goal" :use ((:instance booleanp-of-f7x2-element-p)))))

(defthm f7x2-fix-of-f7x2-add
  (equal (f7x2-fix (f7x2-add x y)) (f7x2-add x y))
  :hints (("Goal"
           :use ((:instance f7x2-fix-when-f7x2-element-p
                            (x (f7x2-add x y)))
                 (:instance f7x2-element-p-of-f7x2-add
                            (first x) (second y)))
           :in-theory (theory 'minimal-theory))))

(defthm f7x2-fix-of-f7x2-mul
  (equal (f7x2-fix (f7x2-mul x y)) (f7x2-mul x y))
  :hints (("Goal"
           :use ((:instance f7x2-fix-when-f7x2-element-p
                            (x (f7x2-mul x y)))
                 (:instance f7x2-element-p-of-f7x2-mul
                            (first x) (second y)))
           :in-theory (theory 'minimal-theory))))

(defthm f7x2-fix-of-f7x2-neg
  (equal (f7x2-fix (f7x2-neg x)) (f7x2-neg x))
  :hints (("Goal"
           :use ((:instance f7x2-fix-when-f7x2-element-p
                            (x (f7x2-neg x)))
                 (:instance f7x2-element-p-of-f7x2-neg
                            (value x)))
           :in-theory (theory 'minimal-theory))))

(defthm f7x2-add-fixed-congruence
  (implies (and (equal (f7x2-fix x1) (f7x2-fix x2))
                (equal (f7x2-fix y1) (f7x2-fix y2)))
           (equal (f7x2-add x1 y1) (f7x2-add x2 y2)))
  :hints (("Goal"
           :use ((:instance f7x2-add-of-fixes
                            (first x1) (second y1))
                 (:instance f7x2-add-of-fixes
                            (first x2) (second y2)))
           :in-theory (theory 'minimal-theory))))

(defthm f7x2-mul-fixed-congruence
  (implies (and (equal (f7x2-fix x1) (f7x2-fix x2))
                (equal (f7x2-fix y1) (f7x2-fix y2)))
           (equal (f7x2-mul x1 y1) (f7x2-mul x2 y2)))
  :hints (("Goal"
           :use ((:instance f7x2-mul-of-fixes
                            (first x1) (second y1))
                 (:instance f7x2-mul-of-fixes
                            (first x2) (second y2)))
           :in-theory (theory 'minimal-theory))))

(defthm f7x2-field-add-of-fixes
  (equal (f7x2-add (f7x2-fix x) (f7x2-fix y))
         (f7x2-add x y))
  :hints (("Goal"
           :use ((:instance f7x2-add-of-fixes
                            (first x) (second y)))
           :in-theory (theory 'minimal-theory))))

(defthm f7x2-field-mul-of-fixes
  (equal (f7x2-mul (f7x2-fix x) (f7x2-fix y))
         (f7x2-mul x y))
  :hints (("Goal"
           :use ((:instance f7x2-mul-of-fixes
                            (first x) (second y)))
           :in-theory (theory 'minimal-theory))))

(defthm f7x2-field-mul-inverse-left
  (implies (not (equal (f7x2-fix x) (f7x2-zero)))
           (equal (f7x2-mul (f7x2-inv x) x)
                  (f7x2-one)))
  :hints (("Goal" :use ((:instance f7x2-mul-inverse-left)))))

(defun f7x2-div (numerator denominator)
  (declare (xargs :guard t))
  (f7x2-mul numerator (f7x2-inv denominator)))

(verify-guards f7x2-div)
