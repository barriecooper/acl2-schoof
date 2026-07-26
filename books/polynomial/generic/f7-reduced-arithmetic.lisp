(in-package "GPOLY")
(include-book "f7-division")
(include-book "reduced-ring")

; Concrete execution witnesses use the same transparent operation/remainder
; chain as the generic boundary.  They do not introduce a concrete quotient
; object or duplicate the generic structural proofs.
(def-reduced-ring-instance
 f7-poly-reduced-add f7-poly-reduced-neg f7-poly-reduced-sub
 f7-poly-reduced-mul f7-poly-reduced-one
 f7-poly-add f7-poly-neg f7-poly-sub f7-poly-mul f7-polynomial-one
 f7-poly-remainder f7-normalize f7-canonical-polynomial-p
 f7-poly-reduced-mul-right-distributive
 poly-reduced-mul-right-distributive
 ((gfield::field-element-p gfield::f7-element-p)
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
  (raw-add f7-raw-add)
  (poly-add f7-poly-add)
  (raw-neg f7-raw-neg)
  (poly-neg f7-poly-neg)
  (poly-sub f7-poly-sub)
  (raw-scale f7-raw-scale)
  (poly-scale f7-poly-scale)
  (raw-mul f7-raw-mul)
  (poly-mul f7-poly-mul)
  (zero-prefix f7-zero-prefix)
  (poly-shift f7-poly-shift)
  (monomial f7-monomial)
  (poly-degree f7-poly-degree)
  (poly-leading-coefficient f7-poly-leading-coefficient)
  (poly-division-step-core f7-poly-division-step-core)
  (poly-division-step f7-poly-division-step)
  (poly-division-step-term f7-poly-division-step-term)
  (poly-division-step-next f7-poly-division-step-next)
  (poly-divmod-core f7-poly-divmod-core)
  (poly-divmod f7-poly-divmod)
  (poly-remainder f7-poly-remainder)
  (poly-reduced-add f7-poly-reduced-add)
  (poly-reduced-neg f7-poly-reduced-neg)
  (poly-reduced-sub f7-poly-reduced-sub)
  (poly-reduced-mul f7-poly-reduced-mul)
  (polynomial-one f7-polynomial-one)
  (poly-reduced-one f7-poly-reduced-one))
 (:in-theory (enable f7-poly-reduced-add f7-poly-reduced-mul))
 (("Subgoal 29.2" :use gfield::f7-mul-inverse-right)
  ("Subgoal 26.9"
   :use ((:instance f7-mul-fixed-congruence-for-divmod-instantiation
                    (x1 gfield::x1) (x2 gfield::x2)
                    (y1 gfield::y1) (y2 gfield::y2))))
  ("Subgoal 26.4"
   :use ((:instance f7-mul-fixed-congruence-for-divmod-instantiation
                    (x1 gfield::x1) (x2 gfield::x2)
                    (y1 gfield::y1) (y2 gfield::y2))))
  ("Subgoal 25.11"
   :use ((:instance f7-add-fixed-congruence-for-divmod-instantiation
                    (x1 gfield::x1) (x2 gfield::x2)
                    (y1 gfield::y1) (y2 gfield::y2))))
  ("Subgoal 25.6"
   :use ((:instance f7-add-fixed-congruence-for-divmod-instantiation
                    (x1 gfield::x1) (x2 gfield::x2)
                    (y1 gfield::y1) (y2 gfield::y2))))
  ("Subgoal 22.2.1" :use gfield::f7-element-p-of-f7-fix
   :in-theory (enable gfield::f7-fix gfield::f7-element-p))
  ("Subgoal 22.2.1'''" :in-theory (enable mod))
  ("Subgoal 22.2.1'" :in-theory (enable mod))
  ("Subgoal 21.2.1'" :in-theory (enable mod))
  ("Subgoal 9.9.1'" :use ((:instance f7-poly-divmod-core)))
  ("Subgoal 8.9.1'" :use ((:instance f7-poly-divmod-core)))
  ("Subgoal 6.9.1'" :use ((:instance f7-poly-divmod-core)))
  ("Subgoal 2.3'"
   :use f7-trim-change-implies-last-zero-for-divmod-instantiation)
  ("Subgoal 2.1"
   :use ((:instance f7-canonical-polynomial-p-implies-last-nonzero
                    (p xs))))
  ("Subgoal 8.2.1'" :in-theory (enable mod)))
 (:rewrite)
 f7-poly-reduced-add-commutative
 poly-reduced-add-commutative
 ((:rewrite :loop-stopper nil))
 nil
 f7-poly-reduced-add-associative
 poly-reduced-add-associative
 (:rewrite)
 nil
 f7-poly-reduced-add-zero-left
 poly-reduced-add-zero-left
 (:rewrite)
 nil
 f7-poly-reduced-add-zero-right
 poly-reduced-add-zero-right
 (:rewrite)
 nil
 f7-poly-reduced-add-inverse-left
 poly-reduced-add-inverse-left
 (:rewrite)
 nil
 f7-poly-reduced-add-inverse-right
 poly-reduced-add-inverse-right
 (:rewrite)
 nil
 f7-poly-reduced-neg-double
 poly-reduced-neg-double
 (:rewrite)
 (("Goal" :in-theory (enable f7-poly-reduced-neg)))
 f7-poly-reduced-neg-zero
 poly-reduced-neg-zero
 (:rewrite)
 nil
 f7-poly-reduced-sub-self
 poly-reduced-sub-self
 (:rewrite)
 nil
 f7-poly-reduced-sub-zero-right
 poly-reduced-sub-zero-right
 (:rewrite)
 nil
 f7-poly-reduced-sub-zero-left
 poly-reduced-sub-zero-left
 (:rewrite)
 nil
 f7-poly-reduced-sub-as-add-neg
 poly-reduced-sub-as-add-neg
 nil
 nil
 f7-canonical-polynomial-p-of-poly-reduced-add
 canonical-polynomial-p-of-poly-reduced-add
 (:rewrite)
 nil
 f7-canonical-polynomial-p-of-poly-reduced-neg
 canonical-polynomial-p-of-poly-reduced-neg
 (:rewrite)
 nil
 f7-canonical-polynomial-p-of-poly-reduced-sub
 canonical-polynomial-p-of-poly-reduced-sub
 (:rewrite)
 nil
 f7-canonical-polynomial-p-of-poly-reduced-mul
 canonical-polynomial-p-of-poly-reduced-mul
 (:rewrite)
 nil
 f7-canonical-polynomial-p-of-poly-reduced-one
 canonical-polynomial-p-of-poly-reduced-one
 (:rewrite)
 nil
 f7-normalize-of-poly-reduced-add
 normalize-of-poly-reduced-add
 (:rewrite)
 nil
 f7-normalize-of-poly-reduced-neg
 normalize-of-poly-reduced-neg
 (:rewrite)
 nil
 f7-normalize-of-poly-reduced-sub
 normalize-of-poly-reduced-sub
 (:rewrite)
 nil
 f7-normalize-of-poly-reduced-mul
 normalize-of-poly-reduced-mul
 (:rewrite)
 nil
 f7-normalize-of-poly-reduced-one
 normalize-of-poly-reduced-one
 (:rewrite)
 nil
 f7-poly-remainder-of-poly-reduced-add
 poly-remainder-of-poly-reduced-add
 (:rewrite)
 nil
 f7-poly-remainder-of-poly-reduced-neg
 poly-remainder-of-poly-reduced-neg
 (:rewrite)
 nil
 f7-poly-remainder-of-poly-reduced-sub
 poly-remainder-of-poly-reduced-sub
 (:rewrite)
 nil
 f7-poly-remainder-of-poly-reduced-mul
 poly-remainder-of-poly-reduced-mul
 (:rewrite)
 nil
 f7-poly-remainder-of-poly-reduced-one
 poly-remainder-of-poly-reduced-one
 (:rewrite)
 nil
 f7-poly-reduced-add-of-remainders
 poly-reduced-add-of-remainders
 nil
 nil
 f7-poly-reduced-neg-of-remainder
 poly-reduced-neg-of-remainder
 nil
 nil
 f7-poly-reduced-sub-of-remainders
 poly-reduced-sub-of-remainders
 nil
 nil
 f7-poly-reduced-mul-of-remainders
 poly-reduced-mul-of-remainders
 nil
 nil)

(local
 (defthm f7-poly-reduced-one-canonicality-regressions
   (and
    (f7-canonical-polynomial-p (f7-poly-reduced-one '(1 0 1)))
    (f7-canonical-polynomial-p (f7-poly-reduced-one nil))
    (f7-canonical-polynomial-p (f7-poly-reduced-one '(0)))
    (f7-canonical-polynomial-p (f7-poly-reduced-one '(1)))
    (f7-canonical-polynomial-p (f7-poly-reduced-one '(3)))
    (f7-canonical-polynomial-p (f7-poly-reduced-one 'bad))
    (f7-canonical-polynomial-p (f7-poly-reduced-one '(1 0 . bad))))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance f7-canonical-polynomial-p-of-poly-reduced-one
                 (modulus '(1 0 1)))
      (:instance f7-canonical-polynomial-p-of-poly-reduced-one (modulus nil))
      (:instance f7-canonical-polynomial-p-of-poly-reduced-one (modulus '(0)))
      (:instance f7-canonical-polynomial-p-of-poly-reduced-one (modulus '(1)))
      (:instance f7-canonical-polynomial-p-of-poly-reduced-one (modulus '(3)))
      (:instance f7-canonical-polynomial-p-of-poly-reduced-one (modulus 'bad))
      (:instance f7-canonical-polynomial-p-of-poly-reduced-one
                 (modulus '(1 0 . bad))))
     :in-theory
     (disable f7-poly-reduced-one f7-canonical-polynomial-p
              f7-polynomial-one f7-normalize f7-fix-coefficients
              f7-trim-trailing-zeros f7-poly-remainder f7-poly-divmod
              f7-poly-divmod-core f7-poly-division-step
              f7-poly-division-step-core f7-poly-division-step-term
              f7-poly-division-step-next gfield::f7-fix gfield::f7-add
              gfield::f7-neg gfield::f7-mul)))))

; Canonical output is the common structural boundary of all five reduced-ring
; operations.  These examples use only explicit instances of the
; generated rules while every arithmetic and reduction implementation stays
; closed.
(local
 (defthm f7-poly-reduced-canonicality-regressions
   (and
    ; Canonical zero, constant, and nonconstant operands at positive degree.
    (f7-canonical-polynomial-p
     (f7-poly-reduced-add nil '(3) '(1 0 1)))
    (f7-canonical-polynomial-p
     (f7-poly-reduced-add '(1 2) '(3 4) '(1 0 1)))
    ; Noncanonical, malformed, and coefficient-fixing inputs and moduli.
    (f7-canonical-polynomial-p
     (f7-poly-reduced-add '(8 -1 0 0) 'bad 'zero-modulus))
    (f7-canonical-polynomial-p
     (f7-poly-reduced-neg '(1 2 3 4) nil))
    (f7-canonical-polynomial-p
     (f7-poly-reduced-neg '(1 2 . bad) '(0 . bad)))
    (f7-canonical-polynomial-p
     (f7-poly-reduced-sub '(8 -1 0 0) '(1 2 . bad) '(1)))
    (f7-canonical-polynomial-p
     (f7-poly-reduced-sub 'bad '(3) '(3)))
    ; A genuine higher-degree product and total improper-modulus behavior.
    (f7-canonical-polynomial-p
     (f7-poly-reduced-mul '(1 1 1) '(1 1 1) '(1 0 1)))
    (f7-canonical-polynomial-p
     (f7-poly-reduced-mul '(8 -1 0) '(3) '(1 0 1 . bad))))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance f7-canonical-polynomial-p-of-poly-reduced-add
                 (left nil) (right '(3)) (modulus '(1 0 1)))
      (:instance f7-canonical-polynomial-p-of-poly-reduced-add
                 (left '(1 2)) (right '(3 4)) (modulus '(1 0 1)))
      (:instance f7-canonical-polynomial-p-of-poly-reduced-add
                 (left '(8 -1 0 0)) (right 'bad)
                 (modulus 'zero-modulus))
      (:instance f7-canonical-polynomial-p-of-poly-reduced-neg
                 (polynomial '(1 2 3 4)) (modulus nil))
      (:instance f7-canonical-polynomial-p-of-poly-reduced-neg
                 (polynomial '(1 2 . bad)) (modulus '(0 . bad)))
      (:instance f7-canonical-polynomial-p-of-poly-reduced-sub
                 (left '(8 -1 0 0)) (right '(1 2 . bad))
                 (modulus '(1)))
      (:instance f7-canonical-polynomial-p-of-poly-reduced-sub
                 (left 'bad) (right '(3)) (modulus '(3)))
      (:instance f7-canonical-polynomial-p-of-poly-reduced-mul
                 (left '(1 1 1)) (right '(1 1 1))
                 (modulus '(1 0 1)))
      (:instance f7-canonical-polynomial-p-of-poly-reduced-mul
                 (left '(8 -1 0)) (right '(3))
                 (modulus '(1 0 1 . bad))))
     :in-theory
     (disable f7-canonical-polynomial-p
              f7-poly-reduced-add f7-poly-reduced-neg
              f7-poly-reduced-sub f7-poly-reduced-mul
              f7-poly-add f7-poly-neg f7-poly-sub f7-poly-mul
              f7-raw-add f7-raw-neg f7-raw-scale f7-raw-mul
              f7-normalize f7-fix-coefficients f7-trim-trailing-zeros
              f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
              f7-poly-division-step f7-poly-division-step-core
              f7-poly-division-step-term f7-poly-division-step-next
              gfield::f7-fix gfield::f7-add gfield::f7-neg
              gfield::f7-mul)))))

(local
 (defthm f7-poly-reduced-normalization-regressions
   (and
    (equal (f7-normalize (f7-poly-reduced-add nil '(3) '(1 0 1)))
           (f7-poly-reduced-add nil '(3) '(1 0 1)))
    (equal (f7-normalize
            (f7-poly-reduced-add '(1 2) '(8 -1 0 0) 'bad-modulus))
           (f7-poly-reduced-add '(1 2) '(8 -1 0 0) 'bad-modulus))
    (equal (f7-normalize
            (f7-poly-reduced-neg '(1 2 3 4) nil))
           (f7-poly-reduced-neg '(1 2 3 4) nil))
    (equal (f7-normalize
            (f7-poly-reduced-neg '(1 2 . bad) '(0 . bad)))
           (f7-poly-reduced-neg '(1 2 . bad) '(0 . bad)))
    (equal (f7-normalize
            (f7-poly-reduced-sub '(8 -1 0 0) '(1 2 . bad) '(1)))
           (f7-poly-reduced-sub '(8 -1 0 0) '(1 2 . bad) '(1)))
    (equal (f7-normalize (f7-poly-reduced-sub 'bad '(3) '(3)))
           (f7-poly-reduced-sub 'bad '(3) '(3)))
    (equal (f7-normalize
            (f7-poly-reduced-mul '(1 1 1) '(1 1 1) '(1 0 1)))
           (f7-poly-reduced-mul '(1 1 1) '(1 1 1) '(1 0 1)))
    (equal (f7-normalize
            (f7-poly-reduced-mul '(8 -1 0) '(3) '(1 0 1 . bad)))
           (f7-poly-reduced-mul '(8 -1 0) '(3) '(1 0 1 . bad))))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance f7-normalize-of-poly-reduced-add
                 (left nil) (right '(3)) (modulus '(1 0 1)))
      (:instance f7-normalize-of-poly-reduced-add
                 (left '(1 2)) (right '(8 -1 0 0))
                 (modulus 'bad-modulus))
      (:instance f7-normalize-of-poly-reduced-neg
                 (polynomial '(1 2 3 4)) (modulus nil))
      (:instance f7-normalize-of-poly-reduced-neg
                 (polynomial '(1 2 . bad)) (modulus '(0 . bad)))
      (:instance f7-normalize-of-poly-reduced-sub
                 (left '(8 -1 0 0)) (right '(1 2 . bad)) (modulus '(1)))
      (:instance f7-normalize-of-poly-reduced-sub
                 (left 'bad) (right '(3)) (modulus '(3)))
      (:instance f7-normalize-of-poly-reduced-mul
                 (left '(1 1 1)) (right '(1 1 1)) (modulus '(1 0 1)))
      (:instance f7-normalize-of-poly-reduced-mul
                 (left '(8 -1 0)) (right '(3))
                 (modulus '(1 0 1 . bad))))
     :in-theory
     (disable f7-normalize f7-canonical-polynomial-p
              f7-poly-reduced-add f7-poly-reduced-neg
              f7-poly-reduced-sub f7-poly-reduced-mul
              f7-poly-add f7-poly-neg f7-poly-sub f7-poly-mul
              f7-raw-add f7-raw-neg f7-raw-scale f7-raw-mul
              f7-fix-coefficients f7-trim-trailing-zeros
              f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
              f7-poly-division-step f7-poly-division-step-core
              f7-poly-division-step-term f7-poly-division-step-next
              f7-polynomial-one gfield::f7-fix gfield::f7-add
              gfield::f7-neg gfield::f7-mul
              f7-normalize-of-poly-reduced-add
              f7-normalize-of-poly-reduced-neg
              f7-normalize-of-poly-reduced-sub
              f7-normalize-of-poly-reduced-mul)))))

(local
 (defthm f7-poly-reduced-one-normalization-regressions
   (and
    (equal (f7-normalize (f7-poly-reduced-one '(1 0 1)))
           (f7-poly-reduced-one '(1 0 1)))
    (equal (f7-normalize (f7-poly-reduced-one nil))
           (f7-poly-reduced-one nil))
    (equal (f7-normalize (f7-poly-reduced-one '(0)))
           (f7-poly-reduced-one '(0)))
    (equal (f7-normalize (f7-poly-reduced-one '(1)))
           (f7-poly-reduced-one '(1)))
    (equal (f7-normalize (f7-poly-reduced-one '(3)))
           (f7-poly-reduced-one '(3)))
    (equal (f7-normalize (f7-poly-reduced-one 'bad))
           (f7-poly-reduced-one 'bad))
    (equal (f7-normalize (f7-poly-reduced-one '(1 0 . bad)))
           (f7-poly-reduced-one '(1 0 . bad))))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance f7-normalize-of-poly-reduced-one (modulus '(1 0 1)))
      (:instance f7-normalize-of-poly-reduced-one (modulus nil))
      (:instance f7-normalize-of-poly-reduced-one (modulus '(0)))
      (:instance f7-normalize-of-poly-reduced-one (modulus '(1)))
      (:instance f7-normalize-of-poly-reduced-one (modulus '(3)))
      (:instance f7-normalize-of-poly-reduced-one (modulus 'bad))
      (:instance f7-normalize-of-poly-reduced-one
                 (modulus '(1 0 . bad))))
     :in-theory
     (disable f7-normalize f7-canonical-polynomial-p f7-poly-reduced-one
              f7-poly-add f7-poly-neg f7-poly-sub f7-poly-mul
              f7-raw-add f7-raw-neg f7-raw-scale f7-raw-mul
              f7-fix-coefficients f7-trim-trailing-zeros
              f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
              f7-poly-division-step f7-poly-division-step-core
              f7-poly-division-step-term f7-poly-division-step-next
              f7-polynomial-one gfield::f7-fix gfield::f7-add
              gfield::f7-neg gfield::f7-mul
              f7-normalize-of-poly-reduced-one)))))

; Remainder stability is exercised only through explicit instances of the five
; generated public rules.  The rules themselves and the full concrete
; implementation are disabled so these checks cannot fall back to rewriting or
; execution.
(local
 (defthm f7-poly-reduced-remainder-stability-regressions
   (and
    (equal
     (f7-poly-remainder
      (f7-poly-reduced-add nil '(3) '(1 0 1)) '(1 0 1))
     (f7-poly-reduced-add nil '(3) '(1 0 1)))
    (equal
     (f7-poly-remainder
      (f7-poly-reduced-add '(1 2 0 0) '(8 -1 . bad) 'bad-modulus)
      'bad-modulus)
     (f7-poly-reduced-add '(1 2 0 0) '(8 -1 . bad) 'bad-modulus))
    (equal
     (f7-poly-remainder
      (f7-poly-reduced-neg '(1 2 3 4) nil) nil)
     (f7-poly-reduced-neg '(1 2 3 4) nil))
    (equal
     (f7-poly-remainder
      (f7-poly-reduced-neg '(8 -1 0 . bad) '(0)) '(0))
     (f7-poly-reduced-neg '(8 -1 0 . bad) '(0)))
    (equal
     (f7-poly-remainder
      (f7-poly-reduced-sub '(1 2 3 4) '(3 0 0) '(1)) '(1))
     (f7-poly-reduced-sub '(1 2 3 4) '(3 0 0) '(1)))
    (equal
     (f7-poly-remainder
      (f7-poly-reduced-sub 'bad '(8 -1 . bad) '(3)) '(3))
     (f7-poly-reduced-sub 'bad '(8 -1 . bad) '(3)))
    ; Squaring a degree-two polynomial before reducing modulo degree two is a
    ; genuine multiplication-reduction case.
    (equal
     (f7-poly-remainder
      (f7-poly-reduced-mul '(1 1 1) '(1 1 1) '(1 0 1)) '(1 0 1))
     (f7-poly-reduced-mul '(1 1 1) '(1 1 1) '(1 0 1)))
    (equal
     (f7-poly-remainder
      (f7-poly-reduced-mul '(8 -1 0) '(3 . bad) '(1 0 1 . bad))
      '(1 0 1 . bad))
     (f7-poly-reduced-mul '(8 -1 0) '(3 . bad) '(1 0 1 . bad))))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance f7-poly-remainder-of-poly-reduced-add
                 (left nil) (right '(3)) (modulus '(1 0 1)))
      (:instance f7-poly-remainder-of-poly-reduced-add
                 (left '(1 2 0 0)) (right '(8 -1 . bad))
                 (modulus 'bad-modulus))
      (:instance f7-poly-remainder-of-poly-reduced-neg
                 (polynomial '(1 2 3 4)) (modulus nil))
      (:instance f7-poly-remainder-of-poly-reduced-neg
                 (polynomial '(8 -1 0 . bad)) (modulus '(0)))
      (:instance f7-poly-remainder-of-poly-reduced-sub
                 (left '(1 2 3 4)) (right '(3 0 0)) (modulus '(1)))
      (:instance f7-poly-remainder-of-poly-reduced-sub
                 (left 'bad) (right '(8 -1 . bad)) (modulus '(3)))
      (:instance f7-poly-remainder-of-poly-reduced-mul
                 (left '(1 1 1)) (right '(1 1 1)) (modulus '(1 0 1)))
      (:instance f7-poly-remainder-of-poly-reduced-mul
                 (left '(8 -1 0)) (right '(3 . bad))
                 (modulus '(1 0 1 . bad))))
     :in-theory
     (disable f7-poly-remainder-of-poly-reduced-add
              f7-poly-remainder-of-poly-reduced-neg
              f7-poly-remainder-of-poly-reduced-sub
              f7-poly-remainder-of-poly-reduced-mul
              f7-poly-remainder-of-poly-reduced-one
              f7-canonical-polynomial-p-of-poly-reduced-add
              f7-canonical-polynomial-p-of-poly-reduced-neg
              f7-canonical-polynomial-p-of-poly-reduced-sub
              f7-canonical-polynomial-p-of-poly-reduced-mul
              f7-normalize-of-poly-reduced-add
              f7-normalize-of-poly-reduced-neg
              f7-normalize-of-poly-reduced-sub
              f7-normalize-of-poly-reduced-mul
              f7-poly-reduced-add f7-poly-reduced-neg
              f7-poly-reduced-sub f7-poly-reduced-mul
              f7-poly-add f7-poly-neg f7-poly-sub f7-poly-mul
              f7-raw-add f7-raw-neg f7-raw-scale f7-raw-mul
              f7-normalize f7-canonical-polynomial-p
              f7-fix-coefficients f7-trim-trailing-zeros
              f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
              f7-poly-division-step f7-poly-division-step-core
              f7-poly-division-step-term f7-poly-division-step-next
              f7-polynomial-one gfield::f7-fix gfield::f7-add
              gfield::f7-neg gfield::f7-mul)))))

(local
 (defthm f7-poly-reduced-one-remainder-stability-regressions
   (and
    (equal (f7-poly-remainder (f7-poly-reduced-one '(1 0 1)) '(1 0 1))
           (f7-poly-reduced-one '(1 0 1)))
    (equal (f7-poly-remainder (f7-poly-reduced-one nil) nil)
           (f7-poly-reduced-one nil))
    (equal (f7-poly-remainder (f7-poly-reduced-one '(0)) '(0))
           (f7-poly-reduced-one '(0)))
    (equal (f7-poly-remainder (f7-poly-reduced-one '(1)) '(1))
           (f7-poly-reduced-one '(1)))
    (equal (f7-poly-remainder (f7-poly-reduced-one '(3)) '(3))
           (f7-poly-reduced-one '(3)))
    (equal (f7-poly-remainder (f7-poly-reduced-one 'bad) 'bad)
           (f7-poly-reduced-one 'bad))
    (equal
     (f7-poly-remainder
      (f7-poly-reduced-one '(1 0 . bad)) '(1 0 . bad))
     (f7-poly-reduced-one '(1 0 . bad))))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance f7-poly-remainder-of-poly-reduced-one
                 (modulus '(1 0 1)))
      (:instance f7-poly-remainder-of-poly-reduced-one (modulus nil))
      (:instance f7-poly-remainder-of-poly-reduced-one (modulus '(0)))
      (:instance f7-poly-remainder-of-poly-reduced-one (modulus '(1)))
      (:instance f7-poly-remainder-of-poly-reduced-one (modulus '(3)))
      (:instance f7-poly-remainder-of-poly-reduced-one (modulus 'bad))
      (:instance f7-poly-remainder-of-poly-reduced-one
                 (modulus '(1 0 . bad))))
     :in-theory
     (disable f7-poly-remainder-of-poly-reduced-add
              f7-poly-remainder-of-poly-reduced-neg
              f7-poly-remainder-of-poly-reduced-sub
              f7-poly-remainder-of-poly-reduced-mul
              f7-poly-remainder-of-poly-reduced-one
              f7-canonical-polynomial-p-of-poly-reduced-one
              f7-normalize-of-poly-reduced-one
              f7-poly-reduced-add f7-poly-reduced-neg
              f7-poly-reduced-sub f7-poly-reduced-mul
              f7-poly-reduced-one
              f7-poly-add f7-poly-neg f7-poly-sub f7-poly-mul
              f7-raw-add f7-raw-neg f7-raw-scale f7-raw-mul
              f7-normalize f7-canonical-polynomial-p
              f7-fix-coefficients f7-trim-trailing-zeros
              f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
              f7-poly-division-step f7-poly-division-step-core
              f7-poly-division-step-term f7-poly-division-step-next
              f7-polynomial-one gfield::f7-fix gfield::f7-add
              gfield::f7-neg gfield::f7-mul)))))

(local
 (defthm f7-poly-reduced-representative-independence-regressions
   (and
    (equal
     (f7-poly-reduced-add
      (f7-poly-remainder nil '(1 0 1))
      (f7-poly-remainder '(8 -1 0 0) '(1 0 1)) '(1 0 1))
     (f7-poly-reduced-add nil '(8 -1 0 0) '(1 0 1)))
    (equal
     (f7-poly-reduced-add
      (f7-poly-remainder 'bad 'bad-modulus)
      (f7-poly-remainder '(3 . tail) 'bad-modulus) 'bad-modulus)
     (f7-poly-reduced-add 'bad '(3 . tail) 'bad-modulus))
    (equal
     (f7-poly-reduced-neg
      (f7-poly-remainder '(8 -1 0 . tail) nil) nil)
     (f7-poly-reduced-neg '(8 -1 0 . tail) nil))
    (equal
     (f7-poly-reduced-neg
      (f7-poly-remainder 'bad '(0)) '(0))
     (f7-poly-reduced-neg 'bad '(0)))
    (equal
     (f7-poly-reduced-sub
      (f7-poly-remainder '(1 2 0 0) '(3))
      (f7-poly-remainder '(8 -1 . tail) '(3)) '(3))
     (f7-poly-reduced-sub '(1 2 0 0) '(8 -1 . tail) '(3)))
    (equal
     (f7-poly-reduced-sub
      (f7-poly-remainder 'left '(1 0 1 . tail))
      (f7-poly-remainder '(3 4 5) '(1 0 1 . tail))
      '(1 0 1 . tail))
     (f7-poly-reduced-sub 'left '(3 4 5) '(1 0 1 . tail)))
    ; Both degree-two operands require genuine reduction modulo degree two.
    (equal
     (f7-poly-reduced-mul
      (f7-poly-remainder '(1 1 1) '(1 0 1))
      (f7-poly-remainder '(1 2 1) '(1 0 1)) '(1 0 1))
     (f7-poly-reduced-mul '(1 1 1) '(1 2 1) '(1 0 1)))
    (equal
     (f7-poly-reduced-mul
      (f7-poly-remainder '(8 -1 0) 'atomic-modulus)
      (f7-poly-remainder '(3 . tail) 'atomic-modulus) 'atomic-modulus)
     (f7-poly-reduced-mul '(8 -1 0) '(3 . tail) 'atomic-modulus)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance f7-poly-reduced-add-of-remainders
                 (left nil) (right '(8 -1 0 0)) (modulus '(1 0 1)))
      (:instance f7-poly-reduced-add-of-remainders
                 (left 'bad) (right '(3 . tail)) (modulus 'bad-modulus))
      (:instance f7-poly-reduced-neg-of-remainder
                 (polynomial '(8 -1 0 . tail)) (modulus nil))
      (:instance f7-poly-reduced-neg-of-remainder
                 (polynomial 'bad) (modulus '(0)))
      (:instance f7-poly-reduced-sub-of-remainders
                 (left '(1 2 0 0)) (right '(8 -1 . tail)) (modulus '(3)))
      (:instance f7-poly-reduced-sub-of-remainders
                 (left 'left) (right '(3 4 5))
                 (modulus '(1 0 1 . tail)))
      (:instance f7-poly-reduced-mul-of-remainders
                 (left '(1 1 1)) (right '(1 2 1)) (modulus '(1 0 1)))
      (:instance f7-poly-reduced-mul-of-remainders
                 (left '(8 -1 0)) (right '(3 . tail))
                 (modulus 'atomic-modulus)))
     :in-theory
     (disable f7-poly-remainder-of-poly-reduced-add
              f7-poly-remainder-of-poly-reduced-neg
              f7-poly-remainder-of-poly-reduced-sub
              f7-poly-remainder-of-poly-reduced-mul
              f7-poly-reduced-add f7-poly-reduced-neg
              f7-poly-reduced-sub f7-poly-reduced-mul
              f7-poly-add f7-poly-neg f7-poly-sub f7-poly-mul
              f7-raw-add f7-raw-neg f7-raw-scale f7-raw-mul
              f7-normalize f7-canonical-polynomial-p
              f7-fix-coefficients f7-trim-trailing-zeros
              f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
              f7-poly-division-step f7-poly-division-step-core
              f7-poly-division-step-term f7-poly-division-step-next
              gfield::f7-fix gfield::f7-add gfield::f7-neg
              gfield::f7-mul)))))

(local
 (defthm f7-poly-reduced-sub-identity-regressions
   (and
    ; Self-subtraction covers zero, a genuine higher-degree polynomial, and
    ; equal malformed operands.
    (equal (f7-poly-reduced-sub nil nil '(1 0 1)) nil)
    (equal (f7-poly-reduced-sub '(1 2 3 4) '(1 2 3 4) '(1 0 1)) nil)
    (equal (f7-poly-reduced-sub '(1 2 . bad) '(1 2 . bad) 'bad-modulus) nil)
    ; Subtraction of zero returns the exact remainder representative, not the
    ; arbitrary raw operand.  These cases exercise fixing, trailing zeros,
    ; atoms, improper lists, and total modulus behavior.
    (equal (f7-poly-reduced-sub '(8 -1 0 0) nil '(1 0 1))
           (f7-poly-remainder '(8 -1 0 0) '(1 0 1)))
    (equal (f7-poly-reduced-sub '(1 6) nil '(1 0 1))
           (f7-poly-remainder '(1 6) '(1 0 1)))
    (equal (f7-poly-reduced-sub 'malformed nil nil)
           (f7-poly-remainder 'malformed nil))
    (equal (f7-poly-reduced-sub '(1 2 . bad) nil '(1))
           (f7-poly-remainder '(1 2 . bad) '(1)))
    (equal (f7-poly-reduced-sub '(8 9) nil '(3))
           (f7-poly-remainder '(8 9) '(3)))
    ; The preceding first two right-zero cases are unequal raw representatives
    ; with the same remainder.  Zero-left contracts to reduced negation for
    ; canonical and noncanonical presentations, including a malformed modulus.
    (equal (f7-poly-reduced-sub nil '(3 4) '(1 0 1))
           (f7-poly-reduced-neg '(3 4) '(1 0 1)))
    (equal (f7-poly-reduced-sub nil '(8 -1 0 0) 'bad-modulus)
           (f7-poly-reduced-neg '(8 -1 0 0) 'bad-modulus)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance f7-poly-reduced-sub-self
                      (a nil) (modulus '(1 0 1)))
           (:instance f7-poly-reduced-sub-self
                      (a '(1 2 3 4)) (modulus '(1 0 1)))
           (:instance f7-poly-reduced-sub-self
                      (a '(1 2 . bad)) (modulus 'bad-modulus))
           (:instance f7-poly-reduced-sub-zero-right
                      (a '(8 -1 0 0)) (modulus '(1 0 1)))
           (:instance f7-poly-reduced-sub-zero-right
                      (a '(1 6)) (modulus '(1 0 1)))
           (:instance f7-poly-reduced-sub-zero-right
                      (a 'malformed) (modulus nil))
           (:instance f7-poly-reduced-sub-zero-right
                      (a '(1 2 . bad)) (modulus '(1)))
           (:instance f7-poly-reduced-sub-zero-right
                      (a '(8 9)) (modulus '(3)))
           (:instance f7-poly-reduced-sub-zero-left
                      (a '(3 4)) (modulus '(1 0 1)))
           (:instance f7-poly-reduced-sub-zero-left
                      (a '(8 -1 0 0)) (modulus 'bad-modulus)))
     :in-theory
     (disable f7-poly-reduced-sub f7-poly-sub f7-poly-add f7-raw-add
              f7-poly-neg f7-raw-neg f7-poly-reduced-neg
              f7-normalize f7-fix-coefficients f7-trim-trailing-zeros
              f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
              f7-poly-division-step f7-poly-division-step-core
              gfield::f7-add gfield::f7-neg gfield::f7-fix)))))

; This semantic bridge is deliberately absent from the rewrite theory.  These
; examples use an explicit instance while every arithmetic implementation body
; stays closed, so general reduced-subtraction terms retain their public form.
(local
 (defthm f7-poly-reduced-sub-as-add-neg-regressions
   (and
    (equal (f7-poly-reduced-sub '(1 2) '(3 4) '(1 0 1))
           (f7-poly-reduced-add
            '(1 2) (f7-poly-reduced-neg '(3 4) '(1 0 1)) '(1 0 1)))
    (equal (f7-poly-reduced-sub nil '(3 4) '(1 0 1))
           (f7-poly-reduced-add
            nil (f7-poly-reduced-neg '(3 4) '(1 0 1)) '(1 0 1)))
    (equal (f7-poly-reduced-sub '(1 2 3 4) nil '(1 0 0 1))
           (f7-poly-reduced-add
            '(1 2 3 4) (f7-poly-reduced-neg nil '(1 0 0 1)) '(1 0 0 1)))
    (equal (f7-poly-reduced-sub '(8 -1 0 0) '(1 2 . bad) '(1 0 1))
           (f7-poly-reduced-add
            '(8 -1 0 0)
            (f7-poly-reduced-neg '(1 2 . bad) '(1 0 1)) '(1 0 1)))
    (equal (f7-poly-reduced-sub 'bad '(8 -1 . tail) 'bad-modulus)
           (f7-poly-reduced-add
            'bad (f7-poly-reduced-neg '(8 -1 . tail) 'bad-modulus)
            'bad-modulus))
    (equal (f7-poly-reduced-sub '(8 -1 0 0) '(3) '(1 0 1))
           (f7-poly-reduced-add
            '(1 6) (f7-poly-reduced-neg '(3) '(1 0 1)) '(1 0 1))))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance f7-poly-reduced-sub-as-add-neg
                      (a '(1 2)) (b '(3 4)) (modulus '(1 0 1)))
           (:instance f7-poly-reduced-sub-as-add-neg
                      (a nil) (b '(3 4)) (modulus '(1 0 1)))
           (:instance f7-poly-reduced-sub-as-add-neg
                      (a '(1 2 3 4)) (b nil) (modulus '(1 0 0 1)))
           (:instance f7-poly-reduced-sub-as-add-neg
                      (a '(8 -1 0 0)) (b '(1 2 . bad))
                      (modulus '(1 0 1)))
           (:instance f7-poly-reduced-sub-as-add-neg
                      (a 'bad) (b '(8 -1 . tail))
                      (modulus 'bad-modulus))
           (:instance f7-poly-reduced-sub-as-add-neg
                      (a '(8 -1 0 0)) (b '(3)) (modulus '(1 0 1))))
     :in-theory
     (disable f7-poly-reduced-sub f7-poly-reduced-add f7-poly-reduced-neg
              f7-poly-sub f7-poly-add f7-raw-add f7-poly-neg f7-raw-neg
              f7-normalize f7-fix-coefficients f7-trim-trailing-zeros
              f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
              f7-poly-division-step f7-poly-division-step-core
              gfield::f7-add gfield::f7-neg gfield::f7-fix)))))

(local
 (defthm f7-poly-reduced-add-zero-law-regressions
   (and
    ; Canonical zero and nonzero representatives.
    (equal (f7-poly-reduced-add nil nil '(1 0 1))
           (f7-poly-remainder nil '(1 0 1)))
    (equal (f7-poly-reduced-add '(3 4) nil '(1 0 1))
           (f7-poly-remainder '(3 4) '(1 0 1)))
    ; Malformed and noncanonical operands, including values requiring fixing.
    (equal (f7-poly-reduced-add nil 'malformed '(1 0 1))
           (f7-poly-remainder 'malformed '(1 0 1)))
    (equal (f7-poly-reduced-add '(8 -1 0 0) nil '(1 0 1))
           (f7-poly-remainder '(8 -1 0 0) '(1 0 1)))
    ; Malformed, zero, and nonzero constant moduli.
    (equal (f7-poly-reduced-add nil '(8 -1 . tail) 'bad-modulus)
           (f7-poly-remainder '(8 -1 . tail) 'bad-modulus))
    (equal (f7-poly-reduced-add '(8 -1 . tail) nil nil)
           (f7-poly-remainder '(8 -1 . tail) nil))
    (equal (f7-poly-reduced-add nil '(8 -1 . tail) '(3))
           (f7-poly-remainder '(8 -1 . tail) '(3)))
    ; Unequal raw representatives with the same established remainder.
    (equal (f7-poly-reduced-add nil '(8 -1 0 0) '(1 0 1))
           (f7-poly-reduced-add '(1 6) nil '(1 0 1))))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance f7-poly-reduced-add-zero-left
                      (first '(8 -1 0 0)) (modulus '(1 0 1)))
           (:instance f7-poly-reduced-add-zero-right
                      (first '(1 6)) (modulus '(1 0 1))))
     :in-theory
     (disable f7-poly-reduced-add f7-poly-add f7-raw-add
              f7-normalize f7-fix-coefficients f7-trim-trailing-zeros
              f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
              f7-poly-division-step f7-poly-division-step-core
              gfield::f7-fix gfield::f7-add)))))

(local
 (defthm f7-poly-reduced-add-structural-law-regressions
   (and
    ; Canonical representatives.
    (equal (f7-poly-reduced-add '(1 2) '(3 4) '(1 0 1))
           (f7-poly-reduced-add '(3 4) '(1 2) '(1 0 1)))
    (equal (f7-poly-reduced-add
            (f7-poly-reduced-add '(1 2) '(3 4) '(1 0 1)) '(5 6) '(1 0 1))
           (f7-poly-reduced-add
            '(1 2) (f7-poly-reduced-add '(3 4) '(5 6) '(1 0 1)) '(1 0 1)))
    ; Malformed operands and modulus, and a degenerate constant modulus.
    (equal (f7-poly-reduced-add 'bad '(8 -3 . tail) 'bad-modulus)
           (f7-poly-reduced-add '(8 -3 . tail) 'bad 'bad-modulus))
    (equal (f7-poly-reduced-add
            (f7-poly-reduced-add '(1 . bad) '(8 -3 0) '(3)) 'bad '(3))
           (f7-poly-reduced-add
            '(1 . bad) (f7-poly-reduced-add '(8 -3 0) 'bad '(3)) '(3)))
    ; Unequal raw representatives with equal remainders.
    (equal (f7-poly-reduced-add '(8 -1 0 0) '(3) '(1 0 1))
           (f7-poly-reduced-add '(3) '(1 6) '(1 0 1)))
    (equal (f7-poly-reduced-add
            (f7-poly-reduced-add '(8 -1 0 0) '(3) '(1 0 1)) '(2) '(1 0 1))
           (f7-poly-reduced-add
            '(1 6) (f7-poly-reduced-add '(3) '(2) '(1 0 1)) '(1 0 1))))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance f7-poly-reduced-add-commutative
                      (a '(8 -1 0 0)) (b '(3)) (modulus '(1 0 1)))
           (:instance f7-poly-reduced-add-associative
                      (a '(1 6)) (b '(3)) (c '(2))
                      (modulus '(1 0 1))))
     :in-theory
     (disable f7-poly-reduced-add f7-poly-add f7-raw-add
              f7-normalize f7-fix-coefficients f7-trim-trailing-zeros
              f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
              f7-poly-division-step f7-poly-division-step-core
              gfield::f7-fix gfield::f7-add)))))

(local
 (defthm f7-poly-reduced-add-inverse-law-regressions
   (and
    ; Canonical zero and nonzero values, including genuine polynomials.
    (equal (f7-poly-reduced-add
            (f7-poly-reduced-neg nil '(1 0 1)) nil '(1 0 1)) nil)
    (equal (f7-poly-reduced-add
            '(3 4) (f7-poly-reduced-neg '(3 4) '(1 0 1)) '(1 0 1)) nil)
    (equal (f7-poly-reduced-add
            (f7-poly-reduced-neg '(1 2 3) '(1 0 0 1))
            '(1 2 3) '(1 0 0 1)) nil)
    ; Malformed, noncanonical, and coefficient-fixing operands.
    (equal (f7-poly-reduced-add
            'malformed (f7-poly-reduced-neg 'malformed '(1 0 1)) '(1 0 1)) nil)
    (equal (f7-poly-reduced-add
            (f7-poly-reduced-neg '(8 -1 0 0) '(1 0 1))
            '(8 -1 0 0) '(1 0 1)) nil)
    ; Malformed, zero, and constant moduli exercise both orientations.
    (equal (f7-poly-reduced-add
            (f7-poly-reduced-neg '(8 -1 . tail) 'bad-modulus)
            '(8 -1 . tail) 'bad-modulus) nil)
    (equal (f7-poly-reduced-add
            '(8 -1 . tail) (f7-poly-reduced-neg '(8 -1 . tail) nil) nil) nil)
    (equal (f7-poly-reduced-add
            (f7-poly-reduced-neg '(1 2) '(3)) '(1 2) '(3)) nil)
    ; Unequal raw representatives with the same established remainder.
    (equal (f7-poly-reduced-add
            (f7-poly-reduced-neg '(8 -1 0 0) '(1 0 1))
            '(8 -1 0 0) '(1 0 1))
           (f7-poly-reduced-add
            '(1 6) (f7-poly-reduced-neg '(1 6) '(1 0 1)) '(1 0 1))))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance f7-poly-reduced-add-inverse-left
                      (a '(8 -1 0 0)) (modulus '(1 0 1)))
           (:instance f7-poly-reduced-add-inverse-right
                      (a '(1 6)) (modulus '(1 0 1))))
     :in-theory
     (disable f7-poly-reduced-add f7-poly-reduced-neg
              f7-poly-add f7-poly-neg f7-raw-add f7-raw-neg
              f7-normalize f7-fix-coefficients f7-trim-trailing-zeros
              f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
              f7-poly-division-step f7-poly-division-step-core
              gfield::f7-fix gfield::f7-add gfield::f7-neg)))))

(local
 (defthm f7-poly-reduced-neg-law-regressions
   (and
    ; Zero, canonical nonzero values, and a genuine polynomial.
    (equal (f7-poly-reduced-neg nil '(1 0 1)) nil)
    (equal (f7-poly-reduced-neg
            (f7-poly-reduced-neg '(3 4) '(1 0 1)) '(1 0 1))
           (f7-poly-remainder '(3 4) '(1 0 1)))
    (equal (f7-poly-reduced-neg
            (f7-poly-reduced-neg '(1 2 3) '(1 0 0 1)) '(1 0 0 1))
           (f7-poly-remainder '(1 2 3) '(1 0 0 1)))
    ; Malformed, noncanonical, and coefficient-fixing operands.
    (equal (f7-poly-reduced-neg
            (f7-poly-reduced-neg 'malformed '(1 0 1)) '(1 0 1))
           (f7-poly-remainder 'malformed '(1 0 1)))
    (equal (f7-poly-reduced-neg
            (f7-poly-reduced-neg '(8 -1 0 0) '(1 0 1)) '(1 0 1))
           (f7-poly-remainder '(8 -1 0 0) '(1 0 1)))
    ; Malformed, zero, and constant moduli.
    (equal (f7-poly-reduced-neg nil 'bad-modulus) nil)
    (equal (f7-poly-reduced-neg
            (f7-poly-reduced-neg '(8 -1 . tail) nil) nil)
           (f7-poly-remainder '(8 -1 . tail) nil))
    (equal (f7-poly-reduced-neg
            (f7-poly-reduced-neg '(1 2) '(3)) '(3))
           (f7-poly-remainder '(1 2) '(3)))
    ; Unequal raw representatives with the same established remainder.
    (equal (f7-poly-reduced-neg
            (f7-poly-reduced-neg '(8 -1 0 0) '(1 0 1)) '(1 0 1))
           (f7-poly-remainder '(1 6) '(1 0 1))))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance f7-poly-reduced-neg-double
                      (a '(8 -1 0 0)) (modulus '(1 0 1)))
           (:instance f7-poly-reduced-neg-zero
                      (modulus 'bad-modulus)))
     :in-theory
     (disable f7-poly-reduced-neg f7-poly-neg f7-raw-neg
              f7-poly-add f7-raw-add
              f7-normalize f7-fix-coefficients f7-trim-trailing-zeros
              f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
              f7-poly-division-step f7-poly-division-step-core
              gfield::f7-fix gfield::f7-neg gfield::f7-add)))))

; Concrete execution spelling of the generic quotient-equality boundary.
(defun f7-poly-congruent-p (left right modulus)
  (equal (f7-poly-remainder left modulus)
         (f7-poly-remainder right modulus)))

(verify-guards f7-poly-congruent-p)

(defthm f7-poly-congruent-p-exact-regressions
  (and
   ; Different representations, the same exact representative.
   (equal (f7-poly-remainder '(8 -1 0 0) '(1 0 1)) '(1 6))
   (equal (f7-poly-remainder '(1 6) '(1 0 1)) '(1 6))
   (f7-poly-congruent-p '(8 -1 0 0) '(1 6) '(1 0 1))
   (not (equal '(8 -1 0 0) '(1 6)))
   ; Distinct already-reduced representatives do not compare equal.
   (not (f7-poly-congruent-p '(1 2) '(2 2) '(1 0 1)))
   (equal (f7-poly-remainder '(1 2) '(1 0 1)) '(1 2))
   (equal (f7-poly-remainder '(2 2) '(1 0 1)) '(2 2))
   ; Adding one modulus multiple, trailing zeros, malformed total inputs.
   (f7-poly-congruent-p '(2 2 1) '(1 2) '(1 0 1))
   (f7-poly-congruent-p '(1 2 0 0) '(1 2) '(1 0 1))
   (f7-poly-congruent-p 'malformed nil '(1 0 1))
   (f7-poly-congruent-p '(1 2 . 9) '(1 2) '(1 0 1))
   ; Exact total modulus semantics.
   (f7-poly-congruent-p '(8 -1 0) '(1 6) nil)
   (not (f7-poly-congruent-p '(1) '(2) nil))
   (f7-poly-congruent-p '(1 2) '(6 5) '(1))
   (f7-poly-congruent-p '(1 2) '(6 5) '(3))
   ; Reducible x^2-1 and irreducible-looking x^2+1 examples.
   (f7-poly-congruent-p '(0 0 1) '(1) '(6 0 1))
   (f7-poly-congruent-p '(0 0 1) '(6) '(1 0 1))
   ; Compatibility is checked at exact representative values.
   (equal (f7-poly-reduced-add '(8 -1 0 0) '(3) '(1 0 1))
          (f7-poly-reduced-add '(1 6) '(3) '(1 0 1)))
   (equal (f7-poly-reduced-neg '(8 -1 0 0) '(1 0 1))
          (f7-poly-reduced-neg '(1 6) '(1 0 1)))
   (equal (f7-poly-reduced-sub '(8 -1 0 0) '(3) '(1 0 1))
          (f7-poly-reduced-sub '(1 6) '(3) '(1 0 1)))
   (equal (f7-poly-reduced-mul '(8 -1 0 0) '(3) '(1 0 1))
          (f7-poly-reduced-mul '(1 6) '(3) '(1 0 1)))
   ; For fixed representatives, congruence is literal equality.
   (equal (f7-poly-congruent-p '(1 2) '(1 2) '(1 0 1))
          (equal '(1 2) '(1 2)))
   (equal (f7-poly-congruent-p '(1 2) '(2 2) '(1 0 1))
          (equal '(1 2) '(2 2))))
  :rule-classes nil)

; x^2+1 is used only as an irreducible-looking execution example.  No
; irreducibility or field conclusion is asserted.
(defthm f7-poly-reduced-arithmetic-exact-regressions
  (and
   ; Addition requiring reduction, addition below the bound, and cancellation.
   (equal (f7-poly-add '(0 0 1) '(3)) '(3 0 1))
   (equal (f7-poly-reduced-add '(0 0 1) '(3) '(1 0 1)) '(2))
   (equal (f7-poly-reduced-add '(1 2) '(3) '(1 0 1)) '(4 2))
   (equal (f7-poly-reduced-add '(1 2) '(6 5) '(1 0 1)) nil)
   ; Negation and subtraction retain their public arithmetic boundaries.
   (equal (f7-poly-reduced-neg '(1 2) '(1 0 1)) '(6 5))
   (equal (f7-poly-reduced-sub '(1 2) '(3 4) '(1 0 1)) '(5 5))
   ; A degree-four product substantially reduces; zero and one are explicit.
   (equal (f7-poly-mul '(1 1 1) '(1 1 1)) '(1 2 3 2 1))
   (equal (f7-poly-reduced-mul '(1 1 1) '(1 1 1) '(1 0 1)) '(6))
   (equal (f7-poly-reduced-mul '(1 2) nil '(1 0 1)) nil)
   (equal (f7-poly-reduced-mul '(3 4 5) '(1) '(1 0 1)) '(5 4))
   ; Total modulus semantics.
   (equal (f7-poly-reduced-add '(8 -1 0) '(3) nil) '(4 6))
   (equal (f7-poly-reduced-sub '(1 2) '(3 4) '(1)) nil)
   (equal (f7-poly-reduced-mul '(1 2) '(3 4) '(3)) nil)
   ; Trailing zeros, out-of-range coefficients, atoms, and dotted lists.
   (equal (f7-poly-reduced-add '(8 -1 0 0) '(3) '(1 0 1 0)) '(4 6))
   (equal (f7-poly-reduced-neg 'malformed '(1 0 1)) nil)
   (equal (f7-poly-reduced-add '(1 2) '(3) 'malformed-modulus) '(4 2))
   (equal (f7-poly-reduced-sub '(1 2 . 9) '(3 . 8) '(1 0 1)) '(5 2))
   (equal (f7-poly-reduced-add '(0 0 1) '(3) '(1 0 1 . 9)) '(2))
   ; A small reducible-modulus execution example, with no field claim.
   (equal (f7-poly-reduced-mul '(1 1) '(1 1) '(6 0 1)) '(2 2))))

(defthm f7-poly-reduced-arithmetic-boundary-regressions
  (let* ((modulus '(1 0 1))
         (result (f7-poly-reduced-mul '(1 1 1) '(1 1 1) modulus)))
    (and (f7-canonical-polynomial-p result)
         (equal (f7-normalize result) result)
         (equal (f7-poly-remainder result modulus) result)
         (or (equal result nil)
             (< (f7-poly-degree result)
                (f7-poly-degree (f7-normalize modulus))))
         (equal (f7-poly-reduced-add '(8 -1 0 0) '(3) '(1 0 1 0))
                (f7-poly-reduced-add
                 (f7-normalize '(8 -1 0 0))
                 (f7-normalize '(3))
                 (f7-normalize '(1 0 1 0)))))))

(defthm f7-poly-reduced-ring-law-regressions
  (let* ((m '(1 0 1))
         (a '(0 0 1))
         (b '(3 4 5))
         (c '(8 -1 0 0))
         (ra (f7-poly-remainder a m))
         (rb (f7-poly-remainder b m))
         (rc (f7-poly-remainder c m))
         (one (f7-poly-reduced-one m))
         (add-left (f7-poly-reduced-add
                    (f7-poly-reduced-add a b m) c m))
         (add-right (f7-poly-reduced-add
                     a (f7-poly-reduced-add b c m) m))
         (mul-left (f7-poly-reduced-mul
                    (f7-poly-reduced-mul a b m) c m))
         (mul-right (f7-poly-reduced-mul
                     a (f7-poly-reduced-mul b c m) m)))
    (and
     (equal ra '(6)) (equal rb '(5 4)) (equal rc '(1 6))
     (equal one '(1))
     (equal add-left '(5 3)) (equal add-right '(5 3))
     (equal (f7-poly-reduced-add 'malformed nil m) nil)
     (equal (f7-poly-reduced-add a (f7-poly-reduced-neg a m) m) nil)
     (equal (f7-poly-reduced-neg (f7-poly-reduced-neg c m) m) rc)
     (equal (f7-poly-reduced-sub b c m)
            (f7-poly-reduced-add b (f7-poly-reduced-neg c m) m))
     (equal mul-left '(5 1)) (equal mul-right '(5 1))
     (equal (f7-poly-reduced-mul b one m) rb)
     (equal (f7-poly-reduced-mul nil '(1 2 . 9) m) nil)
     (equal (f7-poly-reduced-mul a (f7-poly-reduced-add b c m) m)
            (f7-poly-reduced-add (f7-poly-reduced-mul a b m)
                                 (f7-poly-reduced-mul a c m) m))
     (equal (f7-poly-reduced-mul (f7-poly-reduced-add a b m) c m)
            (f7-poly-reduced-add (f7-poly-reduced-mul a c m)
                                 (f7-poly-reduced-mul b c m) m))
     (equal (f7-poly-reduced-one nil) '(1))
     (equal (f7-poly-reduced-one '(1)) nil)
     (equal (f7-poly-reduced-one '(3)) nil)
     (equal (f7-poly-reduced-one '(6 0 1)) '(1))
     (equal (f7-poly-reduced-mul '(1 1) '(1 1) '(6 0 1)) '(2 2))
     (f7-canonical-polynomial-p mul-left)
     (equal (f7-normalize mul-left) mul-left)
     (equal (f7-poly-remainder mul-left m) mul-left)))
  :rule-classes nil)

; Focused unit-law executions.  These record the complete canonical data for
; a unit modulo a reducible polynomial, an irreducible-looking execution-only
; modulus, total constant moduli, and normalized malformed representations.
(assert-event
 (let* ((first '(0 1))
        (modulus '(6 0 1))       ; x^2 - 1, deliberately reducible
        (inverse (f7-poly-modular-inverse first modulus))
        (one (f7-poly-reduced-one modulus))
        (left (f7-poly-reduced-mul inverse first modulus))
        (right (f7-poly-reduced-mul first inverse modulus)))
   (and (equal (f7-normalize first) '(0 1))
        (equal (f7-normalize modulus) '(6 0 1))
        (equal (f7-poly-monic-euclidean-gcd first modulus) '(1))
        (equal inverse '(0 1))
        (equal one '(1))
        (equal left '(1)) (equal right '(1))
        (equal left one) (equal right one)
        (f7-canonical-polynomial-p inverse)
        (equal (f7-normalize inverse) inverse)
        (equal (f7-poly-remainder inverse modulus) inverse))))

(assert-event
 (let* ((first '(1 0 0 0 1))
        (modulus '(1 1 1))       ; no irreducibility claim
        (inverse (f7-poly-modular-inverse first modulus))
        (one (f7-poly-reduced-one modulus))
        (left (f7-poly-reduced-mul inverse first modulus))
        (right (f7-poly-reduced-mul first inverse modulus)))
   (and (equal (f7-normalize first) '(1 0 0 0 1))
        (equal (f7-normalize modulus) '(1 1 1))
        (equal (f7-poly-monic-euclidean-gcd first modulus) '(1))
        (equal inverse '(0 6))
        (equal one '(1))
        (equal left '(1)) (equal right '(1))
        (equal left one) (equal right one)
        (f7-canonical-polynomial-p inverse)
        (equal (f7-normalize inverse) inverse)
        (equal (f7-poly-remainder inverse modulus) inverse))))

(assert-event
 (let ((modulus '(6 0 1)))
   (and (equal (f7-poly-monic-euclidean-gcd '(6 1) modulus) '(6 1))
        (not (equal (f7-poly-monic-euclidean-gcd '(6 1) modulus)
                    (f7-polynomial-one))))))

(assert-event
 (and
  ; Zero-normalized modulus: only normalized nonzero constants meet the
  ; monic-GCD-one condition; ordinary normalized multiplication remains.
  (equal (f7-normalize '(3)) '(3))
  (equal (f7-poly-monic-euclidean-gcd '(3) nil) '(1))
  (equal (f7-poly-modular-inverse '(3) nil) '(5))
  (equal (f7-poly-reduced-one nil) '(1))
  (equal (f7-poly-reduced-mul '(3) '(5) nil) '(1))
  (equal (f7-poly-reduced-mul '(5) '(3) nil) '(1))
  ; Polynomial-one and every normalized nonzero constant modulus are the
  ; trivial ring, including malformed/trailing input normalization.
  (equal (f7-poly-monic-euclidean-gcd '(8 -7 8) '(1)) '(1))
  (equal (f7-poly-modular-inverse '(8 -7 8) '(1)) nil)
  (equal (f7-poly-reduced-one '(1)) nil)
  (equal (f7-poly-reduced-mul '(8 -7 8) nil '(1)) nil)
  (equal (f7-poly-reduced-mul nil '(8 -7 8) '(1)) nil)
  (equal (f7-poly-monic-euclidean-gcd '(1 0 1 . bad) '(9 0 . tail)) '(1))
  (equal (f7-poly-modular-inverse '(1 0 1 . bad) '(9 0 . tail)) nil)
  (equal (f7-poly-reduced-one '(9 0 . tail)) nil)
  (equal (f7-poly-reduced-mul '(1 0 1 . bad) nil '(9 0 . tail)) nil)
  (equal (f7-poly-reduced-mul nil '(1 0 1 . bad) '(9 0 . tail)) nil)))
