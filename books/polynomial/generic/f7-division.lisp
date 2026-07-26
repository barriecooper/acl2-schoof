(in-package "GPOLY")
(include-book "pfield-instance")
(include-book "modular-inverse")


; Ordinary generated recursive division over the named concrete field.
(verify-guards gfield::f7-element-p)
(verify-guards f7-coefficient-list-p)
(verify-guards f7-canonical-polynomial-p)
(def-divmod-instance
  f7-poly-divmod-core f7-poly-divmod f7-canonical-polynomial-p
  f7-poly-degree f7-poly-division-step-core f7-poly-add f7-normalize
  f7-poly-division-step-core-length-decreases)
(def-divmod-projections-instance
  f7-poly-quotient f7-poly-remainder f7-poly-divmod)

(defthm f7-add-fixed-congruence-for-divmod-instantiation
  (implies (and (equal (gfield::f7-fix x1) (gfield::f7-fix x2))
                (equal (gfield::f7-fix y1) (gfield::f7-fix y2)))
           (equal (gfield::f7-add x1 y1) (gfield::f7-add x2 y2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (gfield::f7-add)
                                    (gfield::f7-fix)))))
(defthm f7-mul-fixed-congruence-for-divmod-instantiation
  (implies (and (equal (gfield::f7-fix x1) (gfield::f7-fix x2))
                (equal (gfield::f7-fix y1) (gfield::f7-fix y2)))
           (equal (gfield::f7-mul x1 y1) (gfield::f7-mul x2 y2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (gfield::f7-mul)
                                    (gfield::f7-fix)))))
(defthm f7-inv-fixed-congruence-for-gcd-instantiation
  (implies (equal (gfield::f7-fix x1) (gfield::f7-fix x2))
           (equal (gfield::f7-inv x1) (gfield::f7-inv x2)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance gfield::f7-inv-logical-definition (x x1))
                 (:instance gfield::f7-inv-logical-definition (x x2)))
           :in-theory (disable gfield::f7-inv-logical-definition))))
(defthm f7-trim-change-implies-last-zero-for-divmod-instantiation
  (implies (and (f7-coefficient-list-p xs)
                (not (equal (f7-trim-trailing-zeros xs) xs)))
           (equal (car (last xs)) (gfield::f7-zero)))
  :hints (("Goal"
           :use ((:instance
                  f7-trim-trailing-zeros-when-coefficient-list-p-and-last-nonzero
                  (p xs)))
           :in-theory (enable f7-coefficient-list-p))))

(defthm f7-poly-divmod-public-interface-from-generic
  (and (f7-canonical-polynomial-p (mv-nth 0 (f7-poly-divmod f g)))
       (f7-canonical-polynomial-p (mv-nth 1 (f7-poly-divmod f g)))
       (equal (f7-poly-add
               (f7-poly-mul (mv-nth 0 (f7-poly-divmod f g))
                            (f7-normalize g))
               (mv-nth 1 (f7-poly-divmod f g)))
              (f7-normalize f))
       (implies (consp (f7-normalize g))
                (or (equal (mv-nth 1 (f7-poly-divmod f g)) nil)
                    (< (f7-poly-degree (mv-nth 1 (f7-poly-divmod f g)))
                       (f7-poly-degree (f7-normalize g))))))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                        poly-divmod-public-interface
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
                        (zero-prefix f7-zero-prefix)
                        (poly-shift f7-poly-shift) (monomial f7-monomial)
                        (poly-degree f7-poly-degree)
                        (poly-leading-coefficient f7-poly-leading-coefficient)
                        (poly-division-step-core f7-poly-division-step-core)
                        (poly-division-step f7-poly-division-step)
                        (poly-division-step-term f7-poly-division-step-term)
                        (poly-division-step-next f7-poly-division-step-next)
                        (poly-divmod-core f7-poly-divmod-core)
                        (poly-divmod f7-poly-divmod)))
          ("Subgoal 29.2" :use gfield::f7-mul-inverse-right)
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
          ("Subgoal 22.2.1"
           :use gfield::f7-element-p-of-f7-fix
           :in-theory (enable gfield::f7-fix gfield::f7-element-p))
          ("Subgoal 22.2.1'''" :in-theory (enable mod))
          ("Subgoal 22.2.1'" :in-theory (enable mod))
          ("Subgoal 21.2.1'" :in-theory (enable mod))
          ("Subgoal 9.9.1'" :use ((:instance f7-poly-divmod-core)))
          ("Subgoal 6.9.1'" :use ((:instance f7-poly-divmod-core)))
          ("Subgoal 2.3'"
           :use f7-trim-change-implies-last-zero-for-divmod-instantiation)
          ("Subgoal 2.1"
           :use ((:instance f7-canonical-polynomial-p-implies-last-nonzero
                            (p xs))))
          ("Subgoal 8.2.1'" :in-theory (enable mod))))

(defthm f7-poly-divmod-quotient-canonical
  (f7-canonical-polynomial-p (mv-nth 0 (f7-poly-divmod f g)))
  :hints (("Goal" :use f7-poly-divmod-public-interface-from-generic)))
(defthm f7-poly-divmod-remainder-canonical
  (f7-canonical-polynomial-p (mv-nth 1 (f7-poly-divmod f g)))
  :hints (("Goal" :use f7-poly-divmod-public-interface-from-generic)))
(defthm f7-poly-divmod-reconstruction
  (equal (f7-poly-add
          (f7-poly-mul (mv-nth 0 (f7-poly-divmod f g)) (f7-normalize g))
          (mv-nth 1 (f7-poly-divmod f g)))
         (f7-normalize f))
  :rule-classes nil
  :hints (("Goal" :use f7-poly-divmod-public-interface-from-generic)))
(defthm f7-poly-divmod-final-remainder-degree-bound
  (implies (consp (f7-normalize g))
           (or (equal (mv-nth 1 (f7-poly-divmod f g)) nil)
               (< (f7-poly-degree (mv-nth 1 (f7-poly-divmod f g)))
                  (f7-poly-degree (f7-normalize g)))))
  :rule-classes nil
  :hints (("Goal" :use f7-poly-divmod-public-interface-from-generic)))
(defthm f7-poly-quotient-is-divmod-quotient
  (equal (f7-poly-quotient f g) (mv-nth 0 (f7-poly-divmod f g)))
  :hints (("Goal" :in-theory (enable f7-poly-quotient))))
(defthm f7-poly-remainder-is-divmod-remainder
  (equal (f7-poly-remainder f g) (mv-nth 1 (f7-poly-divmod f g)))
  :hints (("Goal" :in-theory (enable f7-poly-remainder))))
(defthm f7-poly-remainder-of-normalize-dividend
  (equal (f7-poly-remainder (f7-normalize f) g)
         (f7-poly-remainder f g))
  :hints (("Goal"
           :in-theory (e/d (f7-poly-remainder f7-poly-divmod)
                            (f7-poly-divmod-core
                             f7-poly-division-step-core
                             f7-poly-division-step)))))

(defthm f7-poly-remainder-of-fix-coefficients-dividend
  (equal (f7-poly-remainder (f7-fix-coefficients dividend) modulus)
         (f7-poly-remainder dividend modulus))
  :hints
  (("Goal"
    :by (:functional-instance
         poly-remainder-of-fix-coefficients-dividend
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
         (zero-prefix f7-zero-prefix)
         (poly-shift f7-poly-shift) (monomial f7-monomial)
         (poly-degree f7-poly-degree)
         (poly-leading-coefficient f7-poly-leading-coefficient)
         (poly-division-step-core f7-poly-division-step-core)
         (poly-division-step f7-poly-division-step)
         (poly-division-step-term f7-poly-division-step-term)
         (poly-division-step-next f7-poly-division-step-next)
         (poly-divmod-core f7-poly-divmod-core)
         (poly-divmod f7-poly-divmod)
         (poly-remainder f7-poly-remainder))
    :in-theory
    (disable poly-remainder f7-poly-remainder
             poly-divmod f7-poly-divmod
             poly-divmod-core f7-poly-divmod-core
             poly-division-step f7-poly-division-step
             poly-division-step-core f7-poly-division-step-core
             poly-division-step-term f7-poly-division-step-term
             poly-division-step-next f7-poly-division-step-next
             normalize f7-normalize
             fix-coefficients f7-fix-coefficients
             trim-trailing-zeros f7-trim-trailing-zeros
             raw-add f7-raw-add poly-add f7-poly-add
             raw-neg f7-raw-neg poly-neg f7-poly-neg
             poly-sub f7-poly-sub
             raw-scale f7-raw-scale poly-scale f7-poly-scale
             raw-mul f7-raw-mul poly-mul f7-poly-mul))))

(defthm f7-poly-remainder-of-fix-coefficients-modulus
  (equal (f7-poly-remainder dividend (f7-fix-coefficients modulus))
         (f7-poly-remainder dividend modulus))
  :hints
  (("Goal"
    :by (:functional-instance
         poly-remainder-of-fix-coefficients-modulus
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
         (zero-prefix f7-zero-prefix)
         (poly-shift f7-poly-shift) (monomial f7-monomial)
         (poly-degree f7-poly-degree)
         (poly-leading-coefficient f7-poly-leading-coefficient)
         (poly-division-step-core f7-poly-division-step-core)
         (poly-division-step f7-poly-division-step)
         (poly-division-step-term f7-poly-division-step-term)
         (poly-division-step-next f7-poly-division-step-next)
         (poly-divmod-core f7-poly-divmod-core)
         (poly-divmod f7-poly-divmod)
         (poly-remainder f7-poly-remainder))
    :in-theory
    (disable poly-remainder f7-poly-remainder
             poly-divmod f7-poly-divmod
             poly-divmod-core f7-poly-divmod-core
             poly-division-step f7-poly-division-step
             poly-division-step-core f7-poly-division-step-core
             poly-division-step-term f7-poly-division-step-term
             poly-division-step-next f7-poly-division-step-next
             normalize f7-normalize
             fix-coefficients f7-fix-coefficients
             trim-trailing-zeros f7-trim-trailing-zeros
             raw-add f7-raw-add poly-add f7-poly-add
             raw-neg f7-raw-neg poly-neg f7-poly-neg
             poly-sub f7-poly-sub
             raw-scale f7-raw-scale poly-scale f7-poly-scale
             raw-mul f7-raw-mul poly-mul f7-poly-mul))))

(local
 (defthm f7-poly-remainder-of-fix-coefficients-regressions
   (and
    (equal (f7-poly-remainder (f7-fix-coefficients nil) modulus)
           (f7-poly-remainder nil modulus))
    (equal (f7-poly-remainder (f7-fix-coefficients 'bad-dividend) '(1 0 1))
           (f7-poly-remainder 'bad-dividend '(1 0 1)))
    (equal (f7-poly-remainder
            (f7-fix-coefficients '(8 -1 14 -8 0 0)) '(1 0 1))
           (f7-poly-remainder '(8 -1 14 -8 0 0) '(1 0 1)))
    (equal (f7-poly-remainder
            (f7-fix-coefficients '(8 -1 . bad-tail)) modulus)
           (f7-poly-remainder '(8 -1 . bad-tail) modulus))
    (equal (f7-poly-remainder dividend (f7-fix-coefficients nil))
           (f7-poly-remainder dividend nil))
    (equal (f7-poly-remainder dividend
                              (f7-fix-coefficients 'bad-modulus))
           (f7-poly-remainder dividend 'bad-modulus))
    (equal (f7-poly-remainder dividend (f7-fix-coefficients '(3)))
           (f7-poly-remainder dividend '(3)))
    (equal (f7-poly-remainder dividend
                              (f7-fix-coefficients '(7 14 0 . tail)))
           (f7-poly-remainder dividend '(7 14 0 . tail)))
    (equal (f7-poly-remainder dividend
                              (f7-fix-coefficients '(8 -1 14 -8 0)))
           (f7-poly-remainder dividend '(8 -1 14 -8 0)))
    (equal
     (f7-poly-remainder
      (f7-fix-coefficients '(8 -1 14 -8 . dividend-tail))
      (f7-fix-coefficients '(7 14 0 . modulus-tail)))
     (f7-poly-remainder '(8 -1 14 -8 . dividend-tail)
                        '(7 14 0 . modulus-tail))))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance f7-poly-remainder-of-fix-coefficients-dividend
                 (dividend nil))
      (:instance f7-poly-remainder-of-fix-coefficients-dividend
                 (dividend 'bad-dividend) (modulus '(1 0 1)))
      (:instance f7-poly-remainder-of-fix-coefficients-dividend
                 (dividend '(8 -1 14 -8 0 0)) (modulus '(1 0 1)))
      (:instance f7-poly-remainder-of-fix-coefficients-dividend
                 (dividend '(8 -1 . bad-tail)))
      (:instance f7-poly-remainder-of-fix-coefficients-modulus
                 (modulus nil))
      (:instance f7-poly-remainder-of-fix-coefficients-modulus
                 (modulus 'bad-modulus))
      (:instance f7-poly-remainder-of-fix-coefficients-modulus
                 (modulus '(3)))
      (:instance f7-poly-remainder-of-fix-coefficients-modulus
                 (modulus '(7 14 0 . tail)))
      (:instance f7-poly-remainder-of-fix-coefficients-modulus
                 (modulus '(8 -1 14 -8 0)))
      (:instance f7-poly-remainder-of-fix-coefficients-dividend
                 (dividend '(8 -1 14 -8 . dividend-tail))
                 (modulus
                  (f7-fix-coefficients '(7 14 0 . modulus-tail))))
      (:instance f7-poly-remainder-of-fix-coefficients-modulus
                 (dividend '(8 -1 14 -8 . dividend-tail))
                 (modulus '(7 14 0 . modulus-tail))))
     :in-theory
     (disable f7-poly-remainder-of-fix-coefficients-dividend
              f7-poly-remainder-of-fix-coefficients-modulus
              poly-remainder f7-poly-remainder
              poly-divmod f7-poly-divmod
              poly-divmod-core f7-poly-divmod-core
              poly-division-step f7-poly-division-step
              poly-division-step-core f7-poly-division-step-core
              poly-division-step-term f7-poly-division-step-term
              poly-division-step-next f7-poly-division-step-next
              normalize f7-normalize
              fix-coefficients f7-fix-coefficients
              trim-trailing-zeros f7-trim-trailing-zeros
              gfield::f7-fix gfield::f7-add gfield::f7-mul
              gfield::f7-neg gfield::f7-inv gfield::f7-div
              raw-add f7-raw-add poly-add f7-poly-add
              raw-neg f7-raw-neg poly-neg f7-poly-neg
              poly-sub f7-poly-sub
              raw-scale f7-raw-scale poly-scale f7-poly-scale
              raw-mul f7-raw-mul poly-mul f7-poly-mul
              poly-congruent-p)))))

(defthm f7-poly-remainder-canonical
  (f7-canonical-polynomial-p (f7-poly-remainder f g))
  :hints (("Goal" :use f7-poly-divmod-remainder-canonical)))

; A single symbolic leading-term cancellation by the presentation modulus.
; This deliberately opens the concrete recursion only for a canonical
; degree-two dividend; the exported statement exposes only the remainder.
(defthm f7-poly-remainder-degree-two-by-x2-plus-one
  (implies (and (gfield::f7-element-p a)
                (gfield::f7-element-p b)
                (gfield::f7-element-p c)
                (not (equal c 0)))
           (equal (f7-poly-remainder (list a b c) '(1 0 1))
                  (f7-normalize
                   (list (gfield::f7-sub a c) b))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory
           (enable f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
                   f7-poly-division-step-core f7-poly-degree
                   f7-poly-leading-coefficient f7-monomial f7-zero-prefix
                   f7-poly-sub f7-poly-add f7-raw-add f7-poly-neg f7-raw-neg
                   f7-poly-mul f7-raw-mul f7-poly-scale f7-raw-scale
                   f7-poly-shift f7-normalize f7-fix-coefficients
                   f7-trim-trailing-zeros gfield::f7-div gfield::f7-inv
                   gfield::f7-sub gfield::f7-add gfield::f7-neg
                   gfield::f7-mul gfield::f7-fix))))

(defthm f7-poly-remainder-degree-two-by-x2-plus-one-regressions
  (and (equal (f7-poly-remainder '(0 0 1) '(1 0 1)) '(6))
       (equal (f7-poly-remainder '(1 0 1) '(1 0 1)) nil)
       (equal (f7-poly-remainder '(0 1 1) '(1 0 1)) '(6 1))
       (equal (f7-poly-remainder '(1 1 1) '(1 0 1)) '(0 1))
       (equal (f7-poly-remainder '(2 0 1) '(1 0 1)) '(1))
       (equal (f7-poly-remainder '(3 4 3) '(1 0 1)) '(0 4)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable f7-poly-remainder
                                      f7-poly-divmod
                                      f7-poly-divmod-core))))
(defthm f7-poly-divmod-zero-normalized-divisor
  (implies (equal (f7-normalize g) nil)
           (equal (f7-poly-divmod f g) (mv nil (f7-normalize f))))
  :hints (("Goal" :in-theory (enable f7-poly-divmod f7-poly-divmod-core))))
(defthm f7-poly-divmod-nonzero-constant-regression
  (equal (f7-poly-divmod '(1 2 3) '(2)) (mv '(4 1 5) nil)))
(defthm f7-poly-divmod-zero-normalized-regression
  (equal (f7-poly-divmod '(1 9 0) '(7 14 . bad)) (mv nil '(1 2))))

; Focused exact ordinary-execution regressions, including total malformed input.
(assert-event (mv-let (q r) (f7-poly-divmod '(6 1 1) '(1 1))
                (and (equal q '(0 1)) (equal r '(6)))))
(assert-event (mv-let (q r) (f7-poly-divmod '(1 0 0 1) '(1 1))
                (and (equal q '(1 6 1)) (equal r nil))))
(assert-event (mv-let (q r) (f7-poly-divmod '(1) '(0 1))
                (and (equal q nil) (equal r '(1)))))
(assert-event (mv-let (q r) (f7-poly-divmod '(8 9 0 0) '(1 1 0))
                (and (equal q '(2)) (equal r '(6)))))
(assert-event (mv-let (q r) (f7-poly-divmod 'malformed '(1 1))
                (and (equal q nil) (equal r nil))))
(assert-event (mv-let (q r) (f7-poly-divmod '(1 2 . bad) '(1 . bad))
                (and (equal q '(1 2)) (equal r nil))))
(assert-event
 (mv-let (q r) (f7-poly-divmod '(1 0 0 1) '(1 1))
   (and (equal q (f7-poly-quotient '(1 0 0 1) '(1 1)))
        (equal r (f7-poly-remainder '(1 0 0 1) '(1 1)))
        (f7-canonical-polynomial-p r)
        (equal (f7-normalize r) r)
        (equal (f7-poly-add (f7-poly-mul q '(1 1)) r) '(1 0 0 1)))))

; Canonical-representative executions use the retained remainder projection,
; not a second quotient reduction runtime.  Each representative is fixed by
; normalization and repeated reduction; positive-degree nonzero results also
; satisfy the strict degree bound.
(assert-event
 (let* ((large (f7-poly-remainder '(6 1 1) '(1 1)))
        (bounded (f7-poly-remainder '(6) '(1 1)))
        (exact (f7-poly-remainder '(1 0 0 1) '(1 1)))
        (zero-dividend (f7-poly-remainder nil '(1 1)))
        (zero-modulus (f7-poly-remainder '(8 9 0) nil))
        (one-modulus (f7-poly-remainder '(1 2 3) '(1)))
        (constant-modulus (f7-poly-remainder '(1 2 3) '(2)))
        (trailing-zeroes (f7-poly-remainder '(8 9 0 0) '(1 1 0)))
        (malformed-atom (f7-poly-remainder 'malformed '(1 1)))
        (dotted (f7-poly-remainder '(1 2 . bad) '(1 1))))
   (and (equal large '(6))
        (equal bounded '(6))
        (equal exact nil)
        (equal zero-dividend nil)
        (equal zero-modulus '(1 2))
        (equal one-modulus nil)
        (equal constant-modulus nil)
        (equal trailing-zeroes '(6))
        (equal malformed-atom nil)
        (equal dotted '(6))
        (f7-canonical-polynomial-p large)
        (f7-canonical-polynomial-p bounded)
        (f7-canonical-polynomial-p zero-modulus)
        (equal (f7-normalize large) large)
        (equal (f7-normalize bounded) bounded)
        (equal (f7-normalize zero-modulus) zero-modulus)
        (< (f7-poly-degree large) (f7-poly-degree (f7-normalize '(1 1))))
        (< (f7-poly-degree bounded) (f7-poly-degree (f7-normalize '(1 1))))
        (equal (f7-poly-remainder large '(1 1)) large)
        (equal (f7-poly-remainder bounded '(1 1)) bounded)
        (equal (f7-poly-remainder zero-modulus nil) zero-modulus))))

(verify-guards f7-poly-divmod-core)
(verify-guards f7-poly-divmod)
(verify-guards f7-poly-quotient)
(verify-guards f7-poly-remainder)

; Concrete divisor-first predicates are retained because the later monic GCD
; correctness instance names them directly.
(def-divisibility-instance
  f7-poly-divides-p f7-poly-common-divisor-p f7-poly-remainder)

; The complete substitution is intentionally visible at the theorem boundary.
(defthm f7-poly-divides-p-of-poly-monic-normalize-dividend
  (equal (f7-poly-divides-p divisor (f7-poly-monic-normalize dividend))
         (f7-poly-divides-p divisor dividend))
  :hints (("Goal" :by (:functional-instance
    poly-divides-p-of-poly-monic-normalize-dividend
    (gfield::field-element-p gfield::f7-element-p)
    (gfield::field-fix gfield::f7-fix) (gfield::field-zero gfield::f7-zero)
    (gfield::field-one gfield::f7-one) (gfield::field-add gfield::f7-add)
    (gfield::field-mul gfield::f7-mul) (gfield::field-neg gfield::f7-neg)
    (gfield::field-inv gfield::f7-inv) (gfield::field-div gfield::f7-div)
    (fix-coefficients f7-fix-coefficients)
    (trim-trailing-zeros f7-trim-trailing-zeros) (normalize f7-normalize)
    (coefficient-list-p f7-coefficient-list-p) (polynomial-p f7-polynomial-p)
    (canonical-polynomial-p f7-canonical-polynomial-p)
    (raw-add f7-raw-add) (poly-add f7-poly-add) (raw-neg f7-raw-neg)
    (poly-neg f7-poly-neg) (poly-sub f7-poly-sub)
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
    (poly-divmod-core f7-poly-divmod-core) (poly-divmod f7-poly-divmod)
    (poly-remainder f7-poly-remainder) (poly-divides-p f7-poly-divides-p)
    (poly-common-divisor-p f7-poly-common-divisor-p)))
    ("Subgoal 29.7''" :use
     ((:instance f7-mul-fixed-congruence-for-divmod-instantiation
                 (x1 gfield::x1) (x2 gfield::x2)
                 (y1 gfield::y1) (y2 gfield::y2))))
    ("Subgoal 29.7'" :use
     ((:instance f7-mul-fixed-congruence-for-divmod-instantiation
                 (x1 gfield::x1) (x2 gfield::x2)
                 (y1 gfield::y1) (y2 gfield::y2))))))

(defthm f7-poly-divides-p-of-poly-monic-normalize-divisor
  (equal (f7-poly-divides-p (f7-poly-monic-normalize divisor) dividend)
         (f7-poly-divides-p divisor dividend))
  :hints (("Goal" :by (:functional-instance
    poly-divides-p-of-poly-monic-normalize-divisor
    (gfield::field-element-p gfield::f7-element-p)
    (gfield::field-fix gfield::f7-fix) (gfield::field-zero gfield::f7-zero)
    (gfield::field-one gfield::f7-one) (gfield::field-add gfield::f7-add)
    (gfield::field-mul gfield::f7-mul) (gfield::field-neg gfield::f7-neg)
    (gfield::field-inv gfield::f7-inv) (gfield::field-div gfield::f7-div)
    (fix-coefficients f7-fix-coefficients)
    (trim-trailing-zeros f7-trim-trailing-zeros) (normalize f7-normalize)
    (coefficient-list-p f7-coefficient-list-p) (polynomial-p f7-polynomial-p)
    (canonical-polynomial-p f7-canonical-polynomial-p)
    (raw-add f7-raw-add) (poly-add f7-poly-add) (raw-neg f7-raw-neg)
    (poly-neg f7-poly-neg) (poly-sub f7-poly-sub)
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
    (poly-divmod-core f7-poly-divmod-core) (poly-divmod f7-poly-divmod)
    (poly-remainder f7-poly-remainder) (poly-divides-p f7-poly-divides-p)
    (poly-common-divisor-p f7-poly-common-divisor-p)))
    ("Subgoal 29.7''" :use
     ((:instance f7-mul-fixed-congruence-for-divmod-instantiation
                 (x1 gfield::x1) (x2 gfield::x2)
                 (y1 gfield::y1) (y2 gfield::y2))))
    ("Subgoal 29.7'" :use
     ((:instance f7-mul-fixed-congruence-for-divmod-instantiation
                 (x1 gfield::x1) (x2 gfield::x2)
                 (y1 gfield::y1) (y2 gfield::y2))))))

(defthm f7-poly-common-divisor-p-of-poly-monic-normalize
  (equal (f7-poly-common-divisor-p
          candidate (f7-poly-monic-normalize first)
          (f7-poly-monic-normalize second))
         (f7-poly-common-divisor-p candidate first second))
  :hints
  (("Goal"
    :use ((:instance f7-poly-divides-p-of-poly-monic-normalize-dividend
                     (divisor candidate) (dividend first))
          (:instance f7-poly-divides-p-of-poly-monic-normalize-dividend
                     (divisor candidate) (dividend second)))
    :in-theory (e/d (f7-poly-common-divisor-p)
                    (f7-poly-divides-p
                     f7-poly-divides-p-of-poly-monic-normalize-dividend)))))

; Exact total-semantics and witness regressions.  The witness orientation is
; DIVIDEND = DIVISOR * WITNESS, as checked by the explicit products below.
(assert-event (equal (f7-poly-monic-normalize '(1 2)) '(4 1)))
(assert-event (equal (f7-poly-monic-normalize '(3 1)) '(3 1)))
(assert-event (equal (f7-poly-monic-normalize '(3)) '(1)))
(assert-event (equal (f7-poly-monic-normalize nil) nil))
(assert-event (equal (f7-poly-monic-normalize '(1 9)) '(4 1)))
(assert-event (equal (f7-poly-monic-normalize '(1 2 0 0)) '(4 1)))
(assert-event (equal (f7-poly-monic-normalize 'bad) nil))
(assert-event (equal (f7-poly-monic-normalize '(1 2 . bad)) '(4 1)))
(assert-event (equal (gfield::f7-mul 15 10)
                     (gfield::f7-mul (gfield::f7-fix 1)
                                     (gfield::f7-fix 3))))
(assert-event
 (and (equal (gfield::f7-add 15 -4) (gfield::f7-add 1 3))
      (equal (gfield::f7-add 'bad 7) (gfield::f7-add nil 0))
      (equal (gfield::f7-inv -6) (gfield::f7-inv 1))
      (equal (gfield::f7-inv 0) 0)
      (equal (gfield::f7-inv 7) 0)
      (equal (gfield::f7-inv -7) 0)
      (equal (gfield::f7-inv 'bad) 0)
      (equal (gfield::f7-div -6 8) (gfield::f7-div 1 1))
      (equal (gfield::f7-div 3 0) 0)
      (equal (gfield::f7-div 3 7) 0)
      (equal (gfield::f7-div 3 -7) 0)
      (equal (gfield::f7-div 'bad 'also-bad) 0)))
(assert-event
 (and (equal (f7-poly-mul '(1 2) '(3)) '(3 6))
      (f7-poly-divides-p '(1 2) '(3 6))
      (f7-poly-divides-p (f7-poly-monic-normalize '(1 2)) '(3 6))))
(assert-event
 (and (equal (f7-poly-mul '(4 1) '(2 4)) '(1 4 4))
      (f7-poly-divides-p '(4 1) '(1 4 4))
      (f7-poly-divides-p '(1 2) '(1 4 4))))

; The public remainder is already canonical, so normalizing it does not
; change the length used by the generic Euclidean recursion.
(defthm normalize-f7-poly-remainder-strict-length-bound
  (implies (consp (f7-normalize modulus))
           (< (len (f7-normalize (f7-poly-remainder dividend modulus)))
              (len (f7-normalize modulus))))
  :rule-classes :linear
  :hints
  (("Goal"
    :use ((:instance f7-poly-divmod-final-remainder-degree-bound
                     (f dividend) (g modulus))
          (:instance f7-poly-remainder-canonical
                     (f dividend) (g modulus))
          (:instance f7-poly-remainder-is-divmod-remainder
                     (f dividend) (g modulus))
          (:instance f7-normalize-when-canonical
                     (xs (f7-poly-remainder dividend modulus)))
          (:instance f7-degree-when-canonical-nonzero
                     (p (f7-poly-remainder dividend modulus)))
          (:instance f7-degree-when-canonical-nonzero
                     (p (f7-normalize modulus)))
          (:instance f7-canonical-polynomial-p-of-normalize (xs modulus)))
    :cases ((consp (f7-poly-remainder dividend modulus)))
    :in-theory (disable f7-normalize f7-poly-remainder f7-poly-divmod
                        f7-poly-degree f7-canonical-polynomial-p))))

; This is the ordinary raw Euclidean recursion from DEF-EUCLIDEAN-GCD-INSTANCE,
; expanded here because that generator also emits the deliberately deferred
; monic wrapper.
(defun f7-poly-euclidean-gcd (first second)
  (declare
   (xargs
    :measure (len (f7-normalize second))
    :hints (("Goal"
             :use ((:instance normalize-f7-poly-remainder-strict-length-bound
                              (dividend first) (modulus second)))
             :in-theory (disable f7-normalize f7-poly-remainder)))))
  (if (consp (f7-normalize second))
      (f7-poly-euclidean-gcd second (f7-poly-remainder first second))
    (f7-normalize first)))

(verify-guards f7-poly-euclidean-gcd)

; The raw theorem deliberately omits monic normalization: it is the direct
; concrete instance of the generic raw common-divisor specification.
(defthm f7-poly-euclidean-gcd-raw-correct
  (and
   (f7-poly-common-divisor-p
    (f7-poly-euclidean-gcd first second) first second)
   (implies
    (f7-poly-common-divisor-p divisor first second)
    (f7-poly-divides-p divisor (f7-poly-euclidean-gcd first second))))
  :rule-classes nil
  :hints
  (("Goal"
    :by (:functional-instance
         poly-euclidean-gcd-raw-correct
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
         (zero-prefix f7-zero-prefix)
         (poly-shift f7-poly-shift) (monomial f7-monomial)
         (poly-degree f7-poly-degree)
         (poly-leading-coefficient f7-poly-leading-coefficient)
         (poly-division-step-core f7-poly-division-step-core)
         (poly-division-step f7-poly-division-step)
         (poly-division-step-term f7-poly-division-step-term)
         (poly-division-step-next f7-poly-division-step-next)
         (poly-divmod-core f7-poly-divmod-core)
         (poly-divmod f7-poly-divmod)
         (poly-remainder f7-poly-remainder)
         (poly-divides-p f7-poly-divides-p)
         (poly-common-divisor-p f7-poly-common-divisor-p)
         (poly-euclidean-gcd f7-poly-euclidean-gcd)))
   ("Subgoal 29.7''"
    :use ((:instance f7-mul-fixed-congruence-for-divmod-instantiation
                     (x1 gfield::x1) (x2 gfield::x2)
                     (y1 gfield::y1) (y2 gfield::y2))))
   ("Subgoal 29.7'"
    :use ((:instance f7-mul-fixed-congruence-for-divmod-instantiation
                     (x1 gfield::x1) (x2 gfield::x2)
                     (y1 gfield::y1) (y2 gfield::y2))))
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
   ("Subgoal 24.3"
    :use ((:instance f7-inv-fixed-congruence-for-gcd-instantiation
                     (x1 gfield::x1) (x2 gfield::x2))))))

(defthm f7-poly-euclidean-gcd-divides-first
  (f7-poly-divides-p (f7-poly-euclidean-gcd first second) first)
  :hints (("Goal" :use ((:instance f7-poly-euclidean-gcd-raw-correct))
           :in-theory (enable f7-poly-common-divisor-p))))

(defthm f7-poly-euclidean-gcd-divides-second
  (f7-poly-divides-p (f7-poly-euclidean-gcd first second) second)
  :hints (("Goal" :use ((:instance f7-poly-euclidean-gcd-raw-correct))
           :in-theory (enable f7-poly-common-divisor-p))))

(defthm f7-poly-common-divisor-divides-euclidean-gcd
  (implies (f7-poly-common-divisor-p divisor first second)
           (f7-poly-divides-p divisor (f7-poly-euclidean-gcd first second)))
  :hints (("Goal" :use ((:instance f7-poly-euclidean-gcd-raw-correct)))))

; Concrete raw extended Euclidean computation.  This is the generic XGCD
; recursion specialized transparently to F7; its one DIVMOD call supplies both
; the quotient used in the Bezout update and the remainder used for descent.
(defun f7-poly-extended-euclidean-gcd (first second)
  (declare
   (xargs
    :measure (len (f7-normalize second))
    :hints
    (("Goal"
      :use ((:instance normalize-f7-poly-remainder-strict-length-bound
                       (dividend first) (modulus second))
            (:instance f7-poly-remainder-is-divmod-remainder
                       (f first) (g second)))
      :in-theory (disable f7-normalize f7-poly-remainder f7-poly-divmod)))))
  (if (consp (f7-normalize second))
      (mv-let (quotient remainder)
        (f7-poly-divmod first second)
        (mv-let (gcd s-next t-next)
          (f7-poly-extended-euclidean-gcd second remainder)
          (mv gcd t-next
              (f7-poly-sub s-next (f7-poly-mul t-next quotient)))))
    (mv (f7-normalize first) (f7-polynomial-one) nil)))

(verify-guards f7-poly-extended-euclidean-gcd)

(defthm f7-poly-extended-euclidean-gcd-zero-second
  (implies (not (consp (f7-normalize second)))
           (equal (f7-poly-extended-euclidean-gcd first second)
                  (mv (f7-normalize first) (f7-polynomial-one) nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (f7-poly-extended-euclidean-gcd)
                                      (f7-normalize f7-polynomial-one)))))

(defthm f7-poly-extended-euclidean-gcd-nonzero-second
  (implies
   (consp (f7-normalize second))
   (equal
    (f7-poly-extended-euclidean-gcd first second)
    (mv-let (quotient remainder)
      (f7-poly-divmod first second)
      (mv-let (gcd s-next t-next)
        (f7-poly-extended-euclidean-gcd second remainder)
        (mv gcd t-next
            (f7-poly-sub s-next (f7-poly-mul t-next quotient)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (f7-poly-extended-euclidean-gcd)
                                      (f7-poly-divmod f7-normalize
                                       f7-poly-sub f7-poly-mul)))))

(defthm f7-poly-extended-euclidean-gcd-gcd-is-f7-poly-euclidean-gcd
  (equal (mv-nth 0 (f7-poly-extended-euclidean-gcd first second))
         (f7-poly-euclidean-gcd first second))

  :hints (("Goal" :by (:functional-instance
                        poly-extended-euclidean-gcd-gcd-is-poly-euclidean-gcd
         (gfield::field-element-p gfield::f7-element-p)
         (gfield::field-fix gfield::f7-fix) (gfield::field-zero gfield::f7-zero)
         (gfield::field-one gfield::f7-one) (gfield::field-add gfield::f7-add)
         (gfield::field-mul gfield::f7-mul) (gfield::field-neg gfield::f7-neg)
         (gfield::field-inv gfield::f7-inv) (gfield::field-div gfield::f7-div)
         (fix-coefficients f7-fix-coefficients)
         (trim-trailing-zeros f7-trim-trailing-zeros) (normalize f7-normalize)
         (coefficient-list-p f7-coefficient-list-p)
         (polynomial-p f7-polynomial-p)
         (canonical-polynomial-p f7-canonical-polynomial-p)
         (raw-add f7-raw-add) (poly-add f7-poly-add)
         (raw-neg f7-raw-neg) (poly-neg f7-poly-neg) (poly-sub f7-poly-sub)
         (raw-scale f7-raw-scale) (poly-scale f7-poly-scale)
         (raw-mul f7-raw-mul) (poly-mul f7-poly-mul)
         (const f7-const) (polynomial-one f7-polynomial-one)
         (zero-prefix f7-zero-prefix) (poly-shift f7-poly-shift)
         (monomial f7-monomial) (poly-degree f7-poly-degree)
         (poly-leading-coefficient f7-poly-leading-coefficient)
         (poly-division-step-core f7-poly-division-step-core)
         (poly-division-step f7-poly-division-step)
         (poly-division-step-term f7-poly-division-step-term)
         (poly-division-step-next f7-poly-division-step-next)
         (poly-divmod-core f7-poly-divmod-core) (poly-divmod f7-poly-divmod)
         (poly-remainder f7-poly-remainder)
         (poly-euclidean-gcd f7-poly-euclidean-gcd)
         (poly-extended-euclidean-gcd f7-poly-extended-euclidean-gcd)))))

(defthm f7-poly-extended-euclidean-gcd-gcd-canonical
  (f7-canonical-polynomial-p
   (mv-nth 0 (f7-poly-extended-euclidean-gcd first second)))

  :hints (("Goal" :by (:functional-instance
                        poly-extended-euclidean-gcd-gcd-canonical
         (gfield::field-element-p gfield::f7-element-p)
         (gfield::field-fix gfield::f7-fix) (gfield::field-zero gfield::f7-zero)
         (gfield::field-one gfield::f7-one) (gfield::field-add gfield::f7-add)
         (gfield::field-mul gfield::f7-mul) (gfield::field-neg gfield::f7-neg)
         (gfield::field-inv gfield::f7-inv) (gfield::field-div gfield::f7-div)
         (fix-coefficients f7-fix-coefficients)
         (trim-trailing-zeros f7-trim-trailing-zeros) (normalize f7-normalize)
         (coefficient-list-p f7-coefficient-list-p)
         (polynomial-p f7-polynomial-p)
         (canonical-polynomial-p f7-canonical-polynomial-p)
         (raw-add f7-raw-add) (poly-add f7-poly-add)
         (raw-neg f7-raw-neg) (poly-neg f7-poly-neg) (poly-sub f7-poly-sub)
         (raw-scale f7-raw-scale) (poly-scale f7-poly-scale)
         (raw-mul f7-raw-mul) (poly-mul f7-poly-mul)
         (const f7-const) (polynomial-one f7-polynomial-one)
         (zero-prefix f7-zero-prefix) (poly-shift f7-poly-shift)
         (monomial f7-monomial) (poly-degree f7-poly-degree)
         (poly-leading-coefficient f7-poly-leading-coefficient)
         (poly-division-step-core f7-poly-division-step-core)
         (poly-division-step f7-poly-division-step)
         (poly-division-step-term f7-poly-division-step-term)
         (poly-division-step-next f7-poly-division-step-next)
         (poly-divmod-core f7-poly-divmod-core) (poly-divmod f7-poly-divmod)
         (poly-remainder f7-poly-remainder)
         (poly-euclidean-gcd f7-poly-euclidean-gcd)
         (poly-extended-euclidean-gcd f7-poly-extended-euclidean-gcd)))))

(defthm f7-poly-extended-euclidean-gcd-first-coefficient-canonical
  (f7-canonical-polynomial-p
   (mv-nth 1 (f7-poly-extended-euclidean-gcd first second)))

  :hints (("Goal" :by (:functional-instance
                        poly-extended-euclidean-gcd-first-coefficient-canonical
         (gfield::field-element-p gfield::f7-element-p)
         (gfield::field-fix gfield::f7-fix) (gfield::field-zero gfield::f7-zero)
         (gfield::field-one gfield::f7-one) (gfield::field-add gfield::f7-add)
         (gfield::field-mul gfield::f7-mul) (gfield::field-neg gfield::f7-neg)
         (gfield::field-inv gfield::f7-inv) (gfield::field-div gfield::f7-div)
         (fix-coefficients f7-fix-coefficients)
         (trim-trailing-zeros f7-trim-trailing-zeros) (normalize f7-normalize)
         (coefficient-list-p f7-coefficient-list-p)
         (polynomial-p f7-polynomial-p)
         (canonical-polynomial-p f7-canonical-polynomial-p)
         (raw-add f7-raw-add) (poly-add f7-poly-add)
         (raw-neg f7-raw-neg) (poly-neg f7-poly-neg) (poly-sub f7-poly-sub)
         (raw-scale f7-raw-scale) (poly-scale f7-poly-scale)
         (raw-mul f7-raw-mul) (poly-mul f7-poly-mul)
         (const f7-const) (polynomial-one f7-polynomial-one)
         (zero-prefix f7-zero-prefix) (poly-shift f7-poly-shift)
         (monomial f7-monomial) (poly-degree f7-poly-degree)
         (poly-leading-coefficient f7-poly-leading-coefficient)
         (poly-division-step-core f7-poly-division-step-core)
         (poly-division-step f7-poly-division-step)
         (poly-division-step-term f7-poly-division-step-term)
         (poly-division-step-next f7-poly-division-step-next)
         (poly-divmod-core f7-poly-divmod-core) (poly-divmod f7-poly-divmod)
         (poly-remainder f7-poly-remainder)
         (poly-euclidean-gcd f7-poly-euclidean-gcd)
         (poly-extended-euclidean-gcd f7-poly-extended-euclidean-gcd)))))

(defthm f7-poly-extended-euclidean-gcd-second-coefficient-canonical
  (f7-canonical-polynomial-p
   (mv-nth 2 (f7-poly-extended-euclidean-gcd first second)))

  :hints (("Goal" :by (:functional-instance
                        poly-extended-euclidean-gcd-second-coefficient-canonical
         (gfield::field-element-p gfield::f7-element-p)
         (gfield::field-fix gfield::f7-fix) (gfield::field-zero gfield::f7-zero)
         (gfield::field-one gfield::f7-one) (gfield::field-add gfield::f7-add)
         (gfield::field-mul gfield::f7-mul) (gfield::field-neg gfield::f7-neg)
         (gfield::field-inv gfield::f7-inv) (gfield::field-div gfield::f7-div)
         (fix-coefficients f7-fix-coefficients)
         (trim-trailing-zeros f7-trim-trailing-zeros) (normalize f7-normalize)
         (coefficient-list-p f7-coefficient-list-p)
         (polynomial-p f7-polynomial-p)
         (canonical-polynomial-p f7-canonical-polynomial-p)
         (raw-add f7-raw-add) (poly-add f7-poly-add)
         (raw-neg f7-raw-neg) (poly-neg f7-poly-neg) (poly-sub f7-poly-sub)
         (raw-scale f7-raw-scale) (poly-scale f7-poly-scale)
         (raw-mul f7-raw-mul) (poly-mul f7-poly-mul)
         (const f7-const) (polynomial-one f7-polynomial-one)
         (zero-prefix f7-zero-prefix) (poly-shift f7-poly-shift)
         (monomial f7-monomial) (poly-degree f7-poly-degree)
         (poly-leading-coefficient f7-poly-leading-coefficient)
         (poly-division-step-core f7-poly-division-step-core)
         (poly-division-step f7-poly-division-step)
         (poly-division-step-term f7-poly-division-step-term)
         (poly-division-step-next f7-poly-division-step-next)
         (poly-divmod-core f7-poly-divmod-core) (poly-divmod f7-poly-divmod)
         (poly-remainder f7-poly-remainder)
         (poly-euclidean-gcd f7-poly-euclidean-gcd)
         (poly-extended-euclidean-gcd f7-poly-extended-euclidean-gcd)))))

(defthm f7-poly-extended-euclidean-gcd-bezout
  (equal
   (f7-poly-add
    (f7-poly-mul
     (mv-nth 1 (f7-poly-extended-euclidean-gcd first second)) first)
    (f7-poly-mul
     (mv-nth 2 (f7-poly-extended-euclidean-gcd first second)) second))
   (mv-nth 0 (f7-poly-extended-euclidean-gcd first second)))

  :hints (("Goal" :by (:functional-instance
                        poly-extended-euclidean-gcd-bezout
         (gfield::field-element-p gfield::f7-element-p)
         (gfield::field-fix gfield::f7-fix) (gfield::field-zero gfield::f7-zero)
         (gfield::field-one gfield::f7-one) (gfield::field-add gfield::f7-add)
         (gfield::field-mul gfield::f7-mul) (gfield::field-neg gfield::f7-neg)
         (gfield::field-inv gfield::f7-inv) (gfield::field-div gfield::f7-div)
         (fix-coefficients f7-fix-coefficients)
         (trim-trailing-zeros f7-trim-trailing-zeros) (normalize f7-normalize)
         (coefficient-list-p f7-coefficient-list-p)
         (polynomial-p f7-polynomial-p)
         (canonical-polynomial-p f7-canonical-polynomial-p)
         (raw-add f7-raw-add) (poly-add f7-poly-add)
         (raw-neg f7-raw-neg) (poly-neg f7-poly-neg) (poly-sub f7-poly-sub)
         (raw-scale f7-raw-scale) (poly-scale f7-poly-scale)
         (raw-mul f7-raw-mul) (poly-mul f7-poly-mul)
         (const f7-const) (polynomial-one f7-polynomial-one)
         (zero-prefix f7-zero-prefix) (poly-shift f7-poly-shift)
         (monomial f7-monomial) (poly-degree f7-poly-degree)
         (poly-leading-coefficient f7-poly-leading-coefficient)
         (poly-division-step-core f7-poly-division-step-core)
         (poly-division-step f7-poly-division-step)
         (poly-division-step-term f7-poly-division-step-term)
         (poly-division-step-next f7-poly-division-step-next)
         (poly-divmod-core f7-poly-divmod-core) (poly-divmod f7-poly-divmod)
         (poly-remainder f7-poly-remainder)
         (poly-euclidean-gcd f7-poly-euclidean-gcd)
         (poly-extended-euclidean-gcd f7-poly-extended-euclidean-gcd)))))

; Focused exact-value raw-XGCD regressions.  Each event records the full
; triple, all projections, both Bezout products, their sum, and the raw GCD.
(assert-event
 (mv-let (g s tt) (f7-poly-extended-euclidean-gcd '(1 2 1) '(2 3 1))
   (and
        (equal g '(6 6)) (equal s '(1)) (equal tt '(6))
        (equal g (f7-poly-euclidean-gcd '(1 2 1) '(2 3 1)))
        (f7-canonical-polynomial-p g)
        (f7-canonical-polynomial-p s)
        (f7-canonical-polynomial-p tt)
        (equal (f7-poly-mul s '(1 2 1)) '(1 2 1))
        (equal (f7-poly-mul tt '(2 3 1)) '(5 4 6))
        (equal (f7-poly-add '(1 2 1) '(5 4 6)) '(6 6))
        (equal (f7-poly-add (f7-poly-mul s '(1 2 1))
                            (f7-poly-mul tt '(2 3 1)))
               g))))
(assert-event
 (mv-let (g s tt) (f7-poly-extended-euclidean-gcd '(2 3 1) '(1 2 1))
   (and
        (equal g '(1 1)) (equal s '(1)) (equal tt '(6))
        (equal g (f7-poly-euclidean-gcd '(2 3 1) '(1 2 1)))
        (f7-canonical-polynomial-p g)
        (f7-canonical-polynomial-p s)
        (f7-canonical-polynomial-p tt)
        (equal (f7-poly-mul s '(2 3 1)) '(2 3 1))
        (equal (f7-poly-mul tt '(1 2 1)) '(6 5 6))
        (equal (f7-poly-add '(2 3 1) '(6 5 6)) '(1 1))
        (equal (f7-poly-add (f7-poly-mul s '(2 3 1))
                            (f7-poly-mul tt '(1 2 1)))
               g))))
(assert-event
 (mv-let (g s tt) (f7-poly-extended-euclidean-gcd '(1 0 1) '(1 1))
   (and
        (equal g '(2)) (equal s '(1)) (equal tt '(1 6))
        (equal g (f7-poly-euclidean-gcd '(1 0 1) '(1 1)))
        (f7-canonical-polynomial-p g)
        (f7-canonical-polynomial-p s)
        (f7-canonical-polynomial-p tt)
        (equal (f7-poly-mul s '(1 0 1)) '(1 0 1))
        (equal (f7-poly-mul tt '(1 1)) '(1 0 6))
        (equal (f7-poly-add '(1 0 1) '(1 0 6)) '(2))
        (equal (f7-poly-add (f7-poly-mul s '(1 0 1))
                            (f7-poly-mul tt '(1 1)))
               g))))
(assert-event
 (mv-let (g s tt) (f7-poly-extended-euclidean-gcd '(1 2 1) '(1 1))
   (and
        (equal g '(1 1)) (equal s nil) (equal tt '(1))
        (equal g (f7-poly-euclidean-gcd '(1 2 1) '(1 1)))
        (f7-canonical-polynomial-p g)
        (f7-canonical-polynomial-p s)
        (f7-canonical-polynomial-p tt)
        (equal (f7-poly-mul s '(1 2 1)) nil)
        (equal (f7-poly-mul tt '(1 1)) '(1 1))
        (equal (f7-poly-add nil '(1 1)) '(1 1))
        (equal (f7-poly-add (f7-poly-mul s '(1 2 1))
                            (f7-poly-mul tt '(1 1)))
               g))))
(assert-event
 (mv-let (g s tt) (f7-poly-extended-euclidean-gcd '(1 0 0 0 1) '(1 1 1))
   (and
        (equal g '(1)) (equal s '(0 6)) (equal tt '(1 0 6 1))
        (equal g (f7-poly-euclidean-gcd '(1 0 0 0 1) '(1 1 1)))
        (f7-canonical-polynomial-p g)
        (f7-canonical-polynomial-p s)
        (f7-canonical-polynomial-p tt)
        (equal (f7-poly-mul s '(1 0 0 0 1)) '(0 6 0 0 0 6))
        (equal (f7-poly-mul tt '(1 1 1)) '(1 1 0 0 0 1))
        (equal (f7-poly-add '(0 6 0 0 0 6) '(1 1 0 0 0 1)) '(1))
        (equal (f7-poly-add (f7-poly-mul s '(1 0 0 0 1))
                            (f7-poly-mul tt '(1 1 1)))
               g))))
(assert-event
 (mv-let (g s tt) (f7-poly-extended-euclidean-gcd '(2 3) nil)
   (and
        (equal g '(2 3)) (equal s '(1)) (equal tt nil)
        (equal g (f7-poly-euclidean-gcd '(2 3) nil))
        (f7-canonical-polynomial-p g)
        (f7-canonical-polynomial-p s)
        (f7-canonical-polynomial-p tt)
        (equal (f7-poly-mul s '(2 3)) '(2 3))
        (equal (f7-poly-mul tt nil) nil)
        (equal (f7-poly-add '(2 3) nil) '(2 3))
        (equal (f7-poly-add (f7-poly-mul s '(2 3))
                            (f7-poly-mul tt nil))
               g))))
(assert-event
 (mv-let (g s tt) (f7-poly-extended-euclidean-gcd nil '(2 3))
   (and
        (equal g '(2 3)) (equal s nil) (equal tt '(1))
        (equal g (f7-poly-euclidean-gcd nil '(2 3)))
        (f7-canonical-polynomial-p g)
        (f7-canonical-polynomial-p s)
        (f7-canonical-polynomial-p tt)
        (equal (f7-poly-mul s nil) nil)
        (equal (f7-poly-mul tt '(2 3)) '(2 3))
        (equal (f7-poly-add nil '(2 3)) '(2 3))
        (equal (f7-poly-add (f7-poly-mul s nil)
                            (f7-poly-mul tt '(2 3)))
               g))))
(assert-event
 (mv-let (g s tt) (f7-poly-extended-euclidean-gcd nil nil)
   (and
        (equal g nil) (equal s '(1)) (equal tt nil)
        (equal g (f7-poly-euclidean-gcd nil nil))
        (f7-canonical-polynomial-p g)
        (f7-canonical-polynomial-p s)
        (f7-canonical-polynomial-p tt)
        (equal (f7-poly-mul s nil) nil)
        (equal (f7-poly-mul tt nil) nil)
        (equal (f7-poly-add nil nil) nil)
        (equal (f7-poly-add (f7-poly-mul s nil)
                            (f7-poly-mul tt nil))
               g))))
(assert-event
 (mv-let (g s tt) (f7-poly-extended-euclidean-gcd '(3) '(5))
   (and
        (equal g '(5)) (equal s nil) (equal tt '(1))
        (equal g (f7-poly-euclidean-gcd '(3) '(5)))
        (f7-canonical-polynomial-p g)
        (f7-canonical-polynomial-p s)
        (f7-canonical-polynomial-p tt)
        (equal (f7-poly-mul s '(3)) nil)
        (equal (f7-poly-mul tt '(5)) '(5))
        (equal (f7-poly-add nil '(5)) '(5))
        (equal (f7-poly-add (f7-poly-mul s '(3))
                            (f7-poly-mul tt '(5)))
               g))))
(assert-event
 (mv-let (g s tt) (f7-poly-extended-euclidean-gcd '(2 4) '(3 6))
   (and
        (equal g '(3 6)) (equal s nil) (equal tt '(1))
        (equal g (f7-poly-euclidean-gcd '(2 4) '(3 6)))
        (f7-canonical-polynomial-p g)
        (f7-canonical-polynomial-p s)
        (f7-canonical-polynomial-p tt)
        (equal (f7-poly-mul s '(2 4)) nil)
        (equal (f7-poly-mul tt '(3 6)) '(3 6))
        (equal (f7-poly-add nil '(3 6)) '(3 6))
        (equal (f7-poly-add (f7-poly-mul s '(2 4))
                            (f7-poly-mul tt '(3 6)))
               g))))
(assert-event
 (mv-let (g s tt) (f7-poly-extended-euclidean-gcd '(3 6) '(2 4))
   (and
        (equal g '(2 4)) (equal s nil) (equal tt '(1))
        (equal g (f7-poly-euclidean-gcd '(3 6) '(2 4)))
        (f7-canonical-polynomial-p g)
        (f7-canonical-polynomial-p s)
        (f7-canonical-polynomial-p tt)
        (equal (f7-poly-mul s '(3 6)) nil)
        (equal (f7-poly-mul tt '(2 4)) '(2 4))
        (equal (f7-poly-add nil '(2 4)) '(2 4))
        (equal (f7-poly-add (f7-poly-mul s '(3 6))
                            (f7-poly-mul tt '(2 4)))
               g))))
(assert-event
 (mv-let (g s tt) (f7-poly-extended-euclidean-gcd '(1 2 1 0 0) '(2 3 1 0))
   (and
        (equal g '(6 6)) (equal s '(1)) (equal tt '(6))
        (equal g (f7-poly-euclidean-gcd '(1 2 1 0 0) '(2 3 1 0)))
        (f7-canonical-polynomial-p g)
        (f7-canonical-polynomial-p s)
        (f7-canonical-polynomial-p tt)
        (equal (f7-poly-mul s '(1 2 1 0 0)) '(1 2 1))
        (equal (f7-poly-mul tt '(2 3 1 0)) '(5 4 6))
        (equal (f7-poly-add '(1 2 1) '(5 4 6)) '(6 6))
        (equal (f7-poly-add (f7-poly-mul s '(1 2 1 0 0))
                            (f7-poly-mul tt '(2 3 1 0)))
               g))))
(assert-event
 (mv-let (g s tt) (f7-poly-extended-euclidean-gcd '(8 -5 8) '(9 -4 8))
   (and
        (equal g '(6 6)) (equal s '(1)) (equal tt '(6))
        (equal g (f7-poly-euclidean-gcd '(8 -5 8) '(9 -4 8)))
        (f7-canonical-polynomial-p g)
        (f7-canonical-polynomial-p s)
        (f7-canonical-polynomial-p tt)
        (equal (f7-poly-mul s '(8 -5 8)) '(1 2 1))
        (equal (f7-poly-mul tt '(9 -4 8)) '(5 4 6))
        (equal (f7-poly-add '(1 2 1) '(5 4 6)) '(6 6))
        (equal (f7-poly-add (f7-poly-mul s '(8 -5 8))
                            (f7-poly-mul tt '(9 -4 8)))
               g))))
(assert-event
 (mv-let (g s tt) (f7-poly-extended-euclidean-gcd 'bad '(2 3))
   (and
        (equal g '(2 3)) (equal s nil) (equal tt '(1))
        (equal g (f7-poly-euclidean-gcd 'bad '(2 3)))
        (f7-canonical-polynomial-p g)
        (f7-canonical-polynomial-p s)
        (f7-canonical-polynomial-p tt)
        (equal (f7-poly-mul s 'bad) nil)
        (equal (f7-poly-mul tt '(2 3)) '(2 3))
        (equal (f7-poly-add nil '(2 3)) '(2 3))
        (equal (f7-poly-add (f7-poly-mul s 'bad)
                            (f7-poly-mul tt '(2 3)))
               g))))
(assert-event
 (mv-let (g s tt) (f7-poly-extended-euclidean-gcd '(1 2 . bad) '(2 4 . tail))
   (and
        (equal g '(2 4)) (equal s nil) (equal tt '(1))
        (equal g (f7-poly-euclidean-gcd '(1 2 . bad) '(2 4 . tail)))
        (f7-canonical-polynomial-p g)
        (f7-canonical-polynomial-p s)
        (f7-canonical-polynomial-p tt)
        (equal (f7-poly-mul s '(1 2 . bad)) nil)
        (equal (f7-poly-mul tt '(2 4 . tail)) '(2 4))
        (equal (f7-poly-add nil '(2 4)) '(2 4))
        (equal (f7-poly-add (f7-poly-mul s '(1 2 . bad))
                            (f7-poly-mul tt '(2 4 . tail)))
               g))))

; Exact raw representatives are intentional: reversed inputs and scalar
; associates need not return equal (or monic) polynomials.
(assert-event (equal (f7-poly-euclidean-gcd '(1 2 1) '(2 3 1)) '(6 6)))
(assert-event (equal (f7-poly-euclidean-gcd '(2 3 1) '(1 2 1)) '(1 1)))
(assert-event (equal (f7-poly-euclidean-gcd '(1 0 1) '(1 1)) '(2)))
(assert-event (equal (f7-poly-euclidean-gcd '(1 2 1) '(1 1)) '(1 1)))
(assert-event
 (equal (f7-poly-euclidean-gcd '(1 0 0 0 1) '(1 1 1)) '(1)))
(assert-event (equal (f7-poly-euclidean-gcd '(2 3) nil) '(2 3)))
(assert-event (equal (f7-poly-euclidean-gcd nil '(2 3)) '(2 3)))
(assert-event (equal (f7-poly-euclidean-gcd nil nil) nil))
(assert-event (equal (f7-poly-euclidean-gcd '(3) '(5)) '(5)))
(assert-event (equal (f7-poly-euclidean-gcd '(2 4) '(3 6)) '(3 6)))
(assert-event (equal (f7-poly-euclidean-gcd '(3 6) '(2 4)) '(2 4)))
(assert-event
 (equal (f7-poly-euclidean-gcd '(1 2 1 0 0) '(2 3 1 0)) '(6 6)))
(assert-event
 (equal (f7-poly-euclidean-gcd '(8 -5 8) '(9 -4 8)) '(6 6)))
(assert-event (equal (f7-poly-euclidean-gcd 'bad '(2 3)) '(2 3)))
(assert-event
 (equal (f7-poly-euclidean-gcd '(1 2 . bad) '(2 4 . tail)) '(2 4)))
(assert-event
 (and (f7-canonical-polynomial-p
       (f7-poly-euclidean-gcd '(1 2 1) '(2 3 1)))
      (f7-poly-divides-p
       (f7-poly-euclidean-gcd '(1 2 1) '(2 3 1)) '(1 2 1))
      (f7-poly-divides-p
       (f7-poly-euclidean-gcd '(1 2 1) '(2 3 1)) '(2 3 1))
      (f7-poly-common-divisor-p '(1 1) '(1 2 1) '(2 3 1))
      (f7-poly-divides-p
       '(1 1) (f7-poly-euclidean-gcd '(1 2 1) '(2 3 1)))))

; This is the monic post-processing event from DEF-EUCLIDEAN-GCD-INSTANCE,
; expanded alone because invoking that generator would redefine the retained
; and already-certified raw recursion above.
(defun f7-poly-monic-euclidean-gcd (first second)
  (f7-poly-monic-normalize (f7-poly-euclidean-gcd first second)))

(verify-guards f7-poly-monic-euclidean-gcd)

(defthm f7-poly-monic-euclidean-gcd-is-monic-normalize
  (equal (f7-poly-monic-euclidean-gcd first second)
         (f7-poly-monic-normalize
          (f7-poly-euclidean-gcd first second))))

(defthm f7-canonical-polynomial-p-of-poly-monic-euclidean-gcd
  (f7-canonical-polynomial-p
   (f7-poly-monic-euclidean-gcd first second))
  :hints (("Goal" :in-theory (enable f7-poly-monic-euclidean-gcd
                                      f7-poly-monic-normalize))))

(defthm f7-normalize-of-poly-monic-euclidean-gcd
  (equal (f7-normalize (f7-poly-monic-euclidean-gcd first second))
         (f7-poly-monic-euclidean-gcd first second))
  :hints (("Goal"
           :use ((:instance f7-normalize-when-canonical
                            (xs (f7-poly-monic-euclidean-gcd first second)))
                 (:instance
                  f7-canonical-polynomial-p-of-poly-monic-euclidean-gcd))
           :in-theory (disable f7-normalize
                               f7-poly-monic-euclidean-gcd))))

(defthm f7-consp-of-poly-monic-normalize
  (equal (consp (f7-poly-monic-normalize poly))
         (consp (f7-normalize poly)))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
    consp-of-poly-monic-normalize
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
    (raw-scale f7-raw-scale) (poly-scale f7-poly-scale)
    (poly-leading-coefficient f7-poly-leading-coefficient)
    (poly-monic-normalize f7-poly-monic-normalize)))))

(defthm f7-poly-leading-coefficient-of-poly-monic-normalize
  (equal (f7-poly-leading-coefficient (f7-poly-monic-normalize poly))
         (if (consp (f7-normalize poly))
             (gfield::f7-one) (gfield::f7-zero)))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
    poly-leading-coefficient-of-poly-monic-normalize
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
    (raw-scale f7-raw-scale) (poly-scale f7-poly-scale)
    (poly-leading-coefficient f7-poly-leading-coefficient)
    (poly-monic-normalize f7-poly-monic-normalize)))))

(defthm f7-consp-of-poly-monic-euclidean-gcd
  (equal (consp (f7-poly-monic-euclidean-gcd first second))
         (consp (f7-normalize (f7-poly-euclidean-gcd first second))))
  :hints (("Goal"
           :use ((:instance f7-consp-of-poly-monic-normalize
                            (poly (f7-poly-euclidean-gcd first second))))
           :in-theory (enable f7-poly-monic-euclidean-gcd))))

(defthm f7-poly-leading-coefficient-of-poly-monic-euclidean-gcd
  (equal (f7-poly-leading-coefficient
          (f7-poly-monic-euclidean-gcd first second))
         (if (consp (f7-normalize
                     (f7-poly-euclidean-gcd first second)))
             (gfield::f7-one)
           (gfield::f7-zero)))
  :hints (("Goal"
           :use ((:instance
                  f7-poly-leading-coefficient-of-poly-monic-normalize
                  (poly (f7-poly-euclidean-gcd first second))))
           :in-theory (enable f7-poly-monic-euclidean-gcd))))

; Correctness uses only the retained raw package and the two previously
; certified monic-normalization/divisibility transport equivalences.
(defthm f7-poly-monic-euclidean-gcd-divides-first
  (f7-poly-divides-p
   (f7-poly-monic-euclidean-gcd first second) first)
  :hints (("Goal"
           :use ((:instance f7-poly-euclidean-gcd-divides-first)
                 (:instance f7-poly-divides-p-of-poly-monic-normalize-divisor
                            (divisor (f7-poly-euclidean-gcd first second))
                            (dividend first)))
           :in-theory (enable
                       f7-poly-monic-euclidean-gcd-is-monic-normalize))))

(defthm f7-poly-monic-euclidean-gcd-divides-second
  (f7-poly-divides-p
   (f7-poly-monic-euclidean-gcd first second) second)
  :hints (("Goal"
           :use ((:instance f7-poly-euclidean-gcd-divides-second)
                 (:instance f7-poly-divides-p-of-poly-monic-normalize-divisor
                            (divisor (f7-poly-euclidean-gcd first second))
                            (dividend second)))
           :in-theory (enable
                       f7-poly-monic-euclidean-gcd-is-monic-normalize))))

(defthm f7-poly-common-divisor-p-of-poly-monic-euclidean-gcd
  (f7-poly-common-divisor-p
   (f7-poly-monic-euclidean-gcd first second) first second)
  :hints (("Goal"
           :use ((:instance f7-poly-monic-euclidean-gcd-divides-first)
                 (:instance f7-poly-monic-euclidean-gcd-divides-second))
           :in-theory (enable f7-poly-common-divisor-p))))

(defthm f7-poly-divides-p-of-poly-monic-euclidean-gcd
  (implies (f7-poly-common-divisor-p common first second)
           (f7-poly-divides-p
            common (f7-poly-monic-euclidean-gcd first second)))
  :hints (("Goal"
           :use ((:instance f7-poly-common-divisor-divides-euclidean-gcd
                            (divisor common))
                 (:instance f7-poly-divides-p-of-poly-monic-normalize-dividend
                            (divisor common)
                            (dividend
                             (f7-poly-euclidean-gcd first second))))
           :in-theory (enable
                       f7-poly-monic-euclidean-gcd-is-monic-normalize))))

(defthm f7-poly-monic-euclidean-gcd-correct
  (and (f7-poly-common-divisor-p
        (f7-poly-monic-euclidean-gcd first second) first second)
       (implies (f7-poly-common-divisor-p common first second)
                (f7-poly-divides-p
                 common (f7-poly-monic-euclidean-gcd first second))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  f7-poly-common-divisor-p-of-poly-monic-euclidean-gcd)
                 (:instance f7-poly-divides-p-of-poly-monic-euclidean-gcd))
           :in-theory (disable f7-poly-common-divisor-p f7-poly-divides-p
                               f7-poly-monic-euclidean-gcd))))

; Focused exact ordinary-execution regressions for the transparent wrapper.
(assert-event (equal (f7-poly-monic-euclidean-gcd '(1 2 1) '(2 3 1)) '(1 1)))
(assert-event (equal (f7-poly-monic-euclidean-gcd '(2 3 1) '(1 2 1)) '(1 1)))
(assert-event (equal (f7-poly-monic-euclidean-gcd '(1 0 1) '(1 1)) '(1)))
(assert-event (equal (f7-poly-monic-euclidean-gcd '(1 2 1) '(1 1)) '(1 1)))
(assert-event
 (equal (f7-poly-monic-euclidean-gcd '(1 0 0 0 1) '(1 1 1)) '(1)))
(assert-event (equal (f7-poly-monic-euclidean-gcd '(2 3) nil) '(3 1)))
(assert-event (equal (f7-poly-monic-euclidean-gcd nil '(2 3)) '(3 1)))
(assert-event (equal (f7-poly-monic-euclidean-gcd nil nil) nil))
(assert-event (equal (f7-poly-monic-euclidean-gcd '(3) '(5)) '(1)))
(assert-event (equal (f7-poly-monic-euclidean-gcd '(2 4) '(3 6)) '(4 1)))
(assert-event (equal (f7-poly-monic-euclidean-gcd '(3 6) '(2 4)) '(4 1)))
(assert-event
 (equal (f7-poly-monic-euclidean-gcd '(1 2 1 0 0) '(2 3 1 0)) '(1 1)))
(assert-event
 (equal (f7-poly-monic-euclidean-gcd '(8 -5 8) '(9 -4 8)) '(1 1)))
(assert-event (equal (f7-poly-monic-euclidean-gcd 'bad '(2 3)) '(3 1)))
(assert-event
 (equal (f7-poly-monic-euclidean-gcd '(1 2 . bad) '(2 4 . tail)) '(4 1)))
(assert-event
 (let ((g (f7-poly-monic-euclidean-gcd '(1 2 1) '(2 3 1))))
   (and (equal g (f7-poly-monic-normalize
                  (f7-poly-euclidean-gcd '(1 2 1) '(2 3 1))))
        (f7-canonical-polynomial-p g)
        (equal (f7-normalize g) g)
        (f7-poly-divides-p g '(1 2 1))
        (f7-poly-divides-p g '(2 3 1))
        (implies (f7-poly-common-divisor-p '(1 1) '(1 2 1) '(2 3 1))
                 (f7-poly-divides-p '(1 1) g))
        (equal (f7-poly-leading-coefficient g) (gfield::f7-one)))))

; Transparent monic post-processing of the retained raw XGCD.  This matches
; POLY-MONIC-EXTENDED-EUCLIDEAN-GCD literally: in particular, inverse zero
; uniformly scales the raw zero-gcd coefficients to NIL.
(defund f7-poly-monic-extended-euclidean-gcd (first second)
  (declare (xargs :guard t))
  (mv-let (gcd s coefficient-t)
    (f7-poly-extended-euclidean-gcd first second)
    (let ((scale (gfield::f7-inv (f7-poly-leading-coefficient gcd))))
      (mv (f7-poly-monic-normalize gcd)
          (f7-poly-scale scale s)
          (f7-poly-scale scale coefficient-t)))))

(verify-guards f7-poly-monic-extended-euclidean-gcd)

(defthm f7-poly-monic-extended-euclidean-gcd-is-scaled-xgcd
  (equal
   (f7-poly-monic-extended-euclidean-gcd first second)
   (mv-let (gcd s coefficient-t)
     (f7-poly-extended-euclidean-gcd first second)
     (let ((scale (gfield::f7-inv (f7-poly-leading-coefficient gcd))))
       (mv (f7-poly-monic-normalize gcd)
           (f7-poly-scale scale s)
           (f7-poly-scale scale coefficient-t)))))
  :hints (("Goal" :in-theory (enable
                               f7-poly-monic-extended-euclidean-gcd))))

(defthm f7-poly-monic-extended-euclidean-gcd-gcd-is-monic-euclidean-gcd
  (equal (mv-nth 0 (f7-poly-monic-extended-euclidean-gcd first second))
         (f7-poly-monic-euclidean-gcd first second))
  :hints (("Goal"
           :use ((:instance
                  f7-poly-extended-euclidean-gcd-gcd-is-f7-poly-euclidean-gcd))
           :in-theory (enable f7-poly-monic-extended-euclidean-gcd
                              f7-poly-monic-euclidean-gcd))))

(defthm f7-poly-monic-extended-euclidean-gcd-gcd-canonical
  (f7-canonical-polynomial-p
   (mv-nth 0 (f7-poly-monic-extended-euclidean-gcd first second)))
  :hints (("Goal"
           :use ((:instance
                  f7-canonical-polynomial-p-of-poly-monic-euclidean-gcd))
           :in-theory (disable f7-poly-monic-extended-euclidean-gcd))))

(defthm f7-poly-monic-extended-euclidean-gcd-first-coefficient-canonical
  (f7-canonical-polynomial-p
   (mv-nth 1 (f7-poly-monic-extended-euclidean-gcd first second)))
  :hints (("Goal"
           :in-theory (enable f7-poly-monic-extended-euclidean-gcd
                              f7-poly-scale))))

(defthm f7-poly-monic-extended-euclidean-gcd-second-coefficient-canonical
  (f7-canonical-polynomial-p
   (mv-nth 2 (f7-poly-monic-extended-euclidean-gcd first second)))
  :hints (("Goal"
           :in-theory (enable f7-poly-monic-extended-euclidean-gcd
                              f7-poly-scale))))

(defthm f7-normalize-of-poly-monic-extended-euclidean-gcd-gcd
  (equal (f7-normalize
          (mv-nth 0 (f7-poly-monic-extended-euclidean-gcd first second)))
         (mv-nth 0 (f7-poly-monic-extended-euclidean-gcd first second)))
  :hints (("Goal" :use ((:instance
                          f7-poly-monic-extended-euclidean-gcd-gcd-canonical)))))

(defthm f7-normalize-of-poly-monic-extended-euclidean-gcd-first-coefficient
  (equal (f7-normalize
          (mv-nth 1 (f7-poly-monic-extended-euclidean-gcd first second)))
         (mv-nth 1 (f7-poly-monic-extended-euclidean-gcd first second)))
  :hints (("Goal" :use ((:instance
                          f7-poly-monic-extended-euclidean-gcd-first-coefficient-canonical)))))

(defthm f7-normalize-of-poly-monic-extended-euclidean-gcd-second-coefficient
  (equal (f7-normalize
          (mv-nth 2 (f7-poly-monic-extended-euclidean-gcd first second)))
         (mv-nth 2 (f7-poly-monic-extended-euclidean-gcd first second)))
  :hints (("Goal" :use ((:instance
                          f7-poly-monic-extended-euclidean-gcd-second-coefficient-canonical)))))

(defthm f7-poly-monic-extended-euclidean-gcd-bezout
  (equal
   (f7-poly-add
    (f7-poly-mul
     (mv-nth 1 (f7-poly-monic-extended-euclidean-gcd first second)) first)
    (f7-poly-mul
     (mv-nth 2 (f7-poly-monic-extended-euclidean-gcd first second)) second))
   (f7-poly-monic-euclidean-gcd first second))
  :hints
  (("Goal" :by
    (:functional-instance
     poly-monic-extended-euclidean-gcd-bezout
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
     (poly-euclidean-gcd f7-poly-euclidean-gcd)
     (poly-monic-euclidean-gcd f7-poly-monic-euclidean-gcd)
     (poly-extended-euclidean-gcd f7-poly-extended-euclidean-gcd)
     (poly-monic-extended-euclidean-gcd
      f7-poly-monic-extended-euclidean-gcd)))))

(defthm f7-poly-leading-coefficient-of-monic-extended-euclidean-gcd
  (equal
   (f7-poly-leading-coefficient
    (mv-nth 0 (f7-poly-monic-extended-euclidean-gcd first second)))
   (if (consp (f7-poly-monic-euclidean-gcd first second))
       (gfield::f7-one)
     (gfield::f7-zero)))
  :hints (("Goal"
           :use ((:instance
                  f7-poly-leading-coefficient-of-poly-monic-euclidean-gcd))
           :in-theory (disable f7-poly-monic-extended-euclidean-gcd))))

(defthm f7-consp-of-monic-extended-euclidean-gcd
  (equal (consp (mv-nth 0
                        (f7-poly-monic-extended-euclidean-gcd first second)))
         (consp (f7-normalize
                 (f7-poly-euclidean-gcd first second))))
  :hints (("Goal"
           :use ((:instance f7-consp-of-poly-monic-euclidean-gcd)
                 (:instance
                  f7-poly-monic-extended-euclidean-gcd-gcd-is-monic-euclidean-gcd))
           :in-theory
           (disable f7-poly-monic-extended-euclidean-gcd
                    f7-poly-monic-extended-euclidean-gcd-is-scaled-xgcd
                    f7-poly-monic-euclidean-gcd))))





; Exact total-execution monic-XGCD regressions.  Each case retains the raw
; triple and scale, the complete monic triple and projections, and both
; scaled Bezout products and their sum.
; common
(assert-event
 (mv-let (raw-g raw-s raw-t)
    (f7-poly-extended-euclidean-gcd '(1 2 1) '(2 3 1))
    (mv-let (g s tt)
      (f7-poly-monic-extended-euclidean-gcd '(1 2 1) '(2 3 1))
      (let* ((product-s (f7-poly-mul s '(1 2 1)))
             (product-t (f7-poly-mul tt '(2 3 1)))
               (sum (f7-poly-add product-s product-t)))
          (and (equal raw-g '(6 6)) (equal raw-s '(1)) (equal raw-t '(6))
               (equal (f7-poly-leading-coefficient raw-g) 6)
               (equal (gfield::f7-inv 6) 6)
               (equal g '(1 1)) (equal s '(6)) (equal tt '(1))
               (equal product-s '(6 5 6)) (equal product-t '(2 3 1))
             (equal sum '(1 1)) (equal sum g))))))
; common-reverse
(assert-event
 (mv-let (raw-g raw-s raw-t)
    (f7-poly-extended-euclidean-gcd '(2 3 1) '(1 2 1))
    (mv-let (g s tt)
      (f7-poly-monic-extended-euclidean-gcd '(2 3 1) '(1 2 1))
      (let* ((product-s (f7-poly-mul s '(2 3 1)))
             (product-t (f7-poly-mul tt '(1 2 1)))
               (sum (f7-poly-add product-s product-t)))
          (and (equal raw-g '(1 1)) (equal raw-s '(1)) (equal raw-t '(6))
               (equal (f7-poly-leading-coefficient raw-g) 1)
               (equal (gfield::f7-inv 1) 1)
               (equal g '(1 1)) (equal s '(1)) (equal tt '(6))
               (equal product-s '(2 3 1)) (equal product-t '(6 5 6))
             (equal sum '(1 1)) (equal sum g))))))
; coprime
(assert-event
 (mv-let (raw-g raw-s raw-t)
    (f7-poly-extended-euclidean-gcd '(1 0 1) '(1 1))
    (mv-let (g s tt)
      (f7-poly-monic-extended-euclidean-gcd '(1 0 1) '(1 1))
      (let* ((product-s (f7-poly-mul s '(1 0 1)))
             (product-t (f7-poly-mul tt '(1 1)))
               (sum (f7-poly-add product-s product-t)))
          (and (equal raw-g '(2)) (equal raw-s '(1)) (equal raw-t '(1 6))
               (equal (f7-poly-leading-coefficient raw-g) 2)
               (equal (gfield::f7-inv 2) 4)
               (equal g '(1)) (equal s '(4)) (equal tt '(4 3))
               (equal product-s '(4 0 4)) (equal product-t '(4 0 3))
             (equal sum '(1)) (equal sum g))))))
; exact-divisibility
(assert-event
 (mv-let (raw-g raw-s raw-t)
    (f7-poly-extended-euclidean-gcd '(1 2 1) '(1 1))
    (mv-let (g s tt)
      (f7-poly-monic-extended-euclidean-gcd '(1 2 1) '(1 1))
      (let* ((product-s (f7-poly-mul s '(1 2 1)))
             (product-t (f7-poly-mul tt '(1 1)))
               (sum (f7-poly-add product-s product-t)))
          (and (equal raw-g '(1 1)) (equal raw-s nil) (equal raw-t '(1))
               (equal (f7-poly-leading-coefficient raw-g) 1)
               (equal (gfield::f7-inv 1) 1)
               (equal g '(1 1)) (equal s nil) (equal tt '(1))
               (equal product-s nil) (equal product-t '(1 1))
             (equal sum '(1 1)) (equal sum g))))))
; multi-step
(assert-event
 (mv-let (raw-g raw-s raw-t)
    (f7-poly-extended-euclidean-gcd '(1 0 0 0 1) '(1 1 1))
    (mv-let (g s tt)
      (f7-poly-monic-extended-euclidean-gcd '(1 0 0 0 1) '(1 1 1))
      (let* ((product-s (f7-poly-mul s '(1 0 0 0 1)))
             (product-t (f7-poly-mul tt '(1 1 1)))
               (sum (f7-poly-add product-s product-t)))
          (and (equal raw-g '(1)) (equal raw-s '(0 6)) (equal raw-t '(1 0 6 1))
               (equal (f7-poly-leading-coefficient raw-g) 1)
               (equal (gfield::f7-inv 1) 1)
               (equal g '(1)) (equal s '(0 6)) (equal tt '(1 0 6 1))
               (equal product-s '(0 6 0 0 0 6)) (equal product-t '(1 1 0 0 0 1))
             (equal sum '(1)) (equal sum g))))))
; zero-second
(assert-event
 (mv-let (raw-g raw-s raw-t)
    (f7-poly-extended-euclidean-gcd '(2 3) nil)
    (mv-let (g s tt)
      (f7-poly-monic-extended-euclidean-gcd '(2 3) nil)
      (let* ((product-s (f7-poly-mul s '(2 3)))
             (product-t (f7-poly-mul tt nil))
               (sum (f7-poly-add product-s product-t)))
          (and (equal raw-g '(2 3)) (equal raw-s '(1)) (equal raw-t nil)
               (equal (f7-poly-leading-coefficient raw-g) 3)
               (equal (gfield::f7-inv 3) 5)
               (equal g '(3 1)) (equal s '(5)) (equal tt nil)
               (equal product-s '(3 1)) (equal product-t nil)
             (equal sum '(3 1)) (equal sum g))))))
; zero-first
(assert-event
 (mv-let (raw-g raw-s raw-t)
    (f7-poly-extended-euclidean-gcd nil '(2 3))
    (mv-let (g s tt)
      (f7-poly-monic-extended-euclidean-gcd nil '(2 3))
      (let* ((product-s (f7-poly-mul s nil))
             (product-t (f7-poly-mul tt '(2 3)))
               (sum (f7-poly-add product-s product-t)))
          (and (equal raw-g '(2 3)) (equal raw-s nil) (equal raw-t '(1))
               (equal (f7-poly-leading-coefficient raw-g) 3)
               (equal (gfield::f7-inv 3) 5)
               (equal g '(3 1)) (equal s nil) (equal tt '(5))
               (equal product-s nil) (equal product-t '(3 1))
             (equal sum '(3 1)) (equal sum g))))))
; zero-zero
(assert-event
 (mv-let (raw-g raw-s raw-t)
    (f7-poly-extended-euclidean-gcd nil nil)
    (mv-let (g s tt)
      (f7-poly-monic-extended-euclidean-gcd nil nil)
      (let* ((product-s (f7-poly-mul s nil))
             (product-t (f7-poly-mul tt nil))
               (sum (f7-poly-add product-s product-t)))
          (and (equal raw-g nil) (equal raw-s '(1)) (equal raw-t nil)
               (equal (f7-poly-leading-coefficient raw-g) 0)
               (equal (gfield::f7-inv 0) 0)
               (equal g nil) (equal s nil) (equal tt nil)
               (equal product-s nil) (equal product-t nil)
             (equal sum nil) (equal sum g))))))
; constants
(assert-event
 (mv-let (raw-g raw-s raw-t)
    (f7-poly-extended-euclidean-gcd '(3) '(5))
    (mv-let (g s tt)
      (f7-poly-monic-extended-euclidean-gcd '(3) '(5))
      (let* ((product-s (f7-poly-mul s '(3)))
             (product-t (f7-poly-mul tt '(5)))
               (sum (f7-poly-add product-s product-t)))
          (and (equal raw-g '(5)) (equal raw-s nil) (equal raw-t '(1))
               (equal (f7-poly-leading-coefficient raw-g) 5)
               (equal (gfield::f7-inv 5) 3)
               (equal g '(1)) (equal s nil) (equal tt '(3))
               (equal product-s nil) (equal product-t '(1))
             (equal sum '(1)) (equal sum g))))))
; associates
(assert-event
 (mv-let (raw-g raw-s raw-t)
    (f7-poly-extended-euclidean-gcd '(2 4) '(3 6))
    (mv-let (g s tt)
      (f7-poly-monic-extended-euclidean-gcd '(2 4) '(3 6))
      (let* ((product-s (f7-poly-mul s '(2 4)))
             (product-t (f7-poly-mul tt '(3 6)))
               (sum (f7-poly-add product-s product-t)))
          (and (equal raw-g '(3 6)) (equal raw-s nil) (equal raw-t '(1))
               (equal (f7-poly-leading-coefficient raw-g) 6)
               (equal (gfield::f7-inv 6) 6)
               (equal g '(4 1)) (equal s nil) (equal tt '(6))
               (equal product-s nil) (equal product-t '(4 1))
             (equal sum '(4 1)) (equal sum g))))))
; associates-reverse
(assert-event
 (mv-let (raw-g raw-s raw-t)
    (f7-poly-extended-euclidean-gcd '(3 6) '(2 4))
    (mv-let (g s tt)
      (f7-poly-monic-extended-euclidean-gcd '(3 6) '(2 4))
      (let* ((product-s (f7-poly-mul s '(3 6)))
             (product-t (f7-poly-mul tt '(2 4)))
               (sum (f7-poly-add product-s product-t)))
          (and (equal raw-g '(2 4)) (equal raw-s nil) (equal raw-t '(1))
               (equal (f7-poly-leading-coefficient raw-g) 4)
               (equal (gfield::f7-inv 4) 2)
               (equal g '(4 1)) (equal s nil) (equal tt '(2))
               (equal product-s nil) (equal product-t '(4 1))
             (equal sum '(4 1)) (equal sum g))))))
; trailing-zeros
(assert-event
 (mv-let (raw-g raw-s raw-t)
    (f7-poly-extended-euclidean-gcd '(1 2 1 0 0) '(2 3 1 0))
    (mv-let (g s tt)
      (f7-poly-monic-extended-euclidean-gcd '(1 2 1 0 0) '(2 3 1 0))
      (let* ((product-s (f7-poly-mul s '(1 2 1 0 0)))
             (product-t (f7-poly-mul tt '(2 3 1 0)))
               (sum (f7-poly-add product-s product-t)))
          (and (equal raw-g '(6 6)) (equal raw-s '(1)) (equal raw-t '(6))
               (equal (f7-poly-leading-coefficient raw-g) 6)
               (equal (gfield::f7-inv 6) 6)
               (equal g '(1 1)) (equal s '(6)) (equal tt '(1))
               (equal product-s '(6 5 6)) (equal product-t '(2 3 1))
             (equal sum '(1 1)) (equal sum g))))))
; field-fixing
(assert-event
 (mv-let (raw-g raw-s raw-t)
    (f7-poly-extended-euclidean-gcd '(8 -5 8) '(9 -4 8))
    (mv-let (g s tt)
      (f7-poly-monic-extended-euclidean-gcd '(8 -5 8) '(9 -4 8))
      (let* ((product-s (f7-poly-mul s '(8 -5 8)))
             (product-t (f7-poly-mul tt '(9 -4 8)))
               (sum (f7-poly-add product-s product-t)))
          (and (equal raw-g '(6 6)) (equal raw-s '(1)) (equal raw-t '(6))
               (equal (f7-poly-leading-coefficient raw-g) 6)
               (equal (gfield::f7-inv 6) 6)
               (equal g '(1 1)) (equal s '(6)) (equal tt '(1))
               (equal product-s '(6 5 6)) (equal product-t '(2 3 1))
             (equal sum '(1 1)) (equal sum g))))))
; malformed-atoms
(assert-event
 (mv-let (raw-g raw-s raw-t)
    (f7-poly-extended-euclidean-gcd 'bad '(2 3))
    (mv-let (g s tt)
      (f7-poly-monic-extended-euclidean-gcd 'bad '(2 3))
      (let* ((product-s (f7-poly-mul s 'bad))
             (product-t (f7-poly-mul tt '(2 3)))
               (sum (f7-poly-add product-s product-t)))
          (and (equal raw-g '(2 3)) (equal raw-s nil) (equal raw-t '(1))
               (equal (f7-poly-leading-coefficient raw-g) 3)
               (equal (gfield::f7-inv 3) 5)
               (equal g '(3 1)) (equal s nil) (equal tt '(5))
               (equal product-s nil) (equal product-t '(3 1))
             (equal sum '(3 1)) (equal sum g))))))
; dotted-lists
(assert-event
 (mv-let (raw-g raw-s raw-t)
    (f7-poly-extended-euclidean-gcd '(1 2 . bad) '(2 4 . tail))
    (mv-let (g s tt)
      (f7-poly-monic-extended-euclidean-gcd '(1 2 . bad) '(2 4 . tail))
      (let* ((product-s (f7-poly-mul s '(1 2 . bad)))
             (product-t (f7-poly-mul tt '(2 4 . tail)))
               (sum (f7-poly-add product-s product-t)))
          (and (equal raw-g '(2 4)) (equal raw-s nil) (equal raw-t '(1))
               (equal (f7-poly-leading-coefficient raw-g) 4)
               (equal (gfield::f7-inv 4) 2)
               (equal g '(4 1)) (equal s nil) (equal tt '(2))
               (equal product-s nil) (equal product-t '(4 1))
             (equal sum '(4 1)) (equal sum g))))))

; Representative public structural checks, including the retained raw-order
; distinction and the exact nonzero hypothesis for monicity.
(assert-event
 (mv-let (forward-g forward-s forward-t)
   (f7-poly-monic-extended-euclidean-gcd '(1 2 1) '(2 3 1))
   (mv-let (reverse-g reverse-s reverse-t)
     (f7-poly-monic-extended-euclidean-gcd '(2 3 1) '(1 2 1))
     (declare (ignore reverse-s reverse-t))
     (and (equal forward-g
                 (f7-poly-monic-euclidean-gcd '(1 2 1) '(2 3 1)))
          (equal reverse-g
                 (f7-poly-monic-euclidean-gcd '(2 3 1) '(1 2 1)))
          (equal forward-g '(1 1)) (equal reverse-g '(1 1))
          (f7-canonical-polynomial-p forward-g)
          (f7-canonical-polynomial-p forward-s)
          (f7-canonical-polynomial-p forward-t)
          (equal (f7-normalize forward-g) forward-g)
          (implies (consp forward-g)
                   (equal (f7-poly-leading-coefficient forward-g)
                          (gfield::f7-one)))
          (equal (consp forward-g) t)))))

; The concrete modular inverse follows POLY-MODULAR-INVERSE literally.  It
; performs one monic-XGCD computation and reduces that computation's first
; Bezout coefficient with the retained F7 remainder operation.
(defund f7-poly-modular-inverse (first modulus)
  (declare (xargs :guard t))
  (mv-let (gcd s coefficient-t)
    (f7-poly-monic-extended-euclidean-gcd first modulus)
    (declare (ignore gcd coefficient-t))
    (f7-poly-remainder s modulus)))

(verify-guards f7-poly-modular-inverse)

(defthm f7-poly-modular-inverse-definition
  (equal (f7-poly-modular-inverse first modulus)
         (f7-poly-remainder
          (mv-nth 1
                  (f7-poly-monic-extended-euclidean-gcd first modulus))
          modulus))
  :hints (("Goal" :in-theory (enable f7-poly-modular-inverse))))

; This is the complete substitution used for the generic modular-inverse
; package.  Keeping it local avoids exporting a redundant aggregate theorem.
(local
 (defthm f7-poly-modular-inverse-correct-from-generic
   (and
    (f7-canonical-polynomial-p (f7-poly-modular-inverse first modulus))
    (equal
     (f7-poly-remainder
      (f7-poly-mul (f7-poly-modular-inverse first modulus) first) modulus)
     (f7-poly-remainder
      (f7-poly-mul
       (mv-nth 1
               (f7-poly-monic-extended-euclidean-gcd first modulus))
       first)
      modulus))
    (implies
     (equal (f7-poly-monic-euclidean-gcd first modulus)
            (f7-polynomial-one))
     (equal
      (f7-poly-remainder
       (f7-poly-mul (f7-poly-modular-inverse first modulus) first) modulus)
      (f7-poly-remainder (f7-polynomial-one) modulus))))
   :hints
   (("Goal"
     :use
     ((:functional-instance
    poly-modular-inverse-canonical
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
    (poly-euclidean-gcd f7-poly-euclidean-gcd)
    (poly-monic-euclidean-gcd f7-poly-monic-euclidean-gcd)
    (poly-extended-euclidean-gcd f7-poly-extended-euclidean-gcd)
    (poly-monic-extended-euclidean-gcd
     f7-poly-monic-extended-euclidean-gcd)
    (poly-modular-inverse f7-poly-modular-inverse))
      (:functional-instance
    poly-remainder-of-poly-mul-poly-modular-inverse
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
    (poly-euclidean-gcd f7-poly-euclidean-gcd)
    (poly-monic-euclidean-gcd f7-poly-monic-euclidean-gcd)
    (poly-extended-euclidean-gcd f7-poly-extended-euclidean-gcd)
    (poly-monic-extended-euclidean-gcd
     f7-poly-monic-extended-euclidean-gcd)
    (poly-modular-inverse f7-poly-modular-inverse))
      (:functional-instance
    poly-modular-inverse-correct
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
    (poly-euclidean-gcd f7-poly-euclidean-gcd)
    (poly-monic-euclidean-gcd f7-poly-monic-euclidean-gcd)
    (poly-extended-euclidean-gcd f7-poly-extended-euclidean-gcd)
    (poly-monic-extended-euclidean-gcd
     f7-poly-monic-extended-euclidean-gcd)
    (poly-modular-inverse f7-poly-modular-inverse)))
     :in-theory (disable f7-poly-modular-inverse
                         f7-poly-monic-extended-euclidean-gcd
                         f7-poly-remainder f7-poly-mul)))))

(defthm f7-poly-modular-inverse-canonical
  (f7-canonical-polynomial-p (f7-poly-modular-inverse first modulus))
  :hints (("Goal" :use f7-poly-modular-inverse-correct-from-generic)))

(defthm f7-normalize-of-poly-modular-inverse
  (equal (f7-normalize (f7-poly-modular-inverse first modulus))
         (f7-poly-modular-inverse first modulus))
  :hints (("Goal"
           :use ((:instance f7-normalize-when-canonical
                            (xs (f7-poly-modular-inverse first modulus)))
                 (:instance f7-poly-modular-inverse-canonical)))))

(defthm f7-poly-remainder-of-poly-mul-poly-modular-inverse
  (equal
   (f7-poly-remainder
    (f7-poly-mul (f7-poly-modular-inverse first modulus) first) modulus)
   (f7-poly-remainder
    (f7-poly-mul
     (mv-nth 1 (f7-poly-monic-extended-euclidean-gcd first modulus)) first)
    modulus))
  :hints (("Goal" :use f7-poly-modular-inverse-correct-from-generic)))

(defthm f7-poly-modular-inverse-correct
  (implies
   (equal (f7-poly-monic-euclidean-gcd first modulus)
          (f7-polynomial-one))
   (equal
    (f7-poly-remainder
     (f7-poly-mul (f7-poly-modular-inverse first modulus) first) modulus)
    (f7-poly-remainder (f7-polynomial-one) modulus)))
  :hints (("Goal" :use f7-poly-modular-inverse-correct-from-generic)))

(defthm f7-poly-modular-inverse-remainder-one
  (implies
   (and (equal (f7-poly-monic-euclidean-gcd first modulus)
               (f7-polynomial-one))
        (consp (f7-normalize modulus))
        (< 0 (f7-poly-degree (f7-normalize modulus))))
   (equal
    (f7-poly-remainder
     (f7-poly-mul (f7-poly-modular-inverse first modulus) first) modulus)
    (f7-polynomial-one)))
  :hints
  (("Goal"
    :use ((:instance f7-poly-modular-inverse-correct)
          (:functional-instance
    poly-remainder-of-polynomial-one-when-positive-degree
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
    (poly-euclidean-gcd f7-poly-euclidean-gcd)
    (poly-monic-euclidean-gcd f7-poly-monic-euclidean-gcd)
    (poly-extended-euclidean-gcd f7-poly-extended-euclidean-gcd)
    (poly-monic-extended-euclidean-gcd
     f7-poly-monic-extended-euclidean-gcd)
    (poly-modular-inverse f7-poly-modular-inverse)))
    :in-theory (disable f7-poly-modular-inverse f7-poly-remainder
                        f7-poly-mul f7-polynomial-one f7-normalize
                        f7-poly-degree f7-poly-monic-euclidean-gcd))))

; Exact total executions cover successful units, non-units, degenerate
; moduli, fixed coefficients, and malformed list representations.
(assert-event
 (and
  (equal (f7-poly-modular-inverse '(1 0 0 0 1) '(1 1 1)) '(0 6))
  (equal (f7-poly-modular-inverse '(1) '(1 1 1)) '(1))
  (equal (f7-poly-modular-inverse '(3) '(1 1 1)) '(5))
  (equal (f7-poly-modular-inverse '(1 0 1) '(1 1)) '(4))
  (equal (f7-poly-modular-inverse '(1 2 1) '(1 1)) nil)
  (equal (f7-poly-modular-inverse nil '(1 1)) nil)
  (equal (f7-poly-modular-inverse '(2 3) nil) '(5))
  (equal (f7-poly-modular-inverse nil nil) nil)
  (equal (f7-poly-modular-inverse '(1 1) '(1)) nil)
  (equal (f7-poly-modular-inverse '(2 0 2) '(2 2)) '(2))
  (equal (f7-poly-modular-inverse '(1 0 1 0 0) '(1 1 0)) '(4))
  (equal (f7-poly-modular-inverse '(8 -7 8) '(8 8)) '(4))
  (equal (f7-poly-modular-inverse 'bad 'modulus) nil)
  (equal (f7-poly-modular-inverse '(1 0 1 . bad) '(1 1 . tail)) '(4))))

(assert-event
 (let* ((first '(1 0 0 0 1))
        (modulus '(1 1 1)))
   (mv-let (g s tt)
     (f7-poly-monic-extended-euclidean-gcd first modulus)
     (let* ((inverse (f7-poly-modular-inverse first modulus))
            (product (f7-poly-mul first inverse))
            (remainder (f7-poly-remainder product modulus)))
       (and (equal g '(1)) (equal s '(0 6))
            (equal tt '(1 0 6 1))
            (equal inverse s)
            (equal product '(0 6 0 0 0 6))
            (equal remainder '(1))
            (equal remainder (f7-polynomial-one))
            (f7-canonical-polynomial-p inverse)
            (equal (f7-normalize inverse) inverse))))))

(assert-event
 (mv-let (g s tt)
   (f7-poly-monic-extended-euclidean-gcd '(1 2 1) '(1 1))
   (declare (ignore s tt))
   (and (equal g '(1 1))
        (equal (f7-poly-modular-inverse '(1 2 1) '(1 1)) nil)
        (not (equal (f7-poly-monic-euclidean-gcd '(1 2 1) '(1 1))
                    (f7-polynomial-one))))))
