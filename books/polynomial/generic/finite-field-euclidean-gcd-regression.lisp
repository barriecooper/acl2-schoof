(in-package "GPOLY")

(include-book "finite-field-euclidean-gcd")

; Every regression uses only named public theorems over MINIMAL-THEORY.  In
; particular, none opens gcd recursion, divmod, remainder, normalization, or
; the divisibility predicate.
(defthm finite-field-euclidean-gcd-regression-normalized-zero-equation
  (implies (not (consp (finite-field-poly-normalize second)))
           (equal (finite-field-poly-euclidean-gcd first second)
                  (finite-field-poly-normalize first)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-euclidean-gcd-zero-second))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-euclidean-gcd-regression-both-zero
  (finite-field-poly-common-divisor-p
   (finite-field-poly-euclidean-gcd nil nil) nil nil)
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-common-divisor-p-of-euclidean-gcd
                            (first nil) (second nil)))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-euclidean-gcd-regression-one-zero-input
  (and
   (finite-field-poly-common-divisor-p
    (finite-field-poly-euclidean-gcd first nil) first nil)
   (finite-field-poly-common-divisor-p
    (finite-field-poly-euclidean-gcd nil second) nil second))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-common-divisor-p-of-euclidean-gcd
                            (second nil))
                 (:instance finite-field-poly-common-divisor-p-of-euclidean-gcd
                            (first nil)))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-euclidean-gcd-regression-exact-multiple
  (finite-field-poly-common-divisor-p
   (finite-field-poly-euclidean-gcd
    (finite-field-poly-mul multiplier divisor) divisor)
   (finite-field-poly-mul multiplier divisor)
   divisor)
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-common-divisor-p-of-euclidean-gcd
                            (first (finite-field-poly-mul multiplier divisor))
                            (second divisor)))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-euclidean-gcd-regression-zero-first-remainder
  (implies
   (equal (finite-field-poly-remainder first second) nil)
   (finite-field-poly-common-divisor-p
    (finite-field-poly-euclidean-gcd first second) first second))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-common-divisor-p-of-euclidean-gcd))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-euclidean-gcd-regression-total-representations
  (and
   (finite-field-poly-common-divisor-p
    (finite-field-poly-euclidean-gcd
     'malformed-atom '(1 . malformed-tail))
    'malformed-atom '(1 . malformed-tail))
   (finite-field-poly-common-divisor-p
    (finite-field-poly-euclidean-gcd '(1 0 0) '(2 0))
    '(1 0 0) '(2 0)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-common-divisor-p-of-euclidean-gcd
                            (first 'malformed-atom)
                            (second '(1 . malformed-tail)))
                 (:instance finite-field-poly-common-divisor-p-of-euclidean-gcd
                            (first '(1 0 0)) (second '(2 0))))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-euclidean-gcd-regression-normalization-invariance
  (and
   (equal (finite-field-poly-euclidean-gcd
           (finite-field-poly-normalize first) second)
          (finite-field-poly-euclidean-gcd first second))
   (equal (finite-field-poly-euclidean-gcd
           first (finite-field-poly-normalize second))
          (finite-field-poly-euclidean-gcd first second))
   (equal (finite-field-poly-normalize
           (finite-field-poly-euclidean-gcd first second))
          (finite-field-poly-euclidean-gcd first second)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-euclidean-gcd-of-normalize-first)
                 (:instance finite-field-poly-euclidean-gcd-of-normalize-second)
                 (:instance finite-field-poly-normalize-of-euclidean-gcd))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-euclidean-gcd-regression-divides-projections
  (and
   (finite-field-poly-divides-p
    (finite-field-poly-euclidean-gcd first second) first)
   (finite-field-poly-divides-p
    (finite-field-poly-euclidean-gcd first second) second))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-euclidean-gcd-divides-first)
                 (:instance finite-field-poly-euclidean-gcd-divides-second))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-euclidean-gcd-regression-greatestness
  (implies
   (finite-field-poly-common-divisor-p divisor first second)
   (finite-field-poly-divides-p
    divisor (finite-field-poly-euclidean-gcd first second)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-common-divisor-p-greatestness))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-euclidean-gcd-regression-raw-correct
  (and
   (finite-field-poly-common-divisor-p
    (finite-field-poly-euclidean-gcd first second) first second)
   (implies
    (finite-field-poly-common-divisor-p divisor first second)
    (finite-field-poly-divides-p
     divisor (finite-field-poly-euclidean-gcd first second))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-euclidean-gcd-raw-correct))
           :in-theory (theory 'minimal-theory))))
