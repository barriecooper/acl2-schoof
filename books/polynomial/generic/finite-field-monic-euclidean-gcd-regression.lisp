(in-package "GPOLY")

(include-book "finite-field-monic-euclidean-gcd")

; These clients deliberately keep every implementation closed.  The quoted
; inputs cover normalized zero, malformed and dotted lists, fixed
; coefficients, and trailing-zero representations without requiring a
; concrete finite-field executable instance.
(defthm finite-field-monic-gcd-regression-zero-and-total-representations
  (and
   (equal (consp (finite-field-poly-monic-euclidean-gcd nil nil))
          (consp (finite-field-poly-euclidean-gcd nil nil)))
   (equal (consp (finite-field-poly-monic-euclidean-gcd first nil))
          (consp (finite-field-poly-euclidean-gcd first nil)))
   (equal (consp (finite-field-poly-monic-euclidean-gcd
                  'malformed-atom '(1 . malformed-tail)))
          (consp (finite-field-poly-euclidean-gcd
                  'malformed-atom '(1 . malformed-tail))))
   (equal (consp (finite-field-poly-monic-euclidean-gcd
                  '(1 0 0) '(2 0)))
          (consp (finite-field-poly-euclidean-gcd '(1 0 0) '(2 0))))
   (equal (consp (finite-field-poly-monic-euclidean-gcd
                  '(fixed-coefficient) '(0 fixed-coefficient 0)))
          (consp (finite-field-poly-euclidean-gcd
                  '(fixed-coefficient) '(0 fixed-coefficient 0)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-consp-of-poly-monic-euclidean-gcd
                            (first nil) (second nil))
                 (:instance finite-field-consp-of-poly-monic-euclidean-gcd
                            (second nil))
                 (:instance finite-field-consp-of-poly-monic-euclidean-gcd
                            (first 'malformed-atom)
                            (second '(1 . malformed-tail)))
                 (:instance finite-field-consp-of-poly-monic-euclidean-gcd
                            (first '(1 0 0)) (second '(2 0)))
                 (:instance finite-field-consp-of-poly-monic-euclidean-gcd
                            (first '(fixed-coefficient))
                            (second '(0 fixed-coefficient 0))))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-monic-gcd-regression-normalization-and-monic-shapes
  (and
   (equal (finite-field-poly-monic-euclidean-gcd
           (finite-field-poly-normalize first) second)
          (finite-field-poly-monic-euclidean-gcd first second))
   (equal (finite-field-poly-monic-euclidean-gcd
           first (finite-field-poly-normalize second))
          (finite-field-poly-monic-euclidean-gcd first second))
   (finite-field-canonical-polynomial-p
    (finite-field-poly-monic-euclidean-gcd first second))
   (equal (finite-field-poly-normalize
           (finite-field-poly-monic-euclidean-gcd first second))
          (finite-field-poly-monic-euclidean-gcd first second))
   (equal (finite-field-poly-leading-coefficient
           (finite-field-poly-monic-euclidean-gcd first second))
          (if (consp (finite-field-poly-euclidean-gcd first second))
              (gfield::finite-field-one)
            (gfield::finite-field-zero))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  finite-field-poly-monic-euclidean-gcd-of-normalize-first)
                 (:instance
                  finite-field-poly-monic-euclidean-gcd-of-normalize-second)
                 (:instance
                  finite-field-canonical-polynomial-p-of-poly-monic-euclidean-gcd)
                 (:instance
                  finite-field-poly-normalize-of-poly-monic-euclidean-gcd)
                 (:instance
                  finite-field-poly-leading-coefficient-of-poly-monic-euclidean-gcd))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-monic-gcd-regression-divisibility-orientations
  (and
   (equal (finite-field-poly-divides-p
           divisor (finite-field-poly-monic-normalize dividend))
          (finite-field-poly-divides-p divisor dividend))
   (equal (finite-field-poly-divides-p
           (finite-field-poly-monic-normalize divisor) dividend)
          (finite-field-poly-divides-p divisor dividend)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  finite-field-poly-divides-p-of-poly-monic-normalize-dividend)
                 (:instance
                  finite-field-poly-divides-p-of-poly-monic-normalize-divisor))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-monic-gcd-regression-correctness-endpoints
  (and
   (finite-field-poly-divides-p
    (finite-field-poly-monic-euclidean-gcd first second) first)
   (finite-field-poly-divides-p
    (finite-field-poly-monic-euclidean-gcd first second) second)
   (finite-field-poly-common-divisor-p
    (finite-field-poly-monic-euclidean-gcd first second) first second)
   (implies
    (finite-field-poly-common-divisor-p divisor first second)
    (finite-field-poly-divides-p
     divisor (finite-field-poly-monic-euclidean-gcd first second))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-monic-euclidean-gcd-divides-first)
                 (:instance finite-field-poly-monic-euclidean-gcd-divides-second)
                 (:instance
                  finite-field-poly-common-divisor-p-of-poly-monic-euclidean-gcd)
                 (:instance
                  finite-field-poly-common-divisor-divides-monic-euclidean-gcd))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-monic-gcd-regression-aggregate
  (and
   (finite-field-poly-common-divisor-p
    (finite-field-poly-monic-euclidean-gcd first second) first second)
   (implies
    (finite-field-poly-common-divisor-p divisor first second)
    (finite-field-poly-divides-p
     divisor (finite-field-poly-monic-euclidean-gcd first second))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-monic-euclidean-gcd-correct))
           :in-theory (theory 'minimal-theory))))
