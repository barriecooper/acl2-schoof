(in-package "GPOLY")

(include-book "finite-field-reduction")
(include-book "finite-field-monic-xgcd")

; The literal singleton one is already canonical and has degree zero.  Keep
; these bookkeeping facts local: the public boundary is the remainder fact.
(local
 (defthm finite-field-canonical-polynomial-p-of-singleton-one-for-reduction
   (finite-field-canonical-polynomial-p
    (list (gfield::finite-field-one)))
   :hints (("Goal"
            :in-theory (enable finite-field-canonical-polynomial-p
                               finite-field-poly-leading-coefficient)))))

(local
 (defthm finite-field-poly-degree-of-singleton-one-for-reduction
   (equal (finite-field-poly-degree
           (list (gfield::finite-field-one)))
          0)
   :hints (("Goal" :in-theory (enable finite-field-poly-degree)))))

(defthm finite-field-poly-remainder-of-polynomial-one-when-positive-degree
  (implies
   (and (consp (finite-field-poly-normalize modulus))
        (< 0 (finite-field-poly-degree
              (finite-field-poly-normalize modulus))))
   (equal
    (finite-field-poly-remainder
     (list (gfield::finite-field-one)) modulus)
    (list (gfield::finite-field-one))))
  :hints
  (("Goal"
    :use
    ((:instance finite-field-poly-remainder-canonical-lower-degree
                (dividend (list (gfield::finite-field-one))))
     (:instance
      finite-field-canonical-polynomial-p-of-singleton-one-for-reduction)
     (:instance finite-field-poly-degree-of-singleton-one-for-reduction))
    :in-theory
    (disable finite-field-poly-remainder finite-field-poly-normalize
             finite-field-poly-degree finite-field-canonical-polynomial-p))))

; The Bezout sum differs from its first summand by a multiple of SECOND.
(defthm
  finite-field-poly-monic-extended-euclidean-gcd-first-coefficient-reduction
  (implies
   (equal (finite-field-poly-monic-euclidean-gcd first second)
          (list (gfield::finite-field-one)))
   (equal
    (finite-field-poly-remainder
     (finite-field-poly-mul
      (mv-nth 1
              (finite-field-poly-monic-extended-euclidean-gcd first second))
      first)
     second)
    (finite-field-poly-remainder
     (list (gfield::finite-field-one)) second)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      finite-field-poly-monic-extended-euclidean-gcd-bezout-when-one)
     (:instance finite-field-poly-remainder-of-poly-add-divisor-multiple
                (dividend
                 (finite-field-poly-mul
                  (mv-nth
                   1
                   (finite-field-poly-monic-extended-euclidean-gcd
                    first second))
                  first))
                (multiplier
                 (mv-nth
                  2
                  (finite-field-poly-monic-extended-euclidean-gcd
                   first second)))
                (modulus second)))
    :in-theory
    (disable finite-field-poly-monic-extended-euclidean-gcd
             finite-field-poly-monic-euclidean-gcd
             finite-field-poly-remainder finite-field-poly-add
             finite-field-poly-mul finite-field-poly-normalize
             finite-field-poly-remainder-of-poly-add-divisor-multiple))))

(defthm
 finite-field-poly-monic-extended-euclidean-gcd-first-coefficient-remainder-one
  (implies
   (and
    (equal (finite-field-poly-monic-euclidean-gcd first second)
           (list (gfield::finite-field-one)))
    (consp (finite-field-poly-normalize second))
    (< 0 (finite-field-poly-degree
          (finite-field-poly-normalize second))))
   (equal
    (finite-field-poly-remainder
     (finite-field-poly-mul
      (mv-nth 1
              (finite-field-poly-monic-extended-euclidean-gcd first second))
      first)
     second)
    (list (gfield::finite-field-one))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      finite-field-poly-monic-extended-euclidean-gcd-first-coefficient-reduction)
     (:instance
      finite-field-poly-remainder-of-polynomial-one-when-positive-degree
      (modulus second)))
    :in-theory
    (disable finite-field-poly-monic-extended-euclidean-gcd
             finite-field-poly-monic-euclidean-gcd
             finite-field-poly-remainder finite-field-poly-normalize
             finite-field-poly-degree finite-field-poly-mul
             finite-field-poly-remainder-of-polynomial-one-when-positive-degree))))
