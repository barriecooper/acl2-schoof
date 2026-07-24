(in-package "GPOLY")
(include-book "reduction")
(include-book "monic-xgcd")

; The Bezout sum differs from its first summand by a multiple of SECOND.
(defthm poly-monic-extended-euclidean-gcd-first-coefficient-reduction
  (implies
   (equal (poly-monic-euclidean-gcd first second) (polynomial-one))
   (equal
    (poly-remainder
     (poly-mul
      (mv-nth 1 (poly-monic-extended-euclidean-gcd first second)) first)
     second)
    (poly-remainder (polynomial-one) second)))
  :hints
  (("Goal"
    :use ((:instance poly-monic-extended-euclidean-gcd-bezout-when-one)
          (:instance poly-remainder-of-poly-add-divisor-multiple
                     (dividend
                      (poly-mul
                       (mv-nth 1
                        (poly-monic-extended-euclidean-gcd first second))
                       first))
                     (multiplier
                      (mv-nth 2
                       (poly-monic-extended-euclidean-gcd first second)))
                     (modulus second)))
    :in-theory (disable poly-monic-extended-euclidean-gcd
                        poly-monic-euclidean-gcd poly-remainder
                        poly-add poly-mul normalize polynomial-one
                        poly-scale poly-leading-coefficient
                        poly-monic-normalize
                        poly-monic-euclidean-gcd-is-monic-normalize
                        poly-monic-extended-euclidean-gcd-is-scaled-xgcd
                        poly-monic-extended-euclidean-gcd-bezout-when-one
                        poly-remainder-of-poly-add-divisor-multiple))))

(defthm poly-monic-extended-euclidean-gcd-first-coefficient-remainder-one
  (implies
   (and (equal (poly-monic-euclidean-gcd first second) (polynomial-one))
        (consp (normalize second))
        (< 0 (poly-degree (normalize second))))
   (equal
    (poly-remainder
     (poly-mul
      (mv-nth 1 (poly-monic-extended-euclidean-gcd first second)) first)
     second)
    (polynomial-one)))
  :hints
  (("Goal"
    :use ((:instance
           poly-monic-extended-euclidean-gcd-first-coefficient-reduction)
          (:instance poly-remainder-of-polynomial-one-when-positive-degree
                     (modulus second)))
    :in-theory (disable poly-monic-extended-euclidean-gcd
                        poly-monic-euclidean-gcd poly-remainder
                        polynomial-one normalize poly-degree poly-mul
                        poly-scale poly-leading-coefficient
                        poly-monic-normalize
                        poly-monic-euclidean-gcd-is-monic-normalize
                        poly-monic-extended-euclidean-gcd-is-scaled-xgcd
                        poly-monic-extended-euclidean-gcd-first-coefficient-reduction
                        poly-remainder-of-polynomial-one-when-positive-degree))))

; Exact regressions distinguish literal one for positive degree from the zero
; remainder produced by every nonzero constant modulus over a field.
(defthm poly-monic-xgcd-reduction-regression-positive-degree
  (let* ((one (polynomial-one))
         (x (monomial (gfield::field-one) 1))
         (first (poly-add (poly-mul x x) one))
         (second x)
         (s (mv-nth 1
                    (poly-monic-extended-euclidean-gcd first second))))
    (equal (poly-remainder (poly-mul s first) second) one)))

(defthm poly-monic-xgcd-reduction-regression-multi-step
  (let* ((x (monomial (gfield::field-one) 1))
         (first (poly-add (poly-mul x x) (polynomial-one)))
         (second x)
         (result (poly-monic-extended-euclidean-gcd first second)))
    (and (equal (poly-remainder
                 (poly-add (poly-mul (mv-nth 1 result) first)
                           (poly-mul (mv-nth 2 result) second))
                 second)
                (poly-remainder (polynomial-one) second))
         (equal (poly-remainder (poly-mul (mv-nth 1 result) first) second)
                (polynomial-one)))))

(defthm poly-monic-xgcd-reduction-regression-total-inputs
  (let ((one (polynomial-one))
        (x (monomial (gfield::field-one) 1)))
    (and
     (equal (poly-remainder one one) nil)
     (equal (poly-remainder one
                            (list (gfield::field-neg
                                   (gfield::field-one))))
            nil)
     (equal (poly-remainder one nil) one)
     (equal (poly-remainder one 'malformed-modulus) one)
     (equal (poly-remainder one
                            (list (gfield::field-zero)
                                  (gfield::field-zero)))
            one)
     (equal (poly-remainder one
                            (list (gfield::field-one)
                                  (gfield::field-one)
                                  (gfield::field-zero)))
            one)
     (equal (poly-remainder
             (poly-mul
              (mv-nth 1 (poly-monic-extended-euclidean-gcd
                          (poly-add (poly-mul x x) one) x))
              (poly-add (poly-mul x x) one))
             x)
            one))))

(defthm poly-monic-xgcd-reduction-regression-nontrivial-gcd
  (let* ((one (polynomial-one))
         (x (monomial (gfield::field-one) 1))
         (linear (poly-add x one))
         (first (poly-mul linear linear)))
    (not (equal (poly-monic-euclidean-gcd first linear) one))))
