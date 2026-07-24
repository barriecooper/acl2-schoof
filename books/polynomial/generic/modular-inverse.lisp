(in-package "GPOLY")
(include-book "monic-xgcd-reduction")

; This total candidate deliberately does not test the gcd.  It performs one
; monic XGCD call and reduces its first Bezout coefficient through the public
; remainder interface.
(defund poly-modular-inverse (first modulus)
  (mv-let (gcd s coefficient-t)
    (poly-monic-extended-euclidean-gcd first modulus)
    (declare (ignore gcd coefficient-t))
    (poly-remainder s modulus)))

(defthm poly-modular-inverse-definition
  (equal (poly-modular-inverse first modulus)
         (poly-remainder
          (mv-nth 1
           (poly-monic-extended-euclidean-gcd first modulus))
          modulus))
  :hints (("Goal"
           :in-theory (e/d (poly-modular-inverse)
                           (poly-monic-extended-euclidean-gcd
                            poly-monic-extended-euclidean-gcd-is-scaled-xgcd
                            poly-remainder)))))

(defthm poly-modular-inverse-canonical
  (canonical-polynomial-p (poly-modular-inverse first modulus))
  :hints (("Goal"
           :use ((:instance poly-remainder-canonical
                            (dividend
                             (mv-nth 1
                              (poly-monic-extended-euclidean-gcd
                               first modulus))))
                 (:instance poly-modular-inverse-definition))
           :in-theory (disable poly-remainder canonical-polynomial-p
                               poly-monic-extended-euclidean-gcd
                               poly-monic-extended-euclidean-gcd-is-scaled-xgcd
                               poly-modular-inverse))))

(defthm normalize-of-poly-modular-inverse
  (equal (normalize (poly-modular-inverse first modulus))
         (poly-modular-inverse first modulus))
  :hints (("Goal"
           :use ((:instance normalize-when-canonical
                            (xs (poly-modular-inverse first modulus)))
                 (:instance poly-modular-inverse-canonical))
           :in-theory (disable normalize canonical-polynomial-p
                               poly-modular-inverse))))

; Reducing the coefficient before multiplication preserves the final reduced
; product.  This is exactly the existing left-factor multiplication law.
(defthm poly-remainder-of-poly-mul-poly-modular-inverse
  (equal
   (poly-remainder
    (poly-mul (poly-modular-inverse first modulus) first) modulus)
   (poly-remainder
    (poly-mul
     (mv-nth 1 (poly-monic-extended-euclidean-gcd first modulus)) first)
    modulus))
  :hints
  (("Goal"
    :use ((:instance poly-remainder-of-poly-mul-remainder-left
                     (left
                      (mv-nth 1
                       (poly-monic-extended-euclidean-gcd first modulus)))
                     (right first))
          (:instance poly-modular-inverse-definition))
    :in-theory (disable poly-remainder poly-mul
                        poly-monic-extended-euclidean-gcd
                        poly-monic-extended-euclidean-gcd-is-scaled-xgcd
                        poly-modular-inverse))))

(defthm poly-modular-inverse-correct
  (implies
   (equal (poly-monic-euclidean-gcd first modulus) (polynomial-one))
   (equal
    (poly-remainder
     (poly-mul (poly-modular-inverse first modulus) first) modulus)
    (poly-remainder (polynomial-one) modulus)))
  :hints
  (("Goal"
    :use ((:instance poly-remainder-of-poly-mul-poly-modular-inverse)
          (:instance
           poly-monic-extended-euclidean-gcd-first-coefficient-reduction
           (second modulus)))
    :in-theory
    (disable poly-remainder poly-mul polynomial-one
             poly-monic-euclidean-gcd poly-monic-extended-euclidean-gcd
             poly-monic-euclidean-gcd-is-monic-normalize
             poly-monic-extended-euclidean-gcd-is-scaled-xgcd
             poly-modular-inverse-definition
             poly-remainder-of-poly-mul-poly-modular-inverse
             poly-monic-extended-euclidean-gcd-first-coefficient-reduction))))

(defthm poly-modular-inverse-remainder-one
  (implies
   (and (equal (poly-monic-euclidean-gcd first modulus) (polynomial-one))
        (consp (normalize modulus))
        (< 0 (poly-degree (normalize modulus))))
   (equal
    (poly-remainder
     (poly-mul (poly-modular-inverse first modulus) first) modulus)
    (polynomial-one)))
  :hints
  (("Goal"
    :use ((:instance poly-modular-inverse-correct)
          (:instance poly-remainder-of-polynomial-one-when-positive-degree))
    :in-theory (disable poly-modular-inverse poly-remainder poly-mul
                        polynomial-one normalize poly-degree
                        poly-monic-euclidean-gcd
                        poly-monic-euclidean-gcd-is-monic-normalize
                        poly-monic-extended-euclidean-gcd-is-scaled-xgcd
                        poly-remainder-of-poly-mul-poly-modular-inverse
                        poly-modular-inverse-correct
                        poly-remainder-of-polynomial-one-when-positive-degree))))

; Exact executions use only the constrained field's zero and one laws.
(local
 (defthm field-inv-of-negative-one-for-modular-inverse
   (equal (gfield::field-inv
           (gfield::field-neg (gfield::field-one)))
          (gfield::field-neg (gfield::field-one)))
   :hints
   (("Goal"
     :use ((:instance gfield::field-multiplicative-inverse-unique
                      (x (gfield::field-neg (gfield::field-one)))
                      (y (gfield::field-neg (gfield::field-one)))))))))

(defthm poly-modular-inverse-regression-positive-degree
  (let* ((one (polynomial-one))
         (x (monomial (gfield::field-one) 1))
         (first (poly-add (poly-mul x x) one))
         (s (mv-nth 1
                    (poly-monic-extended-euclidean-gcd first x)))
         (inverse (poly-modular-inverse first x)))
    (and (equal s one)
         (equal inverse one)
         (equal (normalize inverse) inverse)
         (equal (poly-remainder (poly-mul inverse first) x) one)))
  :hints (("Goal" :in-theory (enable poly-modular-inverse))))

(defthm poly-modular-inverse-regression-rescaled-multi-step
  (let* ((minus-one (gfield::field-neg (gfield::field-one)))
         (one (polynomial-one))
         (x (monomial (gfield::field-one) 1))
         (first (poly-scale minus-one (poly-add (poly-mul x x) one)))
         (modulus (poly-scale minus-one x))
         (raw-s (mv-nth 1 (poly-extended-euclidean-gcd first modulus)))
         (s (mv-nth 1
                    (poly-monic-extended-euclidean-gcd first modulus)))
         (inverse (poly-modular-inverse first modulus)))
    (and (equal raw-s one)
         (equal s (list minus-one))
         (equal inverse (list minus-one))
         (equal (normalize inverse) inverse)
         (equal (poly-remainder (poly-mul inverse first) modulus) one)))
  :hints (("Goal" :in-theory (enable poly-modular-inverse))))

(defthm poly-modular-inverse-regression-total-inputs
  (let ((one (polynomial-one)))
    (and
     (equal (poly-modular-inverse nil nil) nil)
     (equal (poly-modular-inverse 'malformed-first
                                  'malformed-modulus) nil)
     (equal (poly-modular-inverse
             (cons (gfield::field-one) 'malformed-tail)
             (list (gfield::field-zero) (gfield::field-zero)))
            one)
     (equal (poly-modular-inverse
             (list (gfield::field-one) (gfield::field-zero)) nil)
            one)
     (equal (poly-modular-inverse
             (list 'malformed-coefficient (gfield::field-zero)) nil)
            (const
             (gfield::field-inv
              (poly-leading-coefficient (list 'malformed-coefficient)))))
     (equal (poly-modular-inverse one one) nil)
     (equal (poly-modular-inverse
             one (list (gfield::field-neg (gfield::field-one))))
            nil)))
  :hints (("Goal" :in-theory (enable poly-modular-inverse))))

(defthm poly-modular-inverse-regression-nontrivial-gcd
  (let* ((one (polynomial-one))
         (x (monomial (gfield::field-one) 1))
         (linear (poly-add x one))
         (first (poly-mul linear linear)))
    (and (equal (poly-modular-inverse first linear) nil)
         (not (equal (poly-monic-euclidean-gcd first linear) one))))
  :hints (("Goal" :in-theory (enable poly-modular-inverse))))
