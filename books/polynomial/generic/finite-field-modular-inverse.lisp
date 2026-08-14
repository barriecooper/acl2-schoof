(in-package "GPOLY")

(include-book "finite-field-monic-xgcd-reduction")
(include-book "finite-field-reduced-ring")

; A total candidate: exactly one monic XGCD call, followed by reduction of its
; first-input coefficient.  Correctness is deliberately a separate theorem.
(defund finite-field-poly-modular-inverse (first modulus)
  (declare (xargs :guard t))
  (mv-let (gcd s coefficient-t)
    (finite-field-poly-monic-extended-euclidean-gcd first modulus)
    (declare (ignore gcd coefficient-t))
    (finite-field-poly-remainder s modulus)))

(defthm finite-field-poly-modular-inverse-definition
  (equal
   (finite-field-poly-modular-inverse first modulus)
   (finite-field-poly-remainder
    (mv-nth 1
            (finite-field-poly-monic-extended-euclidean-gcd first modulus))
    modulus))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (finite-field-poly-modular-inverse)
                           (finite-field-poly-monic-extended-euclidean-gcd
                            finite-field-poly-remainder)))))

(verify-guards finite-field-poly-modular-inverse)

(defthm finite-field-poly-modular-inverse-canonical
  (finite-field-canonical-polynomial-p
   (finite-field-poly-modular-inverse first modulus))
  :hints
  (("Goal"
    :use
    ((:instance finite-field-poly-remainder-canonical
                (dividend
                 (mv-nth
                  1
                  (finite-field-poly-monic-extended-euclidean-gcd
                   first modulus))))
     (:instance finite-field-poly-modular-inverse-definition))
    :in-theory
    (disable finite-field-poly-remainder
             finite-field-canonical-polynomial-p
             finite-field-poly-monic-extended-euclidean-gcd
             finite-field-poly-modular-inverse))))

(defthm finite-field-poly-normalize-of-poly-modular-inverse
  (equal
   (finite-field-poly-normalize
    (finite-field-poly-modular-inverse first modulus))
   (finite-field-poly-modular-inverse first modulus))
  :hints
  (("Goal"
    :use
    ((:instance finite-field-poly-normalize-when-canonical
                (xs (finite-field-poly-modular-inverse first modulus)))
     (:instance finite-field-poly-modular-inverse-canonical))
    :in-theory
    (disable finite-field-poly-normalize
             finite-field-canonical-polynomial-p
             finite-field-poly-modular-inverse))))

(defthm finite-field-poly-remainder-of-poly-mul-poly-modular-inverse
  (equal
   (finite-field-poly-remainder
    (finite-field-poly-mul
     (finite-field-poly-modular-inverse first modulus) first)
    modulus)
   (finite-field-poly-remainder
    (finite-field-poly-mul
     (mv-nth 1
             (finite-field-poly-monic-extended-euclidean-gcd first modulus))
     first)
    modulus))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance finite-field-poly-remainder-of-poly-mul-remainder-left
                (left
                 (mv-nth
                  1
                  (finite-field-poly-monic-extended-euclidean-gcd
                   first modulus)))
                (right first))
     (:instance finite-field-poly-modular-inverse-definition))
    :in-theory
    (disable finite-field-poly-remainder finite-field-poly-mul
             finite-field-poly-monic-extended-euclidean-gcd
             finite-field-poly-modular-inverse))))

(defthm finite-field-poly-modular-inverse-correct
  (implies
   (equal (finite-field-poly-monic-euclidean-gcd first modulus)
          (finite-field-polynomial-one))
   (equal
    (finite-field-poly-remainder
     (finite-field-poly-mul
      (finite-field-poly-modular-inverse first modulus) first)
     modulus)
    (finite-field-poly-remainder
     (finite-field-polynomial-one) modulus)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance finite-field-poly-remainder-of-poly-mul-poly-modular-inverse)
     (:instance
      finite-field-poly-monic-extended-euclidean-gcd-first-coefficient-reduction
      (second modulus))
     (:instance finite-field-polynomial-one-definition))
    :in-theory
    (disable finite-field-poly-remainder finite-field-poly-mul
             finite-field-polynomial-one
             finite-field-poly-monic-euclidean-gcd
             finite-field-poly-monic-extended-euclidean-gcd
             finite-field-poly-modular-inverse))))

(defthm finite-field-poly-reduced-mul-modular-inverse-left
  (implies
   (equal (finite-field-poly-monic-euclidean-gcd first modulus)
          (finite-field-polynomial-one))
   (equal
    (finite-field-poly-reduced-mul
     (finite-field-poly-modular-inverse first modulus) first modulus)
    (finite-field-poly-reduced-one modulus)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-modular-inverse-correct)
          (:instance finite-field-poly-reduced-mul-definition
                     (left (finite-field-poly-modular-inverse first modulus))
                     (right first))
          (:instance finite-field-poly-reduced-one-definition))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-reduced-mul-modular-inverse-right
  (implies
   (equal (finite-field-poly-monic-euclidean-gcd first modulus)
          (finite-field-polynomial-one))
   (equal
    (finite-field-poly-reduced-mul
     first (finite-field-poly-modular-inverse first modulus) modulus)
    (finite-field-poly-reduced-one modulus)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance finite-field-poly-reduced-mul-modular-inverse-left)
     (:instance finite-field-poly-reduced-mul-commutative
                (a first)
                (b (finite-field-poly-modular-inverse first modulus))))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-modular-inverse-remainder-one
  (implies
   (and
    (equal (finite-field-poly-monic-euclidean-gcd first modulus)
           (finite-field-polynomial-one))
    (consp (finite-field-poly-normalize modulus))
    (< 0 (finite-field-poly-degree
          (finite-field-poly-normalize modulus))))
   (equal
    (finite-field-poly-remainder
     (finite-field-poly-mul
      (finite-field-poly-modular-inverse first modulus) first)
     modulus)
    (finite-field-polynomial-one)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance finite-field-poly-modular-inverse-correct)
     (:instance
      finite-field-poly-remainder-of-polynomial-one-when-positive-degree)
     (:instance finite-field-polynomial-one-definition))
    :in-theory
    (disable finite-field-poly-modular-inverse finite-field-poly-remainder
             finite-field-poly-mul finite-field-polynomial-one
             finite-field-poly-normalize finite-field-poly-degree
             finite-field-poly-monic-euclidean-gcd))))

(defthm finite-field-poly-modular-inverse-specification
  (and
   (finite-field-canonical-polynomial-p
    (finite-field-poly-modular-inverse first modulus))
   (equal
    (finite-field-poly-normalize
     (finite-field-poly-modular-inverse first modulus))
    (finite-field-poly-modular-inverse first modulus))
   (implies
    (equal (finite-field-poly-monic-euclidean-gcd first modulus)
           (finite-field-polynomial-one))
    (and
     (equal
      (finite-field-poly-reduced-mul
       (finite-field-poly-modular-inverse first modulus) first modulus)
      (finite-field-poly-reduced-one modulus))
     (equal
      (finite-field-poly-reduced-mul
       first (finite-field-poly-modular-inverse first modulus) modulus)
      (finite-field-poly-reduced-one modulus)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance finite-field-poly-modular-inverse-canonical)
     (:instance finite-field-poly-normalize-of-poly-modular-inverse)
     (:instance finite-field-poly-reduced-mul-modular-inverse-left)
     (:instance finite-field-poly-reduced-mul-modular-inverse-right))
    :in-theory (theory 'minimal-theory))))
