(in-package "GPOLY")

(include-book "finite-field-modular-inverse")
(include-book "finite-field-monic-xgcd-regression")
(include-book "finite-field-monic-xgcd-reduction-regression")

(defthm finite-field-poly-modular-inverse-definition-minimal-theory-client
  (equal
   (finite-field-poly-modular-inverse first modulus)
   (finite-field-poly-remainder
    (mv-nth 1
            (finite-field-poly-monic-extended-euclidean-gcd first modulus))
    modulus))
  :rule-classes nil
  :hints (("Goal" :use ((:instance finite-field-poly-modular-inverse-definition))
                  :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-modular-inverse-correct-minimal-theory-client
  (implies
   (equal (finite-field-poly-monic-euclidean-gcd first modulus)
          (finite-field-polynomial-one))
   (equal
    (finite-field-poly-remainder
     (finite-field-poly-mul
      (finite-field-poly-modular-inverse first modulus) first)
     modulus)
    (finite-field-poly-remainder (finite-field-polynomial-one) modulus)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance finite-field-poly-modular-inverse-correct))
                  :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-modular-inverse-reduced-clients
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
     (finite-field-poly-reduced-one modulus))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance finite-field-poly-reduced-mul-modular-inverse-left)
     (:instance finite-field-poly-reduced-mul-modular-inverse-right))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-modular-inverse-positive-degree-client
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
    :use ((:instance finite-field-poly-modular-inverse-remainder-one))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-modular-inverse-total-input-regressions
  (let ((one (finite-field-polynomial-one)))
    (and
     (equal (finite-field-poly-modular-inverse nil nil) nil)
     (equal (finite-field-poly-modular-inverse
             'malformed-first 'malformed-modulus) nil)
     (equal (finite-field-poly-modular-inverse
             (cons (gfield::finite-field-one) 'malformed-tail)
             (list (gfield::finite-field-zero)
                   (gfield::finite-field-zero)))
            one)
     (equal (finite-field-poly-modular-inverse
             (list (gfield::finite-field-one)
                   (gfield::finite-field-zero)) nil)
            one)
     ; Constant moduli reduce every candidate, and reduced one, to zero.
     (equal (finite-field-poly-modular-inverse one one) nil)
     (equal (finite-field-poly-reduced-one one) nil)))
  :hints
  (("Goal"
    :use
    ((:instance finite-field-monic-xgcd-total-boundary-regressions)
     (:instance finite-field-polynomial-one-total-remainder-regressions)
     (:instance finite-field-polynomial-one-modulo-negative-one-regression)
     (:instance finite-field-poly-modular-inverse-definition
                (first nil) (modulus nil))
     (:instance finite-field-poly-modular-inverse-definition
                (first 'malformed-first)
                (modulus 'malformed-modulus)))
    :in-theory
    (enable finite-field-poly-modular-inverse
            finite-field-poly-reduced-one))))

(defthm finite-field-poly-modular-inverse-coefficient-fixing-regression
  (let ((candidate
         (finite-field-poly-modular-inverse
          (list 'malformed-coefficient (gfield::finite-field-zero)) nil)))
    (and (finite-field-canonical-polynomial-p candidate)
         (equal (finite-field-poly-normalize candidate) candidate)))
  :hints
  (("Goal"
    :use
    ((:instance finite-field-poly-modular-inverse-canonical
                (first (list 'malformed-coefficient
                             (gfield::finite-field-zero)))
                (modulus nil))
     (:instance finite-field-poly-normalize-of-poly-modular-inverse
                (first (list 'malformed-coefficient
                             (gfield::finite-field-zero)))
                (modulus nil)))
    :in-theory (theory 'minimal-theory))))

; This is intentionally a conditional specialization, not an exact execution:
; the abstract finite-field context does not select a concrete characteristic.
(defthm finite-field-poly-modular-inverse-negative-one-constant-client
  (implies
   (equal
    (finite-field-poly-monic-euclidean-gcd
     (finite-field-polynomial-one)
     (list (gfield::finite-field-neg (gfield::finite-field-one))))
    (finite-field-polynomial-one))
   (equal
    (finite-field-poly-reduced-mul
     (finite-field-polynomial-one)
     (finite-field-poly-modular-inverse
      (finite-field-polynomial-one)
      (list (gfield::finite-field-neg (gfield::finite-field-one))))
     (list (gfield::finite-field-neg (gfield::finite-field-one))))
    (finite-field-poly-reduced-one
     (list (gfield::finite-field-neg (gfield::finite-field-one))))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance finite-field-poly-reduced-mul-modular-inverse-right
                (first (finite-field-polynomial-one))
                (modulus
                 (list (gfield::finite-field-neg
                        (gfield::finite-field-one))))))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-modular-inverse-positive-degree-regression
  (let* ((one (finite-field-polynomial-one))
         (x (finite-field-poly-monomial (gfield::finite-field-one) 1))
         (first (finite-field-poly-add (finite-field-poly-mul x x) one)))
    (implies
     (and (equal (finite-field-poly-monic-euclidean-gcd first x) one)
          (consp (finite-field-poly-normalize x))
          (< 0 (finite-field-poly-degree (finite-field-poly-normalize x))))
     (equal (finite-field-poly-remainder
             (finite-field-poly-mul
              (finite-field-poly-modular-inverse first x) first)
             x)
            one)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance finite-field-poly-modular-inverse-remainder-one
                (first
                 (finite-field-poly-add
                  (finite-field-poly-mul
                   (finite-field-poly-monomial
                    (gfield::finite-field-one) 1)
                   (finite-field-poly-monomial
                    (gfield::finite-field-one) 1))
                  (finite-field-polynomial-one)))
                (modulus
                 (finite-field-poly-monomial
                  (gfield::finite-field-one) 1))))
    :in-theory (theory 'minimal-theory))))

; This abstract-context specialization records the exact data path rather than
; mislabelling an unevaluated constrained-field example as concrete execution.
(defthm finite-field-poly-modular-inverse-rescaled-regression
  (implies
   (not
    (equal
     (mv-nth 1
             (finite-field-poly-monic-extended-euclidean-gcd first modulus))
     (mv-nth 1
             (finite-field-poly-extended-euclidean-gcd first modulus))))
   (equal
    (finite-field-poly-modular-inverse first modulus)
    (finite-field-poly-remainder
     (mv-nth 1
             (finite-field-poly-monic-extended-euclidean-gcd first modulus))
     modulus)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-modular-inverse-definition))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-modular-inverse-nontrivial-gcd-regression
  (implies
   (not (equal (finite-field-poly-monic-euclidean-gcd first modulus)
               (finite-field-polynomial-one)))
   (and
    (finite-field-canonical-polynomial-p
     (finite-field-poly-modular-inverse first modulus))
    (equal
     (finite-field-poly-normalize
      (finite-field-poly-modular-inverse first modulus))
     (finite-field-poly-modular-inverse first modulus))))
  :hints
  (("Goal"
    :use
    ((:instance finite-field-poly-modular-inverse-canonical)
     (:instance finite-field-poly-normalize-of-poly-modular-inverse))
    :in-theory (theory 'minimal-theory))))
