(in-package "GPOLY")
(include-book "division")

; Modular reduction is only the public remainder projection of recursive
; division.  POLY-DIVMOD owns normalization of both operands.
(defun poly-remainder (dividend modulus)
  (mv-let (quotient remainder)
    (poly-divmod dividend modulus)
    (declare (ignore quotient))
    remainder))

(defthm poly-remainder-is-divmod-remainder
  (equal (poly-remainder dividend modulus)
         (mv-nth 1 (poly-divmod dividend modulus)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable poly-remainder))))

(defthm poly-remainder-canonical
  (canonical-polynomial-p (poly-remainder dividend modulus))
  :hints (("Goal"
           :use ((:instance poly-divmod-remainder-canonical
                            (f dividend) (g modulus)))
           :in-theory (enable poly-remainder))))

(defthm poly-remainder-of-normalize-dividend
  (equal (poly-remainder (normalize dividend) modulus)
         (poly-remainder dividend modulus))
  :hints (("Goal"
           :in-theory (e/d (poly-remainder poly-divmod)
                           (poly-divmod-core normalize)))))

(defthm poly-remainder-of-normalize-modulus
  (equal (poly-remainder dividend (normalize modulus))
         (poly-remainder dividend modulus))
  :hints (("Goal"
           :in-theory (e/d (poly-remainder poly-divmod)
                           (poly-divmod-core normalize)))))

(defthm poly-remainder-zero-modulus
  (equal (poly-remainder dividend nil) (normalize dividend))
  :hints (("Goal"
           :use ((:instance poly-divmod-zero-divisor (f dividend)))
           :in-theory (enable poly-remainder))))

(defthm poly-remainder-zero-normalized-modulus
  (implies (equal (normalize modulus) nil)
           (equal (poly-remainder dividend modulus)
                  (normalize dividend)))
  :hints (("Goal"
           :use ((:instance poly-remainder-of-normalize-modulus)
                 (:instance poly-remainder-zero-modulus))
           :in-theory (disable poly-remainder poly-divmod normalize
                               poly-remainder-of-normalize-modulus
                               poly-remainder-zero-modulus))))

(defthm poly-remainder-strict-degree-bound
  (implies (consp (normalize modulus))
           (or (equal (poly-remainder dividend modulus) nil)
               (< (poly-degree (poly-remainder dividend modulus))
                  (poly-degree (normalize modulus)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-divmod-final-remainder-degree-bound
                            (f dividend) (g modulus)))
           :in-theory (enable poly-remainder))))

(defthm poly-remainder-canonical-lower-degree
  (implies (and (canonical-polynomial-p dividend)
                (consp (normalize modulus))
                (< (poly-degree dividend)
                   (poly-degree (normalize modulus))))
           (equal (poly-remainder dividend modulus) dividend))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-divmod-larger-divisor
                            (f dividend) (g modulus))
                 (:instance normalize-when-canonical (xs dividend)))
           :in-theory (enable poly-remainder))))

(defthm poly-remainder-idempotent
  (equal (poly-remainder (poly-remainder dividend modulus) modulus)
         (poly-remainder dividend modulus))
  :hints (("Goal" :cases ((consp (normalize modulus))))
          ("Subgoal 2"
           :use ((:instance poly-remainder-zero-normalized-modulus)
                 (:instance poly-remainder-zero-normalized-modulus
                            (dividend (poly-remainder dividend modulus)))
                 (:instance normalize-when-canonical
                            (xs (poly-remainder dividend modulus)))
                 (:instance poly-remainder-canonical))
           :in-theory (disable poly-remainder normalize
                               canonical-polynomial-p))
          ("Subgoal 1"
           :use ((:instance poly-remainder-strict-degree-bound)
                 (:instance poly-remainder-canonical-lower-degree
                            (dividend (poly-remainder dividend modulus))))
           :in-theory (disable poly-remainder normalize poly-degree
                               canonical-polynomial-p))))

; Subtraction cannot create a term above either canonical operand.  This is
; the small degree fact needed to compare two bounded Euclidean remainders.
(defthm poly-sub-degree-below-common-bound
  (implies (and (canonical-polynomial-p x)
                (canonical-polynomial-p y)
                (or (not (consp x)) (< (poly-degree x) bound))
                (or (not (consp y)) (< (poly-degree y) bound)))
           (or (equal (poly-sub x y) nil)
               (< (poly-degree (poly-sub x y)) bound)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance len-of-normalize
                            (xs (raw-add x (raw-neg y))))
                 (:instance len-of-raw-add (x x) (y (raw-neg y)))
                 (:instance len-of-raw-neg (x y))
                 (:instance poly-degree-when-canonical-nonzero
                            (p (poly-sub x y))))
           :in-theory (e/d (poly-sub-of-canonical-operands poly-add poly-neg)
                           (poly-sub raw-add raw-neg
                            normalize canonical-polynomial-p poly-degree)))))

(defthm poly-add-left-cancel-canonical
  (implies (and (canonical-polynomial-p x)
                (canonical-polynomial-p y)
                (polynomial-p z)
                (equal (poly-add z x) (poly-add z y)))
           (equal x y))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-add-associative
                            (x (poly-neg z)) (y z) (z x))
                 (:instance poly-add-associative
                            (x (poly-neg z)) (y z) (z y))
                 (:instance poly-add-commutative (x (poly-neg z)) (y z))
                 (:instance poly-add-inverse-right (x z)))
           :in-theory (disable poly-add-associative poly-add-commutative
                               poly-add poly-neg canonical-polynomial-p))))

(defthm poly-mul-of-poly-neg-left
  (implies (polynomial-p x)
           (equal (poly-mul (poly-neg x) y)
                  (poly-neg (poly-mul x y))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-add-left-cancel-canonical
                            (z (poly-mul x y))
                            (x (poly-mul (poly-neg x) y))
                            (y (poly-neg (poly-mul x y))))
                 (:instance poly-mul-right-distributive
                            (x x) (y (poly-neg x)) (z y))
                 (:instance poly-add-inverse-right (x x))
                 (:instance poly-add-inverse-right (x (poly-mul x y))))
           :in-theory (disable poly-add poly-mul poly-neg
                               canonical-polynomial-p polynomial-p))))

(defthm poly-add-right-cancel-canonical
  (implies (and (canonical-polynomial-p x)
                (canonical-polynomial-p y)
                (polynomial-p z)
                (equal (poly-add x z) (poly-add y z)))
           (equal x y))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-add-left-cancel-canonical)
                 (:instance poly-add-commutative (x x) (y z))
                 (:instance poly-add-commutative (x y) (y z)))
           :in-theory (disable poly-add poly-add-commutative
                               canonical-polynomial-p))))

(defthm equal-sums-imply-left-equals-right-plus-difference
  (implies (and (canonical-polynomial-p a)
                (canonical-polynomial-p b)
                (canonical-polynomial-p r1)
                (canonical-polynomial-p r2)
                (equal (poly-add a r1) (poly-add b r2)))
           (equal a (poly-add b (poly-sub r2 r1))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-add-left-to-poly-sub (x r1) (y r2))
                 (:instance canonical-polynomial-p-implies-polynomial-p
                            (xs r1))
                 (:instance poly-add-right-cancel-canonical
                            (z r1) (x a)
                            (y (poly-add b (poly-sub r2 r1))))
                 (:instance poly-add-associative
                            (x b) (y (poly-sub r2 r1)) (z r1))
                 (:instance poly-add-commutative
                            (x (poly-sub r2 r1)) (y r1)))
           :in-theory (disable poly-add poly-sub canonical-polynomial-p))))

(defthm product-of-difference-solves-product-sum
  (implies (and (polynomial-p q1) (polynomial-p q2))
           (equal (poly-add (poly-mul q2 modulus)
                            (poly-mul (poly-sub q1 q2) modulus))
                  (poly-mul q1 modulus)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-mul-right-distributive
                            (x q1) (y (poly-neg q2)) (z modulus))
                 (:instance poly-mul-of-poly-neg-left (x q2) (y modulus))
                 (:instance poly-add-associative
                            (x (poly-mul q2 modulus))
                            (y (poly-mul q1 modulus))
                            (z (poly-neg (poly-mul q2 modulus))))
                 (:instance poly-add-associative
                            (x (poly-mul q1 modulus))
                            (y (poly-mul q2 modulus))
                            (z (poly-neg (poly-mul q2 modulus))))
                 (:instance poly-add-commutative
                            (x (poly-mul q2 modulus))
                            (y (poly-mul q1 modulus)))
                 (:instance poly-add-inverse-right
                            (x (poly-mul q2 modulus)))
                 (:instance poly-add-zero-right
                            (x (poly-mul q1 modulus))))
           :in-theory (e/d (poly-sub-definition)
                           (poly-add poly-mul poly-neg poly-sub)))))

(defthm equal-reconstructions-imply-equal-differences
  (implies (and (polynomial-p q1) (polynomial-p q2)
                (canonical-polynomial-p r1)
                (canonical-polynomial-p r2)
                (equal (poly-add (poly-mul q1 modulus) r1)
                       (poly-add (poly-mul q2 modulus) r2)))
           (equal (poly-mul (poly-sub q1 q2) modulus)
                  (poly-sub r2 r1)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance equal-sums-imply-left-equals-right-plus-difference
                            (a (poly-mul q1 modulus))
                            (b (poly-mul q2 modulus)))
                 (:instance product-of-difference-solves-product-sum)
                 (:instance poly-add-left-cancel-canonical
                            (z (poly-mul q2 modulus))
                            (x (poly-mul (poly-sub q1 q2) modulus))
                            (y (poly-sub r2 r1))))
           :in-theory (disable poly-add poly-sub poly-mul
                               canonical-polynomial-p polynomial-p))))

(defthm poly-sub-equal-nil-implies-equal
  (implies (and (canonical-polynomial-p x)
                (canonical-polynomial-p y)
                (equal (poly-sub x y) nil))
           (equal x y))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-add-left-to-poly-sub (x y) (y x)))
           :in-theory (disable poly-add poly-sub canonical-polynomial-p))))

(defthm bounded-remainders-in-same-coset-are-equal
  (implies
   (and (canonical-polynomial-p r1)
        (canonical-polynomial-p r2)
        (polynomial-p q1)
        (polynomial-p q2)
        (canonical-polynomial-p modulus)
        (consp modulus)
        (or (not (consp r1)) (< (poly-degree r1) (poly-degree modulus)))
        (or (not (consp r2)) (< (poly-degree r2) (poly-degree modulus)))
        (equal (poly-add (poly-mul q1 modulus) r1)
               (poly-add (poly-mul q2 modulus) r2)))
   (equal r1 r2))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-sub-degree-below-common-bound
                            (x r2) (y r1) (bound (poly-degree modulus)))
                 (:instance equal-reconstructions-imply-equal-differences)
                 (:instance poly-sub-equal-nil-implies-equal
                            (x r2) (y r1))
                 (:instance normalize-when-canonical
                            (xs (poly-sub q1 q2)))
                 (:instance poly-degree-of-poly-mul
                            (f (poly-sub q1 q2)) (g modulus))
                 (:instance consp-of-poly-mul-when-canonical-nonzero
                            (f (poly-sub q1 q2)) (g modulus)))
           :in-theory (disable poly-degree poly-sub poly-add poly-mul
                               canonical-polynomial-p))))

(defthm poly-remainder-of-bounded-reconstruction
  (implies
   (and (consp (normalize modulus))
        (canonical-polynomial-p candidate-remainder)
        (or (not (consp candidate-remainder))
            (< (poly-degree candidate-remainder)
               (poly-degree (normalize modulus))))
        (equal (normalize dividend)
               (poly-add
                (poly-mul quotient (normalize modulus))
                candidate-remainder)))
   (equal (poly-remainder dividend modulus)
          candidate-remainder))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-divmod-reconstruction
                            (f dividend) (g modulus))
                 (:instance poly-remainder-is-divmod-remainder)
                 (:instance poly-divmod-quotient-canonical
                            (f dividend) (g modulus))
                 (:instance poly-divmod-quotient-polynomial
                            (f dividend) (g modulus))
                 (:instance poly-divmod-remainder-canonical
                            (f dividend) (g modulus))
                 (:instance poly-divmod-final-remainder-degree-bound
                            (f dividend) (g modulus))
                 (:instance bounded-remainders-in-same-coset-are-equal
                            (q1 (mv-nth 0 (poly-divmod dividend modulus)))
                            (r1 (mv-nth 1 (poly-divmod dividend modulus)))
                            (q2 (normalize quotient))
                            (r2 candidate-remainder)
                            (modulus (normalize modulus))))
           :in-theory (disable poly-divmod poly-remainder normalize poly-add
                               poly-mul poly-degree canonical-polynomial-p))))

; Adding a multiple merely changes the quotient in the certified bounded
; reconstruction.  This algebraic reshaping lemma is deliberately not a
; rewrite rule: its expanded reconstruction shape is useful only to the
; remainder theorem immediately below.
(defthm normalize-of-poly-add-modulus-multiple-reconstruction
  (equal
   (normalize
    (poly-add dividend
              (poly-mul multiplier (normalize modulus))))
   (poly-add
    (poly-mul
     (poly-add (mv-nth 0 (poly-divmod dividend modulus)) multiplier)
     (normalize modulus))
    (poly-remainder dividend modulus)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-divmod-reconstruction
                     (f dividend) (g modulus))
          (:instance poly-remainder-is-divmod-remainder)
          (:instance poly-mul-right-distributive
                     (x (mv-nth 0 (poly-divmod dividend modulus)))
                     (y multiplier) (z (normalize modulus)))
          (:instance poly-add-associative
                     (x (poly-mul
                         (mv-nth 0 (poly-divmod dividend modulus))
                         (normalize modulus)))
                     (y (poly-remainder dividend modulus))
                     (z (poly-mul multiplier (normalize modulus))))
          (:instance poly-add-associative
                     (x (poly-mul
                         (mv-nth 0 (poly-divmod dividend modulus))
                         (normalize modulus)))
                     (y (poly-mul multiplier (normalize modulus)))
                     (z (poly-remainder dividend modulus)))
          (:instance poly-add-commutative
                     (x (poly-remainder dividend modulus))
                     (y (poly-mul multiplier (normalize modulus))))
          (:instance normalize-when-canonical
                     (xs (poly-add
                          dividend
                          (poly-mul multiplier (normalize modulus))))))
    :in-theory
    (e/d (poly-add)
         (poly-divmod poly-remainder normalize poly-mul
          poly-add-associative poly-add-commutative
          canonical-polynomial-p polynomial-p)))))

(defthm poly-remainder-of-poly-add-modulus-multiple
  (implies
   (consp (normalize modulus))
   (equal
    (poly-remainder
     (poly-add dividend
               (poly-mul multiplier (normalize modulus)))
     modulus)
    (poly-remainder dividend modulus)))
  :hints
  (("Goal"
    :use
    ((:instance normalize-of-poly-add-modulus-multiple-reconstruction)
     (:instance poly-remainder-of-bounded-reconstruction
                (dividend
                 (poly-add dividend
                           (poly-mul multiplier (normalize modulus))))
                (quotient
                 (poly-add (mv-nth 0 (poly-divmod dividend modulus))
                           multiplier))
                (candidate-remainder (poly-remainder dividend modulus)))
     (:instance poly-remainder-canonical)
     (:instance poly-remainder-strict-degree-bound))
    :in-theory
    (disable poly-divmod poly-remainder normalize poly-add poly-mul
             poly-degree canonical-polynomial-p))))

(verify-guards poly-remainder)

; Generic congruence is structural equality of the two canonical remainder
; representatives.  It has no nonzero-modulus precondition.
(defun poly-congruent-p (left right modulus)
  (equal (poly-remainder left modulus)
         (poly-remainder right modulus)))

(defthm poly-congruent-p-iff-equal-remainders
  (equal (poly-congruent-p left right modulus)
         (equal (poly-remainder left modulus)
                (poly-remainder right modulus)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable poly-congruent-p))))

(defthm poly-congruent-p-reflexive
  (poly-congruent-p x x modulus))

(defthm poly-congruent-p-symmetric
  (implies (poly-congruent-p x y modulus)
           (poly-congruent-p y x modulus)))

(defthm poly-congruent-p-transitive
  (implies (and (poly-congruent-p x y modulus)
                (poly-congruent-p y z modulus))
           (poly-congruent-p x z modulus)))

(defthm poly-congruent-p-of-normalize-left
  (equal (poly-congruent-p (normalize left) right modulus)
         (poly-congruent-p left right modulus)))

(defthm poly-congruent-p-of-normalize-right
  (equal (poly-congruent-p left (normalize right) modulus)
         (poly-congruent-p left right modulus)))

(defthm poly-congruent-p-of-normalize-modulus
  (equal (poly-congruent-p left right (normalize modulus))
         (poly-congruent-p left right modulus)))

(defthm poly-congruent-p-zero-normalized-modulus
  (implies (not (consp (normalize modulus)))
           (equal (poly-congruent-p left right modulus)
                  (equal (normalize left) (normalize right))))
  :hints (("Goal"
           :use ((:instance poly-remainder-zero-normalized-modulus
                            (dividend left))
                 (:instance poly-remainder-zero-normalized-modulus
                            (dividend right)))
           :in-theory (enable poly-congruent-p))))

(defthm poly-congruent-p-with-remainder
  (poly-congruent-p dividend
                    (poly-remainder dividend modulus)
                    modulus)
  :hints (("Goal" :use ((:instance poly-remainder-idempotent))
           :in-theory (e/d (poly-congruent-p)
                           (poly-remainder poly-remainder-idempotent)))))

(defthm poly-congruent-p-of-remainder-left
  (equal (poly-congruent-p (poly-remainder left modulus) right modulus)
         (poly-congruent-p left right modulus))
  :hints (("Goal" :use ((:instance poly-remainder-idempotent
                                   (dividend left)))
           :in-theory (e/d (poly-congruent-p)
                           (poly-remainder poly-remainder-idempotent)))))

(defthm poly-congruent-p-of-remainder-right
  (equal (poly-congruent-p left (poly-remainder right modulus) modulus)
         (poly-congruent-p left right modulus))
  :hints (("Goal" :use ((:instance poly-remainder-idempotent
                                   (dividend right)))
           :in-theory (e/d (poly-congruent-p)
                           (poly-remainder poly-remainder-idempotent)))))

(defthm bounded-representatives-poly-congruent-p-iff-equal
  (implies
   (and (consp (normalize modulus))
        (canonical-polynomial-p left)
        (canonical-polynomial-p right)
        (or (not (consp left))
            (< (poly-degree left) (poly-degree (normalize modulus))))
        (or (not (consp right))
            (< (poly-degree right) (poly-degree (normalize modulus)))))
   (equal (poly-congruent-p left right modulus)
          (equal left right)))
  :hints
  (("Goal"
    :use ((:instance poly-remainder-canonical-lower-degree
                     (dividend left))
          (:instance poly-remainder-canonical-lower-degree
                     (dividend right)))
    :in-theory (enable poly-congruent-p))))

(defthm poly-add-modulus-multiple-poly-congruent-p
  (implies
   (consp (normalize modulus))
   (poly-congruent-p
    (poly-add dividend
              (poly-mul multiplier (normalize modulus)))
    dividend modulus))
  :hints (("Goal"
           :use ((:instance poly-remainder-of-poly-add-modulus-multiple))
           :in-theory (enable poly-congruent-p))))

(defthm bounded-reconstruction-poly-congruent-p
  (implies
   (and (consp (normalize modulus))
        (canonical-polynomial-p candidate-remainder)
        (or (not (consp candidate-remainder))
            (< (poly-degree candidate-remainder)
               (poly-degree (normalize modulus))))
        (equal (normalize dividend)
               (poly-add
                (poly-mul quotient (normalize modulus))
                candidate-remainder)))
   (poly-congruent-p dividend candidate-remainder modulus))
  :hints
  (("Goal"
    :use ((:instance poly-remainder-of-bounded-reconstruction)
          (:instance poly-remainder-canonical-lower-degree
                     (dividend candidate-remainder)))
    :in-theory (enable poly-congruent-p))))

(verify-guards poly-congruent-p)

; Focused generic structural regressions use the constrained field itself. All
; expected values are structural constant-first polynomials; no evaluation
; equality or concrete reduction API is involved.
(defthm poly-remainder-regression-bounded-reconstruction-exact
 (equal (poly-remainder (poly-mul (polynomial-one)
                                  (monomial (gfield::field-one) 1))
                        (monomial (gfield::field-one) 1))
        nil))
(defthm poly-remainder-regression-bounded-reconstruction-constant
 (equal (poly-remainder
         (poly-add (monomial (gfield::field-one) 1) (polynomial-one))
         (monomial (gfield::field-one) 1))
        (polynomial-one)))
(defthm poly-remainder-regression-bounded-reconstruction-nonconstant
 (equal (poly-remainder
         (poly-add (monomial (gfield::field-one) 2)
                   (poly-add (monomial (gfield::field-one) 1)
                             (polynomial-one)))
         (monomial (gfield::field-one) 2))
        (poly-add (monomial (gfield::field-one) 1) (polynomial-one))))
(defthm poly-remainder-regression-bounded-reconstruction-zero-quotient
 (equal (poly-remainder (polynomial-one)
                        (monomial (gfield::field-one) 1))
        (polynomial-one)))
(defthm poly-congruent-regression-reflexive
 (poly-congruent-p (polynomial-one) (polynomial-one)
                   (monomial (gfield::field-one) 1)))
(defthm poly-congruent-regression-symmetric
 (equal (poly-congruent-p (polynomial-one) nil
                          (monomial (gfield::field-one) 1))
        (poly-congruent-p nil (polynomial-one)
                          (monomial (gfield::field-one) 1))))
(defthm poly-congruent-regression-transitive
 (implies (and (poly-congruent-p x y modulus)
               (poly-congruent-p y z modulus))
          (poly-congruent-p x z modulus)))
(defthm poly-congruent-regression-equal-noncanonical
 (poly-congruent-p
  (list (gfield::field-one) (gfield::field-zero))
  (polynomial-one) (monomial (gfield::field-one) 1)))
(defthm poly-congruent-regression-normalize-left
 (equal (poly-congruent-p (normalize x) y modulus)
        (poly-congruent-p x y modulus)))
(defthm poly-congruent-regression-normalize-right
 (equal (poly-congruent-p x (normalize y) modulus)
        (poly-congruent-p x y modulus)))
(defthm poly-congruent-regression-normalize-modulus
 (equal (poly-congruent-p x y (normalize modulus))
        (poly-congruent-p x y modulus)))
(defthm poly-congruent-regression-one-modulus-multiple
 (poly-congruent-p
  (poly-add (polynomial-one) (monomial (gfield::field-one) 1))
  (polynomial-one) (monomial (gfield::field-one) 1)))
(defthm poly-congruent-regression-polynomial-multiplier
 (poly-congruent-p
  (poly-add
   (polynomial-one)
   (poly-mul (poly-add (monomial (gfield::field-one) 1)
                       (polynomial-one))
             (monomial (gfield::field-one) 2)))
  (polynomial-one) (monomial (gfield::field-one) 2)))
(defthm poly-congruent-regression-malformed-atom
 (poly-congruent-p 'malformed-operand nil (polynomial-one)))
(defthm poly-congruent-regression-trailing-zeros
 (poly-congruent-p
  (list (gfield::field-one) (gfield::field-zero)
        (gfield::field-zero))
  (polynomial-one) (monomial (gfield::field-one) 1)))
(defthm poly-congruent-regression-to-remainder
 (poly-congruent-p
  (poly-add (monomial (gfield::field-one) 1) (polynomial-one))
  (polynomial-one) (monomial (gfield::field-one) 1)))
(defthm poly-congruent-regression-unequal-bounded-representatives
 (not (poly-congruent-p nil (polynomial-one)
                        (monomial (gfield::field-one) 1))))
(defthm poly-congruent-regression-zero-modulus-normalized-equality
 (and (poly-congruent-p
       (list (gfield::field-one) (gfield::field-zero))
       (polynomial-one) nil)
      (not (poly-congruent-p nil (polynomial-one) nil))))
(defthm poly-remainder-regression-exact-divisibility
 (equal (poly-remainder (monomial (gfield::field-one) 2)
                        (polynomial-one))
        nil))
(defthm poly-remainder-regression-nonzero-lower-degree
 (equal (poly-remainder
         (poly-add (monomial (gfield::field-one) 1) (polynomial-one))
         (monomial (gfield::field-one) 1))
        (polynomial-one)))
(defthm poly-remainder-regression-dividend-below-degree
 (equal (poly-remainder (polynomial-one)
                        (monomial (gfield::field-one) 1))
        (polynomial-one)))
(defthm poly-remainder-regression-zero-dividend (equal (poly-remainder nil (polynomial-one)) nil))
(defthm poly-remainder-regression-noncanonical-dividend-and-zero-modulus
 (equal (poly-remainder
         (list 'malformed-coefficient (gfield::field-one) (gfield::field-zero))
         nil)
        (list (gfield::field-fix 'malformed-coefficient)
              (gfield::field-one))))
(defthm poly-remainder-regression-noncanonical-modulus
 (equal (poly-remainder
         (polynomial-one)
         (list 'malformed-coefficient (gfield::field-one)
               (gfield::field-zero)))
        (polynomial-one)))
(defthm poly-remainder-regression-trailing-zeros
 (equal (poly-remainder
         (list (gfield::field-one) (gfield::field-zero)
               (gfield::field-zero))
         (list (gfield::field-one) (gfield::field-one)
               (gfield::field-zero)))
        (polynomial-one)))
(defthm poly-remainder-regression-malformed-dividend (equal (poly-remainder 'malformed-dividend (polynomial-one)) nil))
(defthm poly-remainder-regression-malformed-modulus
 (equal (poly-remainder (list (gfield::field-one) (gfield::field-zero))
                        'malformed-modulus)
        (polynomial-one)))
(defthm poly-remainder-regression-normalization-invariance
 (equal (poly-remainder
         (normalize (list (gfield::field-one) (gfield::field-zero)))
         (list (gfield::field-one) (gfield::field-one)
               (gfield::field-zero)))
        (poly-remainder
         (list (gfield::field-one) (gfield::field-zero))
         (normalize (list (gfield::field-one) (gfield::field-one)
                          (gfield::field-zero))))))
(defthm poly-remainder-regression-idempotence
 (equal (poly-remainder
         (poly-remainder
          (poly-add (monomial (gfield::field-one) 1) (polynomial-one))
          (monomial (gfield::field-one) 1))
         (monomial (gfield::field-one) 1))
        (polynomial-one)))
(defthm poly-remainder-regression-strict-degree-decrease
 (< (poly-degree
     (poly-remainder
      (poly-add (monomial (gfield::field-one) 1) (polynomial-one))
      (monomial (gfield::field-one) 1)))
    (poly-degree (monomial (gfield::field-one) 1))))
