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

; Reassociate the certified division reconstruction through one addition.
; This is not a rewrite rule because the quotient-bearing form expands terms.
(defthm poly-add-left-remainder-reconstruction
  (equal
   (poly-add left right)
   (poly-add
    (poly-add (poly-remainder left modulus) right)
    (poly-mul (mv-nth 0 (poly-divmod left modulus))
              (normalize modulus))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-divmod-reconstruction (f left) (g modulus))
          (:instance poly-remainder-is-divmod-remainder
                     (dividend left) (modulus modulus))
          (:instance poly-add-associative
                     (x (poly-mul (mv-nth 0 (poly-divmod left modulus))
                                  (normalize modulus)))
                     (y (poly-remainder left modulus))
                     (z (normalize right)))
          (:instance poly-add-associative
                     (x (poly-remainder left modulus))
                     (y (normalize right))
                     (z (poly-mul (mv-nth 0 (poly-divmod left modulus))
                                  (normalize modulus))))
          (:instance poly-add-commutative
                     (x (poly-mul (mv-nth 0 (poly-divmod left modulus))
                                  (normalize modulus)))
                     (y (poly-add (poly-remainder left modulus)
                                  (normalize right)))))
    :in-theory
    (e/d (poly-add)
         (poly-divmod poly-remainder normalize poly-mul
          poly-add-associative poly-add-commutative
          poly-add-normalize-left poly-add-normalize-right
          canonical-polynomial-p polynomial-p)))))

(defthm poly-remainder-of-poly-add-remainder-left
  (equal
   (poly-remainder (poly-add left right) modulus)
   (poly-remainder
    (poly-add (poly-remainder left modulus) right)
    modulus))
  :rule-classes nil
  :hints
  (("Goal" :cases ((consp (normalize modulus))))
   ("Subgoal 1"
    :use ((:instance poly-add-left-remainder-reconstruction)
          (:instance poly-remainder-of-poly-add-modulus-multiple
                     (dividend
                      (poly-add (poly-remainder left modulus) right))
                     (multiplier
                      (mv-nth 0 (poly-divmod left modulus)))))
    :in-theory (disable poly-divmod poly-remainder poly-add poly-mul normalize))
   ("Subgoal 2"
    :use ((:instance poly-remainder-zero-normalized-modulus
                     (dividend (poly-add left right)))
          (:instance poly-remainder-zero-normalized-modulus
                     (dividend
                      (poly-add (poly-remainder left modulus) right)))
          (:instance poly-remainder-zero-normalized-modulus
                     (dividend left)))
    :in-theory (e/d (poly-add)
                    (poly-remainder normalize raw-add)))))

(defthm poly-remainder-of-poly-add-remainder-right
  (equal
   (poly-remainder (poly-add left right) modulus)
   (poly-remainder
    (poly-add left (poly-remainder right modulus))
    modulus))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-remainder-of-poly-add-remainder-left
                            (left right) (right left))
                 (:instance poly-add-commutative (x left) (y right))
                 (:instance poly-add-commutative
                            (x (poly-remainder right modulus)) (y left)))
           :in-theory (disable poly-remainder poly-add
                               poly-add-commutative))))

(defthm poly-remainder-of-poly-add-remainders
  (equal
   (poly-remainder (poly-add left right) modulus)
   (poly-remainder
    (poly-add (poly-remainder left modulus)
              (poly-remainder right modulus))
    modulus))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-remainder-of-poly-add-remainder-left)
          (:instance poly-remainder-of-poly-add-remainder-right
                     (left (poly-remainder left modulus))))
    :in-theory (disable poly-remainder poly-add))))

(defthm poly-congruent-p-of-poly-add
  (implies
   (and (poly-congruent-p left-a left-b modulus)
        (poly-congruent-p right-a right-b modulus))
   (poly-congruent-p (poly-add left-a right-a)
                     (poly-add left-b right-b)
                     modulus))
  :hints
  (("Goal"
    :use ((:instance poly-congruent-p-iff-equal-remainders
                     (left left-a) (right left-b))
          (:instance poly-congruent-p-iff-equal-remainders
                     (left right-a) (right right-b))
          (:instance poly-remainder-of-poly-add-remainders
                     (left left-a) (right right-a))
          (:instance poly-remainder-of-poly-add-remainders
                     (left left-b) (right right-b)))
    :in-theory (enable poly-congruent-p))))

(defthm poly-congruent-p-of-poly-add-same-right
  (implies (poly-congruent-p left-a left-b modulus)
           (poly-congruent-p (poly-add left-a right)
                             (poly-add left-b right)
                             modulus))
  :hints (("Goal" :use ((:instance poly-congruent-p-of-poly-add
                                   (right-a right) (right-b right))))))

(defthm poly-congruent-p-of-poly-add-same-left
  (implies (poly-congruent-p right-a right-b modulus)
           (poly-congruent-p (poly-add left right-a)
                             (poly-add left right-b)
                             modulus))
  :hints (("Goal" :use ((:instance poly-congruent-p-of-poly-add
                     (left-a left) (left-b left))))))

; Multiplying the certified reconstruction of LEFT by RIGHT leaves the
; remainder product in the same coset.  This expansionary algebraic shape is
; kept out of rewriting and used only by the multiplication reduction laws.
(defthm normalize-of-poly-mul-reconstruction-left
  (equal
   (normalize (poly-mul left right))
   (poly-add
    (poly-mul (poly-remainder left modulus) right)
    (poly-mul
     (poly-mul (mv-nth 0 (poly-divmod left modulus)) right)
     (normalize modulus))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-divmod-reconstruction (f left) (g modulus))
          (:instance poly-remainder-is-divmod-remainder
                     (dividend left) (modulus modulus))
          (:instance poly-mul-right-distributive
                     (x (poly-mul (mv-nth 0 (poly-divmod left modulus))
                                  (normalize modulus)))
                     (y (poly-remainder left modulus))
                     (z right))
          (:instance poly-mul-associative
                     (x (mv-nth 0 (poly-divmod left modulus)))
                     (y (normalize modulus)) (z right))
          (:instance poly-mul-associative
                     (x (mv-nth 0 (poly-divmod left modulus)))
                     (y right) (z (normalize modulus)))
          (:instance poly-mul-commutative
                     (x (normalize modulus)) (y right))
          (:instance poly-add-commutative
                     (x (poly-mul
                         (mv-nth 0 (poly-divmod left modulus))
                         (poly-mul (normalize modulus) right)))
                     (y (poly-mul (poly-remainder left modulus) right)))
          (:instance poly-mul-normalize-left (x left) (y right))
          (:instance normalize-when-canonical
                     (xs (poly-mul left right))))
    :in-theory
    (disable poly-divmod poly-remainder normalize poly-add poly-mul
             canonical-polynomial-p))))

(defthm poly-remainder-of-poly-mul-remainder-left
  (equal
   (poly-remainder (poly-mul left right) modulus)
   (poly-remainder
    (poly-mul (poly-remainder left modulus) right) modulus))
  :rule-classes nil
  :hints
  (("Goal" :cases ((consp (normalize modulus))))
   ("Subgoal 1"
    :use ((:instance normalize-of-poly-mul-reconstruction-left)
          (:instance poly-remainder-of-normalize-dividend
                     (dividend (poly-mul left right)))
          (:instance poly-remainder-of-normalize-dividend
                     (dividend
                      (poly-add
                       (poly-mul (poly-remainder left modulus) right)
                       (poly-mul
                        (poly-mul
                         (mv-nth 0 (poly-divmod left modulus)) right)
                        (normalize modulus)))))
          (:instance poly-remainder-of-poly-add-modulus-multiple
                     (dividend
                      (poly-mul (poly-remainder left modulus) right))
                     (multiplier
                      (poly-mul (mv-nth 0 (poly-divmod left modulus))
                                right))))
    :in-theory (disable poly-divmod poly-remainder normalize poly-add poly-mul))
   ("Subgoal 2"
    :use ((:instance poly-remainder-zero-normalized-modulus
                     (dividend (poly-mul left right)))
          (:instance poly-remainder-zero-normalized-modulus
                     (dividend
                      (poly-mul (poly-remainder left modulus) right)))
          (:instance poly-remainder-zero-normalized-modulus
                     (dividend left))
          (:instance poly-mul-normalize-left (x left) (y right)))
    :in-theory (disable poly-remainder normalize poly-mul))))

(defthm poly-remainder-of-poly-mul-remainder-right
  (equal
   (poly-remainder (poly-mul left right) modulus)
   (poly-remainder
    (poly-mul left (poly-remainder right modulus)) modulus))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-remainder-of-poly-mul-remainder-left
                            (left right) (right left))
                 (:instance poly-mul-commutative (x left) (y right))
                 (:instance poly-mul-commutative
                            (x (poly-remainder right modulus)) (y left)))
           :in-theory (disable poly-remainder poly-mul))))

(defthm poly-remainder-of-poly-mul-remainders
  (equal
   (poly-remainder (poly-mul left right) modulus)
   (poly-remainder
    (poly-mul (poly-remainder left modulus)
              (poly-remainder right modulus))
    modulus))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-remainder-of-poly-mul-remainder-left)
                 (:instance poly-remainder-of-poly-mul-remainder-right
                            (left (poly-remainder left modulus))))
           :in-theory (disable poly-remainder poly-mul))))

(defthm poly-congruent-p-of-poly-mul
  (implies
   (and (poly-congruent-p left-a left-b modulus)
        (poly-congruent-p right-a right-b modulus))
   (poly-congruent-p (poly-mul left-a right-a)
                     (poly-mul left-b right-b)
                     modulus))
  :hints
  (("Goal"
    :use ((:instance poly-congruent-p-iff-equal-remainders
                     (left left-a) (right left-b))
          (:instance poly-congruent-p-iff-equal-remainders
                     (left right-a) (right right-b))
          (:instance poly-remainder-of-poly-mul-remainders
                     (left left-a) (right right-a))
          (:instance poly-remainder-of-poly-mul-remainders
                     (left left-b) (right right-b)))
    :in-theory (enable poly-congruent-p))))

(defthm poly-congruent-p-of-poly-mul-same-right
  (implies (poly-congruent-p left-a left-b modulus)
           (poly-congruent-p (poly-mul left-a right)
                             (poly-mul left-b right) modulus))
  :hints (("Goal" :use ((:instance poly-congruent-p-of-poly-mul
                                   (right-a right) (right-b right))))))

(defthm poly-congruent-p-of-poly-mul-same-left
  (implies (poly-congruent-p right-a right-b modulus)
           (poly-congruent-p (poly-mul left right-a)
                             (poly-mul left right-b) modulus))
  :hints (("Goal" :use ((:instance poly-congruent-p-of-poly-mul
                                   (left-a left) (left-b left))))))

(defthm poly-mul-poly-congruent-p-with-remainders
  (poly-congruent-p
   (poly-mul left right)
   (poly-mul (poly-remainder left modulus)
             (poly-remainder right modulus))
   modulus)
  :hints (("Goal"
           :use ((:instance poly-remainder-of-poly-mul-remainders))
           :in-theory (enable poly-congruent-p))))

(defthm poly-neg-of-poly-add
  (implies (and (polynomial-p x) (polynomial-p y))
           (equal (poly-neg (poly-add x y))
                  (poly-add (poly-neg x) (poly-neg y))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-add-left-cancel-canonical
                     (z (poly-add x y))
                     (x (poly-neg (poly-add x y)))
                     (y (poly-add (poly-neg x) (poly-neg y))))
          (:instance poly-add-inverse-right (x (poly-add x y)))
          (:instance poly-add-inverse-right (x x))
          (:instance poly-add-inverse-right (x y))
          (:instance poly-add-associative
                     (x x) (y y)
                     (z (poly-add (poly-neg x) (poly-neg y))))
          (:instance poly-add-associative
                     (x y) (y (poly-neg x)) (z (poly-neg y)))
          (:instance poly-add-associative
                     (x (poly-neg x)) (y y) (z (poly-neg y)))
          (:instance poly-add-associative
                     (x x) (y (poly-neg x))
                     (z (poly-add y (poly-neg y))))
          (:instance poly-add-commutative (x y) (y (poly-neg x)))
          (:instance poly-add-zero-right (x (poly-neg x))))
    :in-theory (disable poly-add poly-neg poly-add-associative
                        poly-add-commutative canonical-polynomial-p
                        polynomial-p))))

(defthm poly-neg-remainder-reconstruction
  (equal
   (poly-neg polynomial)
   (poly-add
    (poly-neg (poly-remainder polynomial modulus))
    (poly-mul (poly-neg (mv-nth 0 (poly-divmod polynomial modulus)))
              (normalize modulus))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-divmod-reconstruction
                     (f polynomial) (g modulus))
          (:instance poly-remainder-is-divmod-remainder
                     (dividend polynomial) (modulus modulus))
          (:instance poly-neg-of-poly-add
                     (x (poly-mul
                         (mv-nth 0 (poly-divmod polynomial modulus))
                         (normalize modulus)))
                     (y (poly-remainder polynomial modulus)))
          (:instance poly-mul-of-poly-neg-left
                     (x (mv-nth 0 (poly-divmod polynomial modulus)))
                     (y (normalize modulus)))
          (:instance poly-add-commutative
                     (x (poly-neg
                         (poly-mul
                          (mv-nth 0 (poly-divmod polynomial modulus))
                          (normalize modulus))))
                     (y (poly-neg (poly-remainder polynomial modulus)))))
    :in-theory
    (disable poly-divmod poly-remainder normalize poly-add poly-neg poly-mul
             poly-add-commutative))))

(defthm poly-remainder-of-poly-neg-remainder
  (equal
   (poly-remainder (poly-neg polynomial) modulus)
   (poly-remainder
    (poly-neg (poly-remainder polynomial modulus))
    modulus))
  :rule-classes nil
  :hints
  (("Goal" :cases ((consp (normalize modulus))))
   ("Subgoal 1"
    :use ((:instance poly-neg-remainder-reconstruction)
          (:instance poly-remainder-of-poly-add-modulus-multiple
                     (dividend
                      (poly-neg (poly-remainder polynomial modulus)))
                     (multiplier
                      (poly-neg
                       (mv-nth 0 (poly-divmod polynomial modulus))))))
    :in-theory (disable poly-divmod poly-remainder poly-add poly-neg poly-mul
                        normalize))
   ("Subgoal 2"
    :use ((:instance poly-remainder-zero-normalized-modulus
                     (dividend (poly-neg polynomial)))
          (:instance poly-remainder-zero-normalized-modulus
                     (dividend polynomial))
          (:instance poly-remainder-zero-normalized-modulus
                     (dividend
                      (poly-neg (poly-remainder polynomial modulus)))))
    :in-theory (disable poly-remainder poly-neg normalize))))

(defthm poly-congruent-p-of-poly-neg
  (implies (poly-congruent-p left right modulus)
           (poly-congruent-p (poly-neg left) (poly-neg right) modulus))
  :hints
  (("Goal"
    :use ((:instance poly-congruent-p-iff-equal-remainders)
          (:instance poly-remainder-of-poly-neg-remainder
                     (polynomial left))
          (:instance poly-remainder-of-poly-neg-remainder
                     (polynomial right)))
    :in-theory (enable poly-congruent-p))))

(defthm poly-remainder-of-poly-sub-remainders
  (equal
   (poly-remainder (poly-sub left right) modulus)
   (poly-remainder
    (poly-sub (poly-remainder left modulus)
              (poly-remainder right modulus))
    modulus))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-remainder-of-poly-add-remainders
                     (right (poly-neg right)))
          (:instance poly-remainder-of-poly-neg-remainder
                     (polynomial right))
          (:instance poly-remainder-of-poly-add-remainder-right
                     (left (poly-remainder left modulus))
                     (right
                      (poly-neg (poly-remainder right modulus)))))
    :in-theory (e/d (poly-sub-definition)
                    (poly-remainder poly-add poly-neg poly-sub
                     poly-add-commutative)))))

(defthm poly-congruent-p-of-poly-sub
  (implies
   (and (poly-congruent-p left-a left-b modulus)
        (poly-congruent-p right-a right-b modulus))
   (poly-congruent-p (poly-sub left-a right-a)
                     (poly-sub left-b right-b)
                     modulus))
  :hints
  (("Goal"
    :use ((:instance poly-congruent-p-of-poly-add
                     (right-a (poly-neg right-a))
                     (right-b (poly-neg right-b)))
          (:instance poly-congruent-p-of-poly-neg
                     (left right-a) (right right-b)))
    :in-theory (e/d (poly-sub-definition) (poly-add poly-neg poly-sub)))))

(defthm poly-add-poly-congruent-p-with-remainders
  (poly-congruent-p
   (poly-add left right)
   (poly-add (poly-remainder left modulus)
             (poly-remainder right modulus))
   modulus)
  :hints (("Goal"
           :use ((:instance poly-remainder-of-poly-add-remainders))
           :in-theory (enable poly-congruent-p))))

(defthm poly-neg-poly-congruent-p-with-remainder
  (poly-congruent-p
   (poly-neg polynomial)
   (poly-neg (poly-remainder polynomial modulus))
   modulus)
  :hints (("Goal"
           :use ((:instance poly-remainder-of-poly-neg-remainder))
           :in-theory (enable poly-congruent-p))))

(defthm poly-sub-poly-congruent-p-with-remainders
  (poly-congruent-p
   (poly-sub left right)
   (poly-sub (poly-remainder left modulus)
             (poly-remainder right modulus))
   modulus)
  :hints (("Goal"
           :use ((:instance poly-remainder-of-poly-sub-remainders))
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
(defthm poly-congruent-regression-add-two-pairs
 (implies
  (and (poly-congruent-p left-a left-b modulus)
       (poly-congruent-p right-a right-b modulus))
  (poly-congruent-p (poly-add left-a right-a)
                    (poly-add left-b right-b) modulus))
 :hints (("Goal" :by poly-congruent-p-of-poly-add)))
(defthm poly-congruent-regression-add-same-right
 (implies (poly-congruent-p left-a left-b modulus)
          (poly-congruent-p (poly-add left-a right)
                            (poly-add left-b right) modulus))
 :hints (("Goal" :by poly-congruent-p-of-poly-add-same-right)))
(defthm poly-congruent-regression-add-trailing-zeros
 (implies
  (poly-congruent-p
   (list (gfield::field-one) (gfield::field-zero))
   (polynomial-one) modulus)
  (poly-congruent-p
   (poly-add (list (gfield::field-one) (gfield::field-zero)) right)
   (poly-add (polynomial-one) right) modulus))
 :hints (("Goal" :by poly-congruent-p-of-poly-add-same-right)))
(defthm poly-congruent-regression-add-noncanonical-coefficient
 (poly-congruent-p
  (poly-add (list coefficient) right)
  (poly-add (normalize (list coefficient)) right) modulus)
 :hints (("Goal"
          :use ((:instance poly-congruent-p-of-poly-add-same-right
                           (left-a (list coefficient))
                           (left-b (normalize (list coefficient))))
                (:instance poly-congruent-p-of-normalize-left
                           (left (list coefficient))
                           (right (normalize (list coefficient)))))
          :in-theory (disable poly-add poly-congruent-p))))
(defthm poly-congruent-regression-neg
 (implies (poly-congruent-p left right modulus)
          (poly-congruent-p (poly-neg left) (poly-neg right) modulus))
 :hints (("Goal" :by poly-congruent-p-of-poly-neg)))
(defthm poly-congruent-regression-double-neg
 (poly-congruent-p
  (poly-neg (poly-neg (normalize polynomial))) polynomial modulus)
 :hints (("Goal"
          :use ((:instance poly-congruent-p-of-normalize-left
                           (left polynomial) (right polynomial))
                (:instance poly-neg-double-canonical
                           (x (normalize polynomial))))
          :in-theory (disable poly-congruent-p poly-neg))))
(defthm poly-congruent-regression-sub-two-pairs
 (implies
  (and (poly-congruent-p left-a left-b modulus)
       (poly-congruent-p right-a right-b modulus))
  (poly-congruent-p (poly-sub left-a right-a)
                    (poly-sub left-b right-b) modulus))
 :hints (("Goal" :by poly-congruent-p-of-poly-sub)))
(defthm poly-congruent-regression-sub-zero
 (equal (poly-sub (polynomial-one) (polynomial-one)) nil))
(defthm poly-congruent-regression-add-malformed-atoms
 (poly-congruent-p (poly-add 'bad-left 'bad-right)
                   (poly-add nil nil) modulus))
(defthm poly-congruent-regression-add-remainders
 (poly-congruent-p
  (poly-add x y)
  (poly-add (poly-remainder x modulus) (poly-remainder y modulus))
  modulus)
 :hints (("Goal" :by poly-add-poly-congruent-p-with-remainders)))
(defthm poly-congruent-regression-neg-remainder
 (poly-congruent-p
  (poly-neg x) (poly-neg (poly-remainder x modulus)) modulus)
 :hints (("Goal" :by poly-neg-poly-congruent-p-with-remainder)))
(defthm poly-congruent-regression-sub-remainders
 (poly-congruent-p
  (poly-sub x y)
  (poly-sub (poly-remainder x modulus) (poly-remainder y modulus)) modulus)
 :hints (("Goal" :by poly-sub-poly-congruent-p-with-remainders)))
(defthm poly-congruent-regression-zero-modulus-add
 (implies (equal (normalize left) (normalize right))
          (poly-congruent-p (poly-add left addend)
                            (poly-add right addend) nil))
 :hints (("Goal"
          :use ((:instance poly-congruent-p-of-poly-add-same-right
                           (left-a left) (left-b right)
                           (right addend) (modulus nil)))
          :in-theory (disable poly-add poly-congruent-p))))
(defthm poly-congruent-regression-zero-modulus-neg
 (implies (equal (normalize left) (normalize right))
          (poly-congruent-p (poly-neg left) (poly-neg right) nil))
 :hints (("Goal"
          :use ((:instance poly-congruent-p-of-poly-neg
                           (modulus nil)))
          :in-theory (disable poly-neg poly-congruent-p))))
(defthm poly-congruent-regression-zero-modulus-sub
 (implies (and (equal (normalize left-a) (normalize left-b))
               (equal (normalize right-a) (normalize right-b)))
          (poly-congruent-p (poly-sub left-a right-a)
                            (poly-sub left-b right-b) nil))
 :hints (("Goal"
          :use ((:instance poly-congruent-p-of-poly-sub (modulus nil)))
          :in-theory (disable poly-sub poly-congruent-p))))
(defthm poly-congruent-regression-add-negative-bounded
 (not (poly-congruent-p (poly-add nil (polynomial-one))
                        (poly-add nil nil)
                        (monomial (gfield::field-one) 1))))
(defthm poly-congruent-regression-mul-two-pairs
 (implies
  (and (poly-congruent-p left-a left-b modulus)
       (poly-congruent-p right-a right-b modulus))
  (poly-congruent-p (poly-mul left-a right-a)
                    (poly-mul left-b right-b) modulus))
 :hints (("Goal" :by poly-congruent-p-of-poly-mul)))
(defthm poly-congruent-regression-mul-same-right
 (implies (poly-congruent-p left-a left-b modulus)
          (poly-congruent-p (poly-mul left-a right)
                            (poly-mul left-b right) modulus))
 :hints (("Goal" :by poly-congruent-p-of-poly-mul-same-right)))
(defthm poly-congruent-regression-mul-same-left
 (implies (poly-congruent-p right-a right-b modulus)
          (poly-congruent-p (poly-mul left right-a)
                            (poly-mul left right-b) modulus))
 :hints (("Goal" :by poly-congruent-p-of-poly-mul-same-left)))
(defthm poly-congruent-regression-mul-remainders
 (poly-congruent-p
  (poly-mul left right)
  (poly-mul (poly-remainder left modulus)
            (poly-remainder right modulus)) modulus)
 :hints (("Goal" :by poly-mul-poly-congruent-p-with-remainders)))
(defthm poly-congruent-regression-mul-modulus-multiple
 (poly-congruent-p
  (poly-mul
   (poly-add (polynomial-one)
             (poly-mul multiplier (normalize modulus)))
   right)
  (poly-mul (polynomial-one) right) modulus)
 :hints (("Goal"
          :use ((:instance poly-congruent-p-of-poly-mul-same-right
                           (left-a
                            (poly-add
                             (polynomial-one)
                             (poly-mul multiplier (normalize modulus))))
                           (left-b (polynomial-one)))
                (:instance poly-add-modulus-multiple-poly-congruent-p
                           (dividend (polynomial-one))))
          :in-theory (disable poly-mul poly-add poly-congruent-p))))
(defthm poly-congruent-regression-mul-trailing-zeros
 (poly-congruent-p
  (poly-mul (list (gfield::field-one) (gfield::field-zero)) right)
  (poly-mul (polynomial-one) right) modulus))
(defthm poly-congruent-regression-mul-noncanonical-coefficient
 (poly-congruent-p
  (poly-mul (list coefficient) right)
  (poly-mul (normalize (list coefficient)) right) modulus))
(defthm poly-congruent-regression-mul-zero
 (and (poly-congruent-p (poly-mul left nil) nil modulus)
      (poly-congruent-p (poly-mul nil right) nil modulus)))
(defthm poly-congruent-regression-mul-one
 (poly-congruent-p (poly-mul left (polynomial-one)) left modulus))
(defthm poly-congruent-regression-mul-malformed-atoms
 (poly-congruent-p (poly-mul 'bad-left 'bad-right) nil modulus))
(defthm poly-congruent-regression-zero-modulus-mul
 (implies (and (equal (normalize left-a) (normalize left-b))
               (equal (normalize right-a) (normalize right-b)))
          (poly-congruent-p (poly-mul left-a right-a)
                            (poly-mul left-b right-b) nil))
 :hints (("Goal"
          :use ((:instance poly-congruent-p-of-poly-mul (modulus nil)))
          :in-theory (disable poly-mul poly-congruent-p))))
(defthm poly-congruent-regression-mul-negative-bounded
 (not (poly-congruent-p (poly-mul (polynomial-one) (polynomial-one))
                        (poly-mul nil (polynomial-one))
                        (monomial (gfield::field-one) 1))))
(defthm poly-congruent-regression-mul-no-cancellation
 (and (not (poly-congruent-p nil (polynomial-one)
                             (monomial (gfield::field-one) 1)))
      (poly-congruent-p (poly-mul nil nil)
                        (poly-mul (polynomial-one) nil)
                        (monomial (gfield::field-one) 1))))
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
