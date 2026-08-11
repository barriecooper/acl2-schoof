(in-package "GPOLY")

(include-book "finite-field-divmod")
(local (include-book "division"))

(local (in-theory (disable finite-field-poly-divmod-core
                           finite-field-poly-divmod
                           finite-field-poly-division-step-core
                           finite-field-poly-add
                           finite-field-poly-mul
                           finite-field-poly-normalize
                           finite-field-poly-raw-add
                           finite-field-poly-raw-mul)))

(defthm finite-field-poly-remainder-canonical
  (finite-field-canonical-polynomial-p
   (finite-field-poly-remainder dividend modulus))
  :hints (("Goal" :use ((:instance finite-field-canonical-polynomial-p-of-poly-remainder
                                  (f dividend) (g modulus))))))

(defthm finite-field-poly-normalize-of-remainder
  (equal (finite-field-poly-normalize
          (finite-field-poly-remainder dividend modulus))
         (finite-field-poly-remainder dividend modulus))
  :hints (("Goal" :use ((:instance finite-field-poly-remainder-canonical)
                         (:instance finite-field-poly-normalize-when-canonical
                                  (xs (finite-field-poly-remainder dividend modulus))))
           :in-theory (disable finite-field-poly-remainder
                               finite-field-poly-normalize
                               finite-field-canonical-polynomial-p))))

(defthm finite-field-poly-remainder-of-normalize-dividend
  (equal (finite-field-poly-remainder
          (finite-field-poly-normalize dividend) modulus)
         (finite-field-poly-remainder dividend modulus))
  :hints (("Goal" :in-theory (e/d (finite-field-poly-remainder
                                    finite-field-poly-divmod)
                                   (finite-field-poly-divmod-core
                                    finite-field-poly-normalize)))))

(defthm finite-field-poly-remainder-of-normalize-modulus
  (equal (finite-field-poly-remainder
          dividend (finite-field-poly-normalize modulus))
         (finite-field-poly-remainder dividend modulus))
  :hints (("Goal" :in-theory (e/d (finite-field-poly-remainder
                                    finite-field-poly-divmod)
                                   (finite-field-poly-divmod-core
                                    finite-field-poly-normalize)))))

(defthm finite-field-poly-divmod-zero-divisor
  (equal (finite-field-poly-divmod f nil)
         (mv nil (finite-field-poly-normalize f)))
  :hints (("Goal" :in-theory (enable finite-field-poly-divmod
                                      finite-field-poly-divmod-core))))

(defthm finite-field-poly-divmod-zero-dividend
  (equal (finite-field-poly-divmod nil g) (mv nil nil))
  :hints (("Goal" :in-theory (enable finite-field-poly-divmod
                                      finite-field-poly-divmod-core
                                      finite-field-poly-normalize))))

(defthm finite-field-poly-remainder-zero-modulus
  (equal (finite-field-poly-remainder dividend nil)
         (finite-field-poly-normalize dividend))
  :hints (("Goal" :use ((:instance finite-field-poly-divmod-zero-divisor
                                  (f dividend)))
           :in-theory (enable finite-field-poly-remainder))))

(defthm finite-field-poly-normalize-equal-nil-when-not-consp
  (implies (not (consp (finite-field-poly-normalize xs)))
           (equal (finite-field-poly-normalize xs) nil))
  :hints (("Goal" :use ((:instance finite-field-canonical-polynomial-atom-is-nil
                                  (p (finite-field-poly-normalize xs)))
                         (:instance finite-field-canonical-polynomial-p-of-poly-normalize
                                  (xs xs)))
           :in-theory (disable finite-field-poly-normalize
                               finite-field-canonical-polynomial-p))))

(defthm finite-field-poly-divmod-zero-normalized-divisor
  (implies (equal (finite-field-poly-normalize g) nil)
           (equal (finite-field-poly-divmod f g)
                  (mv nil (finite-field-poly-normalize f))))
  :hints (("Goal" :in-theory (enable finite-field-poly-divmod
                                      finite-field-poly-divmod-core))))

(defthm finite-field-poly-remainder-zero-normalized-modulus
  (implies (equal (finite-field-poly-normalize modulus) nil)
           (equal (finite-field-poly-remainder dividend modulus)
                  (finite-field-poly-normalize dividend)))
  :hints (("Goal" :use ((:instance finite-field-poly-divmod-zero-normalized-divisor
                                  (f dividend) (g modulus)))
           :in-theory (disable finite-field-poly-remainder
                               finite-field-poly-normalize))))

(defthm finite-field-poly-remainder-zero-dividend
  (equal (finite-field-poly-remainder nil modulus) nil)
  :hints (("Goal" :use ((:instance finite-field-poly-divmod-zero-dividend
                                  (g modulus)))
           :in-theory (enable finite-field-poly-remainder))))


(local
 (defthm len-positive-when-consp
   (implies (consp x)
            (< 0 (len x)))))

(local
 (defthm len-not-zero-when-consp
   (implies (consp x)
            (not (equal (len x) 0)))))

(defthm finite-field-poly-remainder-strict-length-bound
  (implies (consp (finite-field-poly-normalize modulus))
           (< (len (finite-field-poly-remainder dividend modulus))
              (len (finite-field-poly-normalize modulus))))
  :rule-classes nil
  :hints (("Goal" :cases ((consp (finite-field-poly-remainder dividend modulus)))
           :use ((:instance finite-field-poly-remainder-canonical)
                 (:instance finite-field-canonical-polynomial-p-of-poly-normalize
                            (xs modulus))
                 (:instance finite-field-poly-remainder-degree-bound
                            (f dividend) (g modulus))
                 (:instance finite-field-poly-degree-when-canonical-nonzero
                            (p (finite-field-poly-remainder dividend modulus)))
                 (:instance finite-field-poly-degree-when-canonical-nonzero
                            (p (finite-field-poly-normalize modulus))))
           :in-theory (disable finite-field-poly-remainder
                               finite-field-poly-normalize
                               finite-field-poly-degree
                               finite-field-canonical-polynomial-p))))

(defthm finite-field-poly-remainder-canonical-lower-degree
  (implies (and (finite-field-canonical-polynomial-p dividend)
                (consp (finite-field-poly-normalize modulus))
                (< (finite-field-poly-degree dividend)
                   (finite-field-poly-degree
                    (finite-field-poly-normalize modulus))))
           (equal (finite-field-poly-remainder dividend modulus)
                  dividend))
  :rule-classes nil
  :hints (("Goal" :cases ((<= (finite-field-poly-degree (finite-field-poly-normalize modulus))
                                (finite-field-poly-degree dividend)))
           :use ((:instance finite-field-poly-normalize-when-canonical
                            (xs dividend))
                 (:instance finite-field-canonical-polynomial-p-of-poly-normalize
                            (xs modulus))
                 (:instance finite-field-canonical-polynomial-p-of-nil)
                 (:instance finite-field-poly-degree-when-normalize-consp
                            (poly modulus)))
           :expand ((finite-field-poly-divmod-core nil dividend (finite-field-poly-normalize modulus)))
           :in-theory (e/d (finite-field-poly-remainder
                            finite-field-poly-divmod
                            finite-field-poly-divmod-core)
                           (finite-field-poly-normalize
                            finite-field-canonical-polynomial-p
                            finite-field-poly-degree)))))

(defthm finite-field-poly-remainder-idempotent
  (equal (finite-field-poly-remainder
          (finite-field-poly-remainder dividend modulus)
          modulus)
         (finite-field-poly-remainder dividend modulus))
  :hints (("Goal" :cases ((consp (finite-field-poly-normalize modulus))))
          ("Subgoal 2"
           :use ((:instance finite-field-poly-remainder-zero-normalized-modulus)
                 (:instance finite-field-poly-remainder-zero-normalized-modulus
                            (dividend (finite-field-poly-remainder dividend modulus)))
                 (:instance finite-field-poly-normalize-when-canonical
                            (xs (finite-field-poly-remainder dividend modulus)))
                 (:instance finite-field-poly-remainder-canonical))
           :in-theory (disable finite-field-poly-remainder
                               finite-field-poly-normalize
                               finite-field-canonical-polynomial-p))
          ("Subgoal 1"
           :use ((:instance finite-field-poly-remainder-degree-bound
                            (f dividend) (g modulus))
                 (:instance finite-field-poly-remainder-canonical-lower-degree
                            (dividend (finite-field-poly-remainder dividend modulus))))
           :in-theory (disable finite-field-poly-remainder
                               finite-field-poly-normalize
                               finite-field-poly-degree
                               finite-field-canonical-polynomial-p))))

(defund finite-field-poly-reduced-p (polynomial modulus)
  (declare (xargs :guard t))
  (equal (finite-field-poly-remainder polynomial modulus)
         polynomial))

(defthm finite-field-poly-reduced-p-definition
  (equal (finite-field-poly-reduced-p polynomial modulus)
         (equal (finite-field-poly-remainder polynomial modulus)
                polynomial))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable finite-field-poly-reduced-p))))

(defthm finite-field-poly-reduced-p-of-remainder
  (finite-field-poly-reduced-p
   (finite-field-poly-remainder polynomial modulus) modulus)
  :hints (("Goal" :use ((:instance finite-field-poly-reduced-p-definition
                                  (polynomial (finite-field-poly-remainder
                                               polynomial modulus)))
                         (:instance finite-field-poly-remainder-idempotent
                                  (dividend polynomial)))
           :in-theory (disable finite-field-poly-reduced-p
                               finite-field-poly-remainder))))

(defthm finite-field-poly-remainder-when-reduced-p
  (implies (finite-field-poly-reduced-p polynomial modulus)
           (equal (finite-field-poly-remainder polynomial modulus)
                  polynomial))
  :hints (("Goal" :use ((:instance finite-field-poly-reduced-p-definition))
           :in-theory (disable finite-field-poly-reduced-p))))

(defthm finite-field-poly-reduced-p-iff-canonical-and-degree-bounded
  (implies
   (consp (finite-field-poly-normalize modulus))
   (equal
    (finite-field-poly-reduced-p polynomial modulus)
    (and (finite-field-canonical-polynomial-p polynomial)
         (or (equal polynomial nil)
             (< (finite-field-poly-degree polynomial)
                (finite-field-poly-degree
                 (finite-field-poly-normalize modulus)))))))
  :rule-classes nil
  :hints (("Goal" :cases ((<= (finite-field-poly-degree (finite-field-poly-normalize modulus))
                                (finite-field-poly-degree polynomial)))
           :use ((:instance finite-field-poly-reduced-p-definition)
                 (:instance finite-field-poly-remainder-canonical
                            (dividend polynomial))
                 (:instance finite-field-poly-remainder-degree-bound
                            (f polynomial) (g modulus))
                 (:instance finite-field-poly-remainder-canonical-lower-degree
                            (dividend polynomial)))
           :in-theory (disable finite-field-poly-reduced-p
                               finite-field-poly-remainder
                               finite-field-poly-normalize
                               finite-field-canonical-polynomial-p
                               finite-field-poly-degree))))

(verify-guards finite-field-poly-reduced-p)

; Subtraction cannot create a term above either canonical operand.  This is
; the finite-field-prefixed degree fact needed for same-coset uniqueness.
(defthm finite-field-poly-sub-degree-below-common-bound
  (implies
   (and (finite-field-canonical-polynomial-p x)
        (finite-field-canonical-polynomial-p y)
        (or (not (consp x))
            (< (finite-field-poly-degree x) bound))
        (or (not (consp y))
            (< (finite-field-poly-degree y) bound)))
   (or (equal (finite-field-poly-sub x y) nil)
       (< (finite-field-poly-degree
           (finite-field-poly-sub x y))
          bound)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-sub-of-canonical-operands)
          (:instance finite-field-len-of-poly-normalize
                     (xs (finite-field-poly-raw-add
                          x (finite-field-poly-raw-neg y))))
          (:instance finite-field-len-of-poly-raw-add
                     (x x) (y (finite-field-poly-raw-neg y)))
          (:instance finite-field-len-of-poly-raw-neg (x y))
          (:instance finite-field-poly-degree-when-canonical-nonzero
                     (p (finite-field-poly-sub x y)))
          (:instance finite-field-canonical-polynomial-atom-is-nil (p x))
          (:instance finite-field-canonical-polynomial-atom-is-nil (p y)))
    :in-theory
    (disable finite-field-poly-sub finite-field-poly-raw-add
          finite-field-poly-raw-neg finite-field-poly-normalize
          finite-field-canonical-polynomial-p finite-field-poly-degree))))

(defthm finite-field-poly-add-left-cancel-canonical
  (implies
   (and (finite-field-canonical-polynomial-p x)
        (finite-field-canonical-polynomial-p y)
        (finite-field-polynomial-p z)
        (equal (finite-field-poly-add z x)
               (finite-field-poly-add z y)))
   (equal x y))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-add-associative
                     (x (finite-field-poly-neg z)) (y z) (z x))
          (:instance finite-field-poly-add-associative
                     (x (finite-field-poly-neg z)) (y z) (z y))
          (:instance finite-field-poly-add-commutative
                     (x (finite-field-poly-neg z)) (y z))
          (:instance finite-field-poly-add-inverse-right (x z)))
    :in-theory
    (disable finite-field-poly-add
     finite-field-poly-neg finite-field-canonical-polynomial-p))))

(defthm finite-field-poly-mul-of-poly-neg-left
  (implies (finite-field-polynomial-p x)
           (equal (finite-field-poly-mul (finite-field-poly-neg x) y)
                  (finite-field-poly-neg (finite-field-poly-mul x y))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-add-left-cancel-canonical
                     (z (finite-field-poly-mul x y))
                     (x (finite-field-poly-mul (finite-field-poly-neg x) y))
                     (y (finite-field-poly-neg (finite-field-poly-mul x y))))
          (:instance finite-field-poly-mul-right-distributive
                     (x x) (y (finite-field-poly-neg x)) (z y))
          (:instance finite-field-poly-add-inverse-right (x x))
          (:instance finite-field-poly-add-inverse-right
                     (x (finite-field-poly-mul x y))))
    :in-theory
    (disable finite-field-poly-add finite-field-poly-mul
             finite-field-poly-neg finite-field-canonical-polynomial-p
             finite-field-polynomial-p))))

(local
 (defthm finite-field-poly-mul-normalize-left-for-reduction
   (equal (finite-field-poly-mul (finite-field-poly-normalize x) y)
          (finite-field-poly-mul x y))
   :hints
   (("Goal"
     :in-theory (theory 'minimal-theory)
     :by (:functional-instance poly-mul-normalize-left
          (gfield::field-element-p gfield::finite-field-element-p)
          (gfield::field-fix gfield::finite-field-fix)
          (gfield::field-zero gfield::finite-field-zero)
          (gfield::field-one gfield::finite-field-one)
          (gfield::field-add gfield::finite-field-add)
          (gfield::field-mul gfield::finite-field-mul)
          (gfield::field-neg gfield::finite-field-neg)
          (gfield::field-inv gfield::finite-field-inv)
          (fix-coefficients finite-field-poly-fix-coefficients)
          (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
          (normalize finite-field-poly-normalize)
          (raw-add finite-field-poly-raw-add)
          (raw-scale finite-field-poly-raw-scale)
          (raw-mul finite-field-poly-raw-mul)
          (poly-mul finite-field-poly-mul)))
    (and stable-under-simplificationp
         (list :use (theory 'gfield::finite-field-context-instance-theory)
               :in-theory
               (list 'quote
                     (union-theories
                      (theory 'finite-field-poly-definition-theory)
                      (theory 'minimal-theory))))))))

(local
 (defthm finite-field-poly-neg-of-normalize-for-reduction
   (equal (finite-field-poly-neg (finite-field-poly-normalize x))
          (finite-field-poly-neg x))
   :hints
   (("Goal"
     :in-theory (theory 'minimal-theory)
     :by (:functional-instance poly-neg-of-normalize
          (gfield::field-element-p gfield::finite-field-element-p)
          (gfield::field-fix gfield::finite-field-fix)
          (gfield::field-zero gfield::finite-field-zero)
          (gfield::field-one gfield::finite-field-one)
          (gfield::field-add gfield::finite-field-add)
          (gfield::field-mul gfield::finite-field-mul)
          (gfield::field-neg gfield::finite-field-neg)
          (gfield::field-inv gfield::finite-field-inv)
          (fix-coefficients finite-field-poly-fix-coefficients)
          (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
          (normalize finite-field-poly-normalize)
          (raw-neg finite-field-poly-raw-neg)
          (poly-neg finite-field-poly-neg)))
    (and stable-under-simplificationp
         (list :use (theory 'gfield::finite-field-context-instance-theory)
               :in-theory
               (list 'quote
                     (union-theories
                      (theory 'finite-field-poly-definition-theory)
                      (theory 'minimal-theory))))))))

(defthm finite-field-poly-mul-of-poly-neg-left-total
  (equal (finite-field-poly-mul (finite-field-poly-neg x) y)
         (finite-field-poly-neg (finite-field-poly-mul x y)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-mul-of-poly-neg-left
                     (x (finite-field-poly-normalize x)) (y y))
          (:instance finite-field-poly-mul-normalize-left-for-reduction))
    :in-theory
    (disable finite-field-poly-mul finite-field-poly-neg
             finite-field-poly-normalize))))

(defthm finite-field-poly-add-right-cancel-canonical
  (implies
   (and (finite-field-canonical-polynomial-p x)
        (finite-field-canonical-polynomial-p y)
        (finite-field-polynomial-p z)
        (equal (finite-field-poly-add x z)
               (finite-field-poly-add y z)))
   (equal x y))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-add-left-cancel-canonical)
          (:instance finite-field-poly-add-commutative (x x) (y z))
          (:instance finite-field-poly-add-commutative (x y) (y z)))
    :in-theory
    (disable finite-field-poly-add finite-field-poly-add-commutative
             finite-field-canonical-polynomial-p))))

(defthm finite-field-equal-sums-imply-left-equals-right-plus-difference
  (implies
   (and (finite-field-canonical-polynomial-p a)
        (finite-field-canonical-polynomial-p b)
        (finite-field-canonical-polynomial-p r1)
        (finite-field-canonical-polynomial-p r2)
        (equal (finite-field-poly-add a r1)
               (finite-field-poly-add b r2)))
   (equal a (finite-field-poly-add b (finite-field-poly-sub r2 r1))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-add-left-to-poly-sub (x r1) (y r2))
          (:instance finite-field-canonical-polynomial-p-implies-polynomial-p
                     (xs r1))
          (:instance finite-field-poly-add-right-cancel-canonical
                     (z r1) (x a)
                     (y (finite-field-poly-add
                         b (finite-field-poly-sub r2 r1))))
          (:instance finite-field-poly-add-associative
                     (x b) (y (finite-field-poly-sub r2 r1)) (z r1))
          (:instance finite-field-poly-add-commutative
                     (x (finite-field-poly-sub r2 r1)) (y r1)))
    :in-theory
    (disable finite-field-poly-add finite-field-poly-sub
             finite-field-canonical-polynomial-p))))

(defthm finite-field-product-of-difference-solves-product-sum
  (implies
   (and (finite-field-polynomial-p q1)
        (finite-field-polynomial-p q2))
   (equal
    (finite-field-poly-add
     (finite-field-poly-mul q2 modulus)
     (finite-field-poly-mul (finite-field-poly-sub q1 q2) modulus))
    (finite-field-poly-mul q1 modulus)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-mul-right-distributive
                     (x q1) (y (finite-field-poly-neg q2)) (z modulus))
          (:instance finite-field-poly-mul-of-poly-neg-left
                     (x q2) (y modulus))
          (:instance finite-field-poly-add-associative
                     (x (finite-field-poly-mul q2 modulus))
                     (y (finite-field-poly-mul q1 modulus))
                     (z (finite-field-poly-neg
                         (finite-field-poly-mul q2 modulus))))
          (:instance finite-field-poly-add-associative
                     (x (finite-field-poly-mul q1 modulus))
                     (y (finite-field-poly-mul q2 modulus))
                     (z (finite-field-poly-neg
                         (finite-field-poly-mul q2 modulus))))
          (:instance finite-field-poly-add-commutative
                     (x (finite-field-poly-mul q2 modulus))
                     (y (finite-field-poly-mul q1 modulus)))
          (:instance finite-field-poly-add-inverse-right
                     (x (finite-field-poly-mul q2 modulus)))
          (:instance finite-field-poly-add-of-nil-left
                     (x (finite-field-poly-mul q1 modulus)))
          (:instance finite-field-poly-normalize-when-canonical
                     (xs (finite-field-poly-mul q1 modulus))))
    :in-theory
    (e/d (finite-field-poly-sub-definition)
         (finite-field-poly-add finite-field-poly-mul
          finite-field-poly-neg finite-field-poly-sub)))))

(defthm finite-field-equal-reconstructions-imply-equal-differences
  (implies
   (and (finite-field-polynomial-p q1)
        (finite-field-polynomial-p q2)
        (finite-field-canonical-polynomial-p r1)
        (finite-field-canonical-polynomial-p r2)
        (equal (finite-field-poly-add (finite-field-poly-mul q1 modulus) r1)
               (finite-field-poly-add (finite-field-poly-mul q2 modulus) r2)))
   (equal (finite-field-poly-mul (finite-field-poly-sub q1 q2) modulus)
          (finite-field-poly-sub r2 r1)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance
           finite-field-equal-sums-imply-left-equals-right-plus-difference
           (a (finite-field-poly-mul q1 modulus))
           (b (finite-field-poly-mul q2 modulus)))
          (:instance finite-field-product-of-difference-solves-product-sum)
          (:instance finite-field-poly-add-left-cancel-canonical
                     (z (finite-field-poly-mul q2 modulus))
                     (x (finite-field-poly-mul
                         (finite-field-poly-sub q1 q2) modulus))
                     (y (finite-field-poly-sub r2 r1))))
    :in-theory
    (disable finite-field-poly-add finite-field-poly-sub finite-field-poly-mul
             finite-field-canonical-polynomial-p
             finite-field-polynomial-p))))

(defthm finite-field-poly-sub-equal-nil-implies-equal
  (implies
   (and (finite-field-canonical-polynomial-p x)
        (finite-field-canonical-polynomial-p y)
        (equal (finite-field-poly-sub x y) nil))
   (equal x y))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-add-left-to-poly-sub (x y) (y x)))
    :in-theory
    (disable finite-field-poly-add finite-field-poly-sub
             finite-field-canonical-polynomial-p))))

(defthm finite-field-bounded-remainders-in-same-coset-are-equal
  (implies
   (and (finite-field-canonical-polynomial-p r1)
        (finite-field-canonical-polynomial-p r2)
        (finite-field-polynomial-p q1)
        (finite-field-polynomial-p q2)
        (finite-field-canonical-polynomial-p modulus)
        (consp modulus)
        (or (not (consp r1))
            (< (finite-field-poly-degree r1)
               (finite-field-poly-degree modulus)))
        (or (not (consp r2))
            (< (finite-field-poly-degree r2)
               (finite-field-poly-degree modulus)))
        (equal (finite-field-poly-add (finite-field-poly-mul q1 modulus) r1)
               (finite-field-poly-add (finite-field-poly-mul q2 modulus) r2)))
   (equal r1 r2))
  :rule-classes nil
  :hints
  (("Goal"
    :cases ((consp (finite-field-poly-sub q1 q2)))
    :use ((:instance finite-field-poly-sub-degree-below-common-bound
                     (x r2) (y r1)
                     (bound (finite-field-poly-degree modulus)))
          (:instance finite-field-equal-reconstructions-imply-equal-differences)
          (:instance finite-field-poly-sub-equal-nil-implies-equal
                     (x r2) (y r1))
          (:instance finite-field-canonical-polynomial-p-of-poly-sub
                     (x q1) (y q2))
          (:instance finite-field-canonical-polynomial-atom-is-nil
                     (p (finite-field-poly-sub q1 q2)))
          (:instance len-positive-when-consp
                     (x (finite-field-poly-sub q1 q2)))
          (:instance len-not-zero-when-consp
                     (x (finite-field-poly-sub q1 q2)))
          (:instance finite-field-poly-normalize-when-canonical
                     (xs (finite-field-poly-sub q1 q2)))
          (:instance finite-field-poly-degree-of-poly-mul
                     (f (finite-field-poly-sub q1 q2)) (g modulus))
          (:instance finite-field-consp-of-poly-mul-when-canonical-nonzero
                     (f (finite-field-poly-sub q1 q2)) (g modulus)))
    :in-theory
    (disable finite-field-poly-degree finite-field-poly-sub
             finite-field-poly-sub-definition
             finite-field-poly-add finite-field-poly-mul
             finite-field-canonical-polynomial-p))))

(defthm finite-field-poly-remainder-of-bounded-reconstruction
  (implies
   (and (consp (finite-field-poly-normalize modulus))
        (finite-field-canonical-polynomial-p candidate-remainder)
        (or (not (consp candidate-remainder))
            (< (finite-field-poly-degree candidate-remainder)
               (finite-field-poly-degree
                (finite-field-poly-normalize modulus))))
        (equal
         (finite-field-poly-normalize dividend)
         (finite-field-poly-add
          (finite-field-poly-mul quotient
                                 (finite-field-poly-normalize modulus))
          candidate-remainder)))
   (equal (finite-field-poly-remainder dividend modulus)
          candidate-remainder))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-divmod-reconstruction
                     (f dividend) (g modulus))
          (:instance finite-field-poly-remainder-is-divmod-remainder)
          (:instance finite-field-poly-divmod-quotient-canonical
                     (f dividend) (g modulus))
          (:instance finite-field-canonical-polynomial-p-implies-polynomial-p
                     (xs (mv-nth 0
                                 (finite-field-poly-divmod dividend modulus))))
          (:instance finite-field-poly-divmod-remainder-canonical
                     (f dividend) (g modulus))
          (:instance finite-field-poly-divmod-final-remainder-degree-bound
                     (f dividend) (g modulus))
          (:instance finite-field-bounded-remainders-in-same-coset-are-equal
                     (q1 (mv-nth 0
                                 (finite-field-poly-divmod dividend modulus)))
                     (r1 (mv-nth 1
                                 (finite-field-poly-divmod dividend modulus)))
                     (q2 (finite-field-poly-normalize quotient))
                     (r2 candidate-remainder)
                     (modulus (finite-field-poly-normalize modulus))))
    :in-theory
    (disable finite-field-poly-divmod finite-field-poly-remainder
             finite-field-poly-normalize finite-field-poly-add
             finite-field-poly-mul finite-field-poly-degree
             finite-field-canonical-polynomial-p))))

(defthm
 finite-field-poly-normalize-of-poly-add-modulus-multiple-reconstruction
  (equal
   (finite-field-poly-normalize
    (finite-field-poly-add
     dividend
     (finite-field-poly-mul
      multiplier (finite-field-poly-normalize modulus))))
   (finite-field-poly-add
    (finite-field-poly-mul
     (finite-field-poly-add
      (mv-nth 0 (finite-field-poly-divmod dividend modulus)) multiplier)
     (finite-field-poly-normalize modulus))
    (finite-field-poly-remainder dividend modulus)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-divmod-reconstruction
                     (f dividend) (g modulus))
          (:instance finite-field-poly-remainder-is-divmod-remainder)
          (:instance finite-field-poly-mul-right-distributive
                     (x (mv-nth 0
                                (finite-field-poly-divmod dividend modulus)))
                     (y multiplier)
                     (z (finite-field-poly-normalize modulus)))
          (:instance finite-field-poly-add-associative
                     (x (finite-field-poly-mul
                         (mv-nth 0
                                 (finite-field-poly-divmod dividend modulus))
                         (finite-field-poly-normalize modulus)))
                     (y (finite-field-poly-remainder dividend modulus))
                     (z (finite-field-poly-mul
                         multiplier (finite-field-poly-normalize modulus))))
          (:instance finite-field-poly-add-associative
                     (x (finite-field-poly-mul
                         (mv-nth 0
                                 (finite-field-poly-divmod dividend modulus))
                         (finite-field-poly-normalize modulus)))
                     (y (finite-field-poly-mul
                         multiplier (finite-field-poly-normalize modulus)))
                     (z (finite-field-poly-remainder dividend modulus)))
          (:instance finite-field-poly-add-commutative
                     (x (finite-field-poly-remainder dividend modulus))
                     (y (finite-field-poly-mul
                         multiplier (finite-field-poly-normalize modulus))))
          (:instance finite-field-poly-normalize-when-canonical
                     (xs (finite-field-poly-add
                          dividend
                          (finite-field-poly-mul
                           multiplier
                           (finite-field-poly-normalize modulus))))))
    :in-theory
    (e/d (finite-field-poly-add)
         (finite-field-poly-divmod finite-field-poly-remainder
          finite-field-poly-normalize finite-field-poly-mul
          finite-field-poly-add-commutative
          finite-field-canonical-polynomial-p
          finite-field-polynomial-p)))))

(defthm finite-field-poly-remainder-of-poly-add-modulus-multiple
  (implies
   (consp (finite-field-poly-normalize modulus))
   (equal
    (finite-field-poly-remainder
     (finite-field-poly-add
      dividend
      (finite-field-poly-mul
       multiplier (finite-field-poly-normalize modulus)))
     modulus)
    (finite-field-poly-remainder dividend modulus)))
  :hints
  (("Goal"
    :use
    ((:instance
      finite-field-poly-normalize-of-poly-add-modulus-multiple-reconstruction)
     (:instance finite-field-poly-remainder-of-bounded-reconstruction
                (dividend
                 (finite-field-poly-add
                  dividend
                  (finite-field-poly-mul
                   multiplier (finite-field-poly-normalize modulus))))
                (quotient
                 (finite-field-poly-add
                  (mv-nth 0 (finite-field-poly-divmod dividend modulus))
                  multiplier))
                (candidate-remainder
                 (finite-field-poly-remainder dividend modulus)))
     (:instance finite-field-poly-remainder-canonical)
     (:instance finite-field-poly-remainder-degree-bound
                (f dividend) (g modulus)))
    :in-theory
    (disable finite-field-poly-divmod finite-field-poly-remainder
             finite-field-poly-normalize finite-field-poly-add
             finite-field-poly-mul finite-field-poly-degree
             finite-field-canonical-polynomial-p))))

(local
 (defthm finite-field-poly-mul-normalize-right-for-reduction
   (equal (finite-field-poly-mul x (finite-field-poly-normalize y))
          (finite-field-poly-mul x y))
   :hints
   (("Goal"
     :in-theory (theory 'minimal-theory)
     :by (:functional-instance poly-mul-normalize-right
          (gfield::field-element-p gfield::finite-field-element-p)
          (gfield::field-fix gfield::finite-field-fix)
          (gfield::field-zero gfield::finite-field-zero)
          (gfield::field-one gfield::finite-field-one)
          (gfield::field-add gfield::finite-field-add)
          (gfield::field-mul gfield::finite-field-mul)
          (gfield::field-neg gfield::finite-field-neg)
          (gfield::field-inv gfield::finite-field-inv)
          (fix-coefficients finite-field-poly-fix-coefficients)
          (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
          (normalize finite-field-poly-normalize)
          (raw-add finite-field-poly-raw-add)
          (raw-scale finite-field-poly-raw-scale)
          (raw-mul finite-field-poly-raw-mul)
          (poly-mul finite-field-poly-mul)))
    (and stable-under-simplificationp
         (list :use (theory 'gfield::finite-field-context-instance-theory)
               :in-theory
               (list 'quote
                     (union-theories
                      (theory 'finite-field-poly-definition-theory)
                      (theory 'minimal-theory))))))))

(local
 (defthm finite-field-poly-mul-of-nil-right-for-reduction
   (equal (finite-field-poly-mul x nil) nil)
   :hints
   (("Goal"
     :in-theory (theory 'minimal-theory)
     :by (:functional-instance poly-mul-of-nil-right
          (gfield::field-element-p gfield::finite-field-element-p)
          (gfield::field-fix gfield::finite-field-fix)
          (gfield::field-zero gfield::finite-field-zero)
          (gfield::field-one gfield::finite-field-one)
          (gfield::field-add gfield::finite-field-add)
          (gfield::field-mul gfield::finite-field-mul)
          (gfield::field-neg gfield::finite-field-neg)
          (gfield::field-inv gfield::finite-field-inv)
          (fix-coefficients finite-field-poly-fix-coefficients)
          (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
          (normalize finite-field-poly-normalize)
          (raw-add finite-field-poly-raw-add)
          (raw-scale finite-field-poly-raw-scale)
          (raw-mul finite-field-poly-raw-mul)
          (poly-mul finite-field-poly-mul)))
    (and stable-under-simplificationp
         (list :use (theory 'gfield::finite-field-context-instance-theory)
               :in-theory
               (list 'quote
                     (union-theories
                      (theory 'finite-field-poly-definition-theory)
                      (theory 'minimal-theory))))))))

(local
 (defthm finite-field-poly-add-of-nil-right-for-reduction
   (equal (finite-field-poly-add x nil)
          (finite-field-poly-normalize x))
   :hints
   (("Goal"
     :use ((:instance finite-field-poly-add-commutative (y nil))
           (:instance finite-field-poly-add-of-nil-left))
     :in-theory
     (disable finite-field-poly-add finite-field-poly-normalize)))))

(local
 (defthm finite-field-poly-mul-zero-normalized-right-for-reduction
   (implies (equal (finite-field-poly-normalize modulus) nil)
            (equal (finite-field-poly-mul multiplier modulus) nil))
   :hints
   (("Goal"
     :use ((:instance finite-field-poly-mul-normalize-right-for-reduction
                      (x multiplier) (y modulus))
           (:instance finite-field-poly-mul-of-nil-right-for-reduction
                      (x multiplier)))
     :in-theory
     (disable finite-field-poly-mul finite-field-poly-normalize
              finite-field-poly-mul-normalize-right-for-reduction)))))

(defthm finite-field-poly-remainder-of-poly-add-divisor-multiple
  (equal
   (finite-field-poly-remainder
    (finite-field-poly-add
     dividend
     (finite-field-poly-mul multiplier modulus))
    modulus)
   (finite-field-poly-remainder dividend modulus))
  :hints
  (("Goal" :cases ((consp (finite-field-poly-normalize modulus))))
   ("Subgoal 1"
    :use ((:instance finite-field-poly-remainder-of-poly-add-modulus-multiple)
          (:instance finite-field-poly-mul-normalize-right-for-reduction
                     (x multiplier) (y modulus)))
    :in-theory
    (disable finite-field-poly-remainder finite-field-poly-add
             finite-field-poly-mul finite-field-poly-normalize))
   ("Subgoal 2"
    :use ((:instance finite-field-poly-remainder-zero-normalized-modulus)
          (:instance finite-field-poly-remainder-zero-normalized-modulus
                     (dividend
                      (finite-field-poly-add
                       dividend
                       (finite-field-poly-mul multiplier modulus))))
          (:instance finite-field-poly-normalize-equal-nil-when-not-consp
                     (xs modulus))
          (:instance finite-field-poly-mul-normalize-right-for-reduction
                     (x multiplier) (y modulus))
          (:instance finite-field-poly-mul-of-nil-right-for-reduction
                     (x multiplier))
          (:instance finite-field-poly-mul-zero-normalized-right-for-reduction)
          (:instance finite-field-poly-add-of-nil-right-for-reduction
                     (x dividend)))
    :in-theory
    (disable finite-field-poly-remainder finite-field-poly-add
             finite-field-poly-mul finite-field-poly-normalize))))

(defthm finite-field-poly-add-left-remainder-reconstruction
  (equal
   (finite-field-poly-add left right)
   (finite-field-poly-add
    (finite-field-poly-add
     (finite-field-poly-remainder left modulus) right)
    (finite-field-poly-mul
     (mv-nth 0 (finite-field-poly-divmod left modulus))
     (finite-field-poly-normalize modulus))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-divmod-reconstruction
                     (f left) (g modulus))
          (:instance finite-field-poly-remainder-is-divmod-remainder
                     (f left) (g modulus))
          (:instance finite-field-poly-add-associative
                     (x (finite-field-poly-mul
                         (mv-nth 0 (finite-field-poly-divmod left modulus))
                         (finite-field-poly-normalize modulus)))
                     (y (finite-field-poly-remainder left modulus))
                     (z (finite-field-poly-normalize right)))
          (:instance finite-field-poly-add-associative
                     (x (finite-field-poly-remainder left modulus))
                     (y (finite-field-poly-normalize right))
                     (z (finite-field-poly-mul
                         (mv-nth 0 (finite-field-poly-divmod left modulus))
                         (finite-field-poly-normalize modulus))))
          (:instance finite-field-poly-add-commutative
                     (x (finite-field-poly-mul
                         (mv-nth 0 (finite-field-poly-divmod left modulus))
                         (finite-field-poly-normalize modulus)))
                     (y (finite-field-poly-add
                         (finite-field-poly-remainder left modulus)
                         (finite-field-poly-normalize right)))))
    :in-theory
    (e/d (finite-field-poly-add)
         (finite-field-poly-divmod finite-field-poly-remainder
          finite-field-poly-normalize finite-field-poly-mul
          finite-field-poly-add-commutative
          finite-field-canonical-polynomial-p
          finite-field-polynomial-p)))))

(defthm finite-field-poly-remainder-of-poly-add-remainder-left
  (equal
   (finite-field-poly-remainder
    (finite-field-poly-add left right) modulus)
   (finite-field-poly-remainder
    (finite-field-poly-add
     (finite-field-poly-remainder left modulus) right)
    modulus))
  :rule-classes nil
  :hints
  (("Goal" :cases ((consp (finite-field-poly-normalize modulus))))
   ("Subgoal 1"
    :use ((:instance finite-field-poly-add-left-remainder-reconstruction)
          (:instance finite-field-poly-remainder-of-poly-add-modulus-multiple
                     (dividend
                      (finite-field-poly-add
                       (finite-field-poly-remainder left modulus) right))
                     (multiplier
                      (mv-nth 0 (finite-field-poly-divmod left modulus)))))
    :in-theory
    (disable finite-field-poly-divmod finite-field-poly-remainder
             finite-field-poly-add finite-field-poly-mul
             finite-field-poly-normalize
             finite-field-poly-mul-normalize-right-for-reduction))
   ("Subgoal 2"
    :use ((:instance finite-field-poly-remainder-zero-normalized-modulus
                     (dividend (finite-field-poly-add left right)))
          (:instance finite-field-poly-remainder-zero-normalized-modulus
                     (dividend
                      (finite-field-poly-add
                       (finite-field-poly-remainder left modulus) right)))
          (:instance finite-field-poly-remainder-zero-normalized-modulus
                     (dividend left)))
    :in-theory
    (e/d (finite-field-poly-add)
         (finite-field-poly-remainder finite-field-poly-normalize
          finite-field-poly-raw-add)))))

(defthm finite-field-poly-remainder-of-poly-add-remainder-right
  (equal
   (finite-field-poly-remainder
    (finite-field-poly-add left right) modulus)
   (finite-field-poly-remainder
    (finite-field-poly-add
     left (finite-field-poly-remainder right modulus))
    modulus))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-remainder-of-poly-add-remainder-left
                     (left right) (right left))
          (:instance finite-field-poly-add-commutative (x left) (y right))
          (:instance finite-field-poly-add-commutative
                     (x (finite-field-poly-remainder right modulus)) (y left)))
    :in-theory
    (disable finite-field-poly-remainder finite-field-poly-add
             finite-field-poly-add-commutative))))

(defthm finite-field-poly-remainder-of-poly-add-remainders
  (equal
   (finite-field-poly-remainder
    (finite-field-poly-add left right) modulus)
   (finite-field-poly-remainder
    (finite-field-poly-add
     (finite-field-poly-remainder left modulus)
     (finite-field-poly-remainder right modulus))
    modulus))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-remainder-of-poly-add-remainder-left)
          (:instance finite-field-poly-remainder-of-poly-add-remainder-right
                     (left (finite-field-poly-remainder left modulus))))
    :in-theory
    (disable finite-field-poly-remainder finite-field-poly-add))))

(defmacro def-finite-field-poly-mul-law-for-reduction (name source formula)
   `(defthm ,name
       ,formula
       :hints
       (("Goal"
         :in-theory (theory 'minimal-theory)
         :by (:functional-instance ,source
              (gfield::field-element-p gfield::finite-field-element-p)
              (gfield::field-fix gfield::finite-field-fix)
              (gfield::field-zero gfield::finite-field-zero)
              (gfield::field-one gfield::finite-field-one)
              (gfield::field-add gfield::finite-field-add)
              (gfield::field-mul gfield::finite-field-mul)
              (gfield::field-neg gfield::finite-field-neg)
              (gfield::field-inv gfield::finite-field-inv)
              (fix-coefficients finite-field-poly-fix-coefficients)
              (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
              (normalize finite-field-poly-normalize)
              (raw-add finite-field-poly-raw-add)
              (poly-add finite-field-poly-add)
              (raw-scale finite-field-poly-raw-scale)
              (poly-scale finite-field-poly-scale)
              (raw-mul finite-field-poly-raw-mul)
              (poly-mul finite-field-poly-mul)))
        (and stable-under-simplificationp
             (list :use (theory 'gfield::finite-field-context-instance-theory)
                   :in-theory
                   (list 'quote
                         (union-theories
                          (theory 'finite-field-poly-definition-theory)
                          (theory 'minimal-theory))))))))

(def-finite-field-poly-mul-law-for-reduction
  finite-field-poly-mul-commutative-for-reduction
  poly-mul-commutative
  (equal (finite-field-poly-mul x y) (finite-field-poly-mul y x)))

(def-finite-field-poly-mul-law-for-reduction
  finite-field-poly-mul-associative-for-reduction
  poly-mul-associative
  (equal (finite-field-poly-mul (finite-field-poly-mul x y) z)
         (finite-field-poly-mul x (finite-field-poly-mul y z))))

; Multiplying the certified reconstruction of LEFT by RIGHT leaves the
; remainder product in the same coset.  This expansionary algebraic shape is
; kept out of rewriting and used only by the multiplication reduction laws.
(defthm finite-field-poly-normalize-of-poly-mul-reconstruction-left
  (equal
   (finite-field-poly-normalize (finite-field-poly-mul left right))
   (finite-field-poly-add
    (finite-field-poly-mul (finite-field-poly-remainder left modulus) right)
    (finite-field-poly-mul
     (finite-field-poly-mul (mv-nth 0 (finite-field-poly-divmod left modulus)) right)
     (finite-field-poly-normalize modulus))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-divmod-reconstruction (f left) (g modulus))
          (:instance finite-field-poly-remainder-is-divmod-remainder
                     (f left) (g modulus))
          (:instance finite-field-poly-mul-right-distributive
                     (x (finite-field-poly-mul (mv-nth 0 (finite-field-poly-divmod left modulus))
                                  (finite-field-poly-normalize modulus)))
                     (y (finite-field-poly-remainder left modulus))
                     (z right))
          (:instance finite-field-poly-mul-associative-for-reduction
                     (x (mv-nth 0 (finite-field-poly-divmod left modulus)))
                     (y (finite-field-poly-normalize modulus)) (z right))
          (:instance finite-field-poly-mul-associative-for-reduction
                     (x (mv-nth 0 (finite-field-poly-divmod left modulus)))
                     (y right) (z (finite-field-poly-normalize modulus)))
          (:instance finite-field-poly-mul-commutative-for-reduction
                     (x (finite-field-poly-normalize modulus)) (y right))
          (:instance finite-field-poly-add-commutative
                     (x (finite-field-poly-mul
                         (mv-nth 0 (finite-field-poly-divmod left modulus))
                         (finite-field-poly-mul (finite-field-poly-normalize modulus) right)))
                     (y (finite-field-poly-mul (finite-field-poly-remainder left modulus) right)))
          (:instance finite-field-poly-mul-normalize-left-for-reduction (x left) (y right))
          (:instance finite-field-poly-normalize-when-canonical
                     (xs (finite-field-poly-mul left right))))
    :in-theory
    (disable finite-field-poly-divmod finite-field-poly-remainder finite-field-poly-normalize finite-field-poly-add finite-field-poly-mul
             finite-field-canonical-polynomial-p))))

(defthm finite-field-poly-remainder-of-poly-mul-remainder-left
  (equal
   (finite-field-poly-remainder (finite-field-poly-mul left right) modulus)
   (finite-field-poly-remainder
    (finite-field-poly-mul (finite-field-poly-remainder left modulus) right) modulus))
  :rule-classes nil
  :hints
  (("Goal" :cases ((consp (finite-field-poly-normalize modulus))))
   ("Subgoal 1"
    :use ((:instance finite-field-poly-normalize-of-poly-mul-reconstruction-left)
          (:instance finite-field-poly-remainder-of-normalize-dividend
                     (dividend (finite-field-poly-mul left right)))
          (:instance finite-field-poly-remainder-of-normalize-dividend
                     (dividend
                      (finite-field-poly-add
                       (finite-field-poly-mul (finite-field-poly-remainder left modulus) right)
                       (finite-field-poly-mul
                        (finite-field-poly-mul
                         (mv-nth 0 (finite-field-poly-divmod left modulus)) right)
                        (finite-field-poly-normalize modulus)))))
          (:instance finite-field-poly-remainder-of-poly-add-modulus-multiple
                     (dividend
                      (finite-field-poly-mul (finite-field-poly-remainder left modulus) right))
                     (multiplier
                      (finite-field-poly-mul (mv-nth 0 (finite-field-poly-divmod left modulus))
                                right))))
    :in-theory (disable finite-field-poly-divmod finite-field-poly-remainder finite-field-poly-normalize finite-field-poly-add finite-field-poly-mul))
   ("Subgoal 2"
    :use ((:instance finite-field-poly-remainder-zero-normalized-modulus
                     (dividend (finite-field-poly-mul left right)))
          (:instance finite-field-poly-remainder-zero-normalized-modulus
                     (dividend
                      (finite-field-poly-mul (finite-field-poly-remainder left modulus) right)))
          (:instance finite-field-poly-remainder-zero-normalized-modulus
                     (dividend left))
          (:instance finite-field-poly-mul-normalize-left-for-reduction (x left) (y right)))
    :in-theory (disable finite-field-poly-remainder finite-field-poly-normalize finite-field-poly-mul))))

(defthm finite-field-poly-remainder-of-poly-mul-remainder-right
  (equal
   (finite-field-poly-remainder (finite-field-poly-mul left right) modulus)
   (finite-field-poly-remainder
    (finite-field-poly-mul left (finite-field-poly-remainder right modulus)) modulus))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-remainder-of-poly-mul-remainder-left
                            (left right) (right left))
                 (:instance finite-field-poly-mul-commutative-for-reduction (x left) (y right))
                 (:instance finite-field-poly-mul-commutative-for-reduction
                            (x (finite-field-poly-remainder right modulus)) (y left)))
           :in-theory (disable finite-field-poly-remainder finite-field-poly-mul))))

(defthm finite-field-poly-remainder-of-poly-mul-remainders
  (equal
   (finite-field-poly-remainder (finite-field-poly-mul left right) modulus)
   (finite-field-poly-remainder
    (finite-field-poly-mul (finite-field-poly-remainder left modulus)
              (finite-field-poly-remainder right modulus))
    modulus))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-remainder-of-poly-mul-remainder-left)
                 (:instance finite-field-poly-remainder-of-poly-mul-remainder-right
                            (left (finite-field-poly-remainder left modulus))))
           :in-theory (disable finite-field-poly-remainder finite-field-poly-mul))))


(def-finite-field-poly-mul-law-for-reduction
  finite-field-poly-mul-one-left-for-remainder-self
  poly-mul-of-one-left
  (equal (finite-field-poly-mul
          (list (gfield::finite-field-one)) polynomial)
         (finite-field-poly-normalize polynomial)))

(defthm finite-field-poly-remainder-self
  (equal (finite-field-poly-remainder modulus modulus) nil)
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-remainder-of-poly-add-divisor-multiple
                     (dividend nil)
                     (multiplier (list (gfield::finite-field-one))))
          (:instance finite-field-poly-remainder-zero-dividend))
    :in-theory
    (e/d (finite-field-poly-add)
         (finite-field-poly-remainder finite-field-poly-mul
          finite-field-poly-normalize finite-field-poly-raw-add)))))
