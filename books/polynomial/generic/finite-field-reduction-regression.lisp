(in-package "GPOLY")

(include-book "finite-field-reduction")
(include-book "f7-division")

(local (in-theory (disable finite-field-poly-divmod-core
                           finite-field-poly-divmod
                           finite-field-poly-remainder
                           finite-field-poly-reduced-p
                           finite-field-poly-division-step-core
                           finite-field-poly-add
                           finite-field-poly-mul
                           finite-field-poly-normalize
                           finite-field-poly-raw-add
                           finite-field-poly-raw-mul)))

(defthm finite-field-remainder-normalize-minimal-theory-client
  (and (equal (finite-field-poly-remainder
               (finite-field-poly-normalize dividend) modulus)
              (finite-field-poly-remainder dividend modulus))
       (equal (finite-field-poly-remainder
               dividend (finite-field-poly-normalize modulus))
              (finite-field-poly-remainder dividend modulus))
       (equal (finite-field-poly-normalize
               (finite-field-poly-remainder dividend modulus))
              (finite-field-poly-remainder dividend modulus)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance finite-field-poly-remainder-of-normalize-dividend)
                 (:instance finite-field-poly-remainder-of-normalize-modulus)
                 (:instance finite-field-poly-normalize-of-remainder)))))

(defthm finite-field-remainder-fixer-minimal-theory-client
  (and (finite-field-poly-reduced-p
        (finite-field-poly-remainder polynomial modulus) modulus)
       (equal (finite-field-poly-remainder
               (finite-field-poly-remainder polynomial modulus) modulus)
              (finite-field-poly-remainder polynomial modulus))
       (implies (finite-field-poly-reduced-p polynomial modulus)
                (equal (finite-field-poly-remainder polynomial modulus)
                       polynomial)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance finite-field-poly-reduced-p-of-remainder)
                 (:instance finite-field-poly-remainder-idempotent
                            (dividend polynomial))
                 (:instance finite-field-poly-remainder-when-reduced-p)))))

(defthm finite-field-reduced-characterization-minimal-theory-client
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
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance finite-field-poly-reduced-p-iff-canonical-and-degree-bounded)))))

(defthm f7-reduction-public-interface-client
  (and (equal (f7-poly-remainder (f7-normalize dividend) modulus)
              (f7-poly-remainder dividend modulus))
       (equal (f7-poly-remainder
               (f7-poly-remainder dividend modulus) modulus)
              (f7-poly-remainder dividend modulus)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f7-poly-remainder-of-normalize-dividend)
                         (:instance f7-poly-remainder-idempotent)))))

(assert-event (equal (f7-poly-remainder '(1) '(0 1)) '(1)))
(assert-event (equal (f7-poly-remainder '(1 0 1) '(1 1)) '(2)))
(assert-event (equal (f7-poly-remainder '(2 3) '(1 0 1)) '(2 3)))
(assert-event (equal (f7-poly-remainder nil '(1 1)) nil))
(assert-event (equal (f7-poly-remainder '(1 0 1) nil) '(1 0 1)))
(assert-event (equal (f7-poly-remainder '(0 0) '(0 0)) nil))
(assert-event (equal (f7-poly-remainder '(8 . bad-tail) '(1 1)) '(1)))

(defthm finite-field-sub-degree-below-bound-minimal-theory-client
  (implies
   (and (finite-field-canonical-polynomial-p x)
        (finite-field-canonical-polynomial-p y)
        (or (not (consp x)) (< (finite-field-poly-degree x) bound))
        (or (not (consp y)) (< (finite-field-poly-degree y) bound)))
   (or (equal (finite-field-poly-sub x y) nil)
       (< (finite-field-poly-degree (finite-field-poly-sub x y)) bound)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-sub-degree-below-common-bound))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-add-left-cancel-minimal-theory-client
  (implies
   (and (finite-field-canonical-polynomial-p x)
        (finite-field-canonical-polynomial-p y)
        (finite-field-polynomial-p z)
        (equal (finite-field-poly-add z x)
               (finite-field-poly-add z y)))
   (equal x y))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-add-left-cancel-canonical))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-mul-neg-left-minimal-theory-client
  (implies (finite-field-polynomial-p x)
           (equal (finite-field-poly-mul (finite-field-poly-neg x) y)
                  (finite-field-poly-neg (finite-field-poly-mul x y))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance finite-field-poly-mul-of-poly-neg-left)))))

(defthm finite-field-poly-mul-neg-left-total-minimal-theory-client
  (equal (finite-field-poly-mul (finite-field-poly-neg x) y)
         (finite-field-poly-neg (finite-field-poly-mul x y)))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance finite-field-poly-mul-of-poly-neg-left-total)))))

(defthm finite-field-add-right-cancel-minimal-theory-client
  (implies
   (and (finite-field-canonical-polynomial-p x)
        (finite-field-canonical-polynomial-p y)
        (finite-field-polynomial-p z)
        (equal (finite-field-poly-add x z) (finite-field-poly-add y z)))
   (equal x y))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance finite-field-poly-add-right-cancel-canonical)))))

(defthm finite-field-reconstruction-difference-minimal-theory-client
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
  (("Goal" :in-theory (theory 'minimal-theory)
    :use ((:instance
           finite-field-equal-reconstructions-imply-equal-differences)))))

(defthm finite-field-equal-sums-difference-minimal-theory-client
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
  (("Goal" :in-theory (theory 'minimal-theory)
    :use ((:instance
           finite-field-equal-sums-imply-left-equals-right-plus-difference)))))

(defthm finite-field-product-difference-minimal-theory-client
  (implies
   (and (finite-field-polynomial-p q1) (finite-field-polynomial-p q2))
   (equal
    (finite-field-poly-add
     (finite-field-poly-mul q2 modulus)
     (finite-field-poly-mul (finite-field-poly-sub q1 q2) modulus))
    (finite-field-poly-mul q1 modulus)))
  :rule-classes nil
  :hints
  (("Goal" :in-theory (theory 'minimal-theory)
    :use ((:instance
           finite-field-product-of-difference-solves-product-sum)))))

(defthm finite-field-sub-zero-equality-minimal-theory-client
  (implies
   (and (finite-field-canonical-polynomial-p x)
        (finite-field-canonical-polynomial-p y)
        (equal (finite-field-poly-sub x y) nil))
   (equal x y))
  :rule-classes nil
  :hints
  (("Goal" :in-theory (theory 'minimal-theory)
    :use ((:instance finite-field-poly-sub-equal-nil-implies-equal)))))

(defthm finite-field-bounded-same-coset-uniqueness-minimal-theory-client
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
  (("Goal" :in-theory (theory 'minimal-theory)
    :use ((:instance
           finite-field-bounded-remainders-in-same-coset-are-equal)))))

(defthm finite-field-bounded-reconstruction-minimal-theory-client
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
  (("Goal" :in-theory (theory 'minimal-theory)
    :use ((:instance finite-field-poly-remainder-of-bounded-reconstruction)))))

(defthm finite-field-divisor-multiple-remainder-minimal-theory-client
  (equal
   (finite-field-poly-remainder
    (finite-field-poly-add
     dividend (finite-field-poly-mul multiplier modulus))
    modulus)
   (finite-field-poly-remainder dividend modulus))
  :hints
  (("Goal" :in-theory (theory 'minimal-theory)
    :use ((:instance
           finite-field-poly-remainder-of-poly-add-divisor-multiple)))))

(defthm finite-field-add-remainder-compatibility-minimal-theory-client
  (and
   (equal
    (finite-field-poly-remainder (finite-field-poly-add left right) modulus)
    (finite-field-poly-remainder
     (finite-field-poly-add
      (finite-field-poly-remainder left modulus) right) modulus))
   (equal
    (finite-field-poly-remainder (finite-field-poly-add left right) modulus)
    (finite-field-poly-remainder
     (finite-field-poly-add
      left (finite-field-poly-remainder right modulus)) modulus))
   (equal
    (finite-field-poly-remainder (finite-field-poly-add left right) modulus)
    (finite-field-poly-remainder
     (finite-field-poly-add
      (finite-field-poly-remainder left modulus)
      (finite-field-poly-remainder right modulus)) modulus)))
  :rule-classes nil
  :hints
  (("Goal" :in-theory (theory 'minimal-theory)
    :use ((:instance finite-field-poly-remainder-of-poly-add-remainder-left)
          (:instance finite-field-poly-remainder-of-poly-add-remainder-right)
          (:instance finite-field-poly-remainder-of-poly-add-remainders)))))

; Focused F7 execution supplements the constrained finite-field proofs.
(assert-event
 (equal (f7-poly-remainder
         (f7-poly-add '(3 4)
                      (f7-poly-mul '(2 1) '(1 0 1)))
         '(1 0 1))
        '(3 4)))
(assert-event
 (equal (f7-poly-remainder
         (f7-poly-add '(3 4) (f7-poly-mul '(2 1) '(0 0)))
         '(0 0))
        '(3 4)))
(assert-event
 (equal (f7-poly-remainder
         (f7-poly-add '(8 . bad-tail)
                      (f7-poly-mul '(1) '(1 1)))
         '(1 1))
        '(1)))
