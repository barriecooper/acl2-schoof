(in-package "GPOLY")

(include-book "runtime-p-monic-product-arbitrary-multiplier")
(include-book "runtime-p-monic-divmod")

; These elementary group rearrangements are deliberately local.  The public
; interface below is the bounded representative theorem, not a second runtime
; polynomial algebra API.
(local
 (encapsulate
  ()
  (defthm runtime-p-poly-add-left-cancel-local
    (implies (equal (runtime-p-poly-add z x p)
                    (runtime-p-poly-add z y p))
             (equal (runtime-p-normalize x p)
                    (runtime-p-normalize y p)))
    :rule-classes nil
    :hints (("Goal"
             :use ((:instance runtime-p-poly-add-associative
                              (x (runtime-p-poly-neg z p)) (y z) (z x))
                   (:instance runtime-p-poly-add-associative
                              (x (runtime-p-poly-neg z p)) (y z) (z y))
                   (:instance runtime-p-poly-add-inverse-left (x z)))
             :in-theory (disable 
                                 runtime-p-poly-add runtime-p-poly-neg))))

  (defthm runtime-p-product-of-difference-local
    (equal (runtime-p-poly-add
            (runtime-p-poly-mul q2 modulus p)
            (runtime-p-poly-mul (runtime-p-poly-sub q1 q2 p) modulus p) p)
           (runtime-p-poly-mul q1 modulus p))
    :rule-classes nil
    :hints (("Goal"
             :use ((:instance runtime-p-poly-mul-right-distributive
                              (x q1) (y (runtime-p-poly-neg q2 p))
                              (z modulus))
                   (:instance runtime-p-poly-mul-neg-left
                              (x q2) (y modulus))
                   (:instance runtime-p-poly-add-associative
                              (x (runtime-p-poly-mul q2 modulus p))
                              (y (runtime-p-poly-mul q1 modulus p))
                              (z (runtime-p-poly-neg
                                  (runtime-p-poly-mul q2 modulus p) p)))
                   (:instance runtime-p-poly-add-associative
                              (x (runtime-p-poly-mul q1 modulus p))
                              (y (runtime-p-poly-mul q2 modulus p))
                              (z (runtime-p-poly-neg
                                  (runtime-p-poly-mul q2 modulus p) p)))
                   (:instance runtime-p-poly-add-commutative
                              (x (runtime-p-poly-mul q2 modulus p))
                              (y (runtime-p-poly-mul q1 modulus p))))
             :in-theory (e/d (runtime-p-poly-sub)
                             (runtime-p-poly-add runtime-p-poly-mul
                              runtime-p-poly-neg
                             )))))

  (defthm runtime-p-poly-add-right-cancel-local
    (implies (equal (runtime-p-poly-add x z p)
                    (runtime-p-poly-add y z p))
             (equal (runtime-p-normalize x p)
                    (runtime-p-normalize y p)))
    :rule-classes nil
    :hints (("Goal"
             :use ((:instance runtime-p-poly-add-left-cancel-local
                              (z z) (x x) (y y))
                   (:instance runtime-p-poly-add-commutative (x x) (y z))
                   (:instance runtime-p-poly-add-commutative (x y) (y z)))
             :in-theory (disable runtime-p-poly-add))))

  (defthm runtime-p-equal-reconstructions-difference-local
    (implies
     (and (runtime-p-canonical-polynomial-p r1 p)
          (runtime-p-canonical-polynomial-p r2 p)
          (equal (runtime-p-poly-add (runtime-p-poly-mul q1 modulus p) r1 p)
                 (runtime-p-poly-add (runtime-p-poly-mul q2 modulus p) r2 p)))
     (equal (runtime-p-poly-mul (runtime-p-poly-sub q1 q2 p) modulus p)
            (runtime-p-poly-sub r2 r1 p)))
    :rule-classes nil
    :hints (("Goal"
             :use ((:instance runtime-p-product-of-difference-local)
                   (:instance runtime-p-poly-sub-reconstruction (x r2) (y r1))
                   (:instance runtime-p-poly-add-associative
                              (x (runtime-p-poly-mul q2 modulus p))
                              (y (runtime-p-poly-sub r2 r1 p)) (z r1))
                   (:instance runtime-p-poly-add-right-cancel-local
                              (z r1)
                              (x (runtime-p-poly-mul q1 modulus p))
                              (y (runtime-p-poly-add
                                  (runtime-p-poly-mul q2 modulus p)
                                  (runtime-p-poly-sub r2 r1 p) p)))
                   (:instance runtime-p-poly-add-left-cancel-local
                              (z (runtime-p-poly-mul q2 modulus p))
                              (x (runtime-p-poly-mul
                                  (runtime-p-poly-sub q1 q2 p) modulus p))
                              (y (runtime-p-poly-sub r2 r1 p))))
             :in-theory (disable runtime-p-poly-add runtime-p-poly-sub
                                 runtime-p-poly-mul
                                 runtime-p-canonical-polynomial-p))))

  (defthm runtime-p-len-raw-neg-local
    (equal (len (runtime-p-raw-neg x p)) (len x))
    :hints (("Goal" :induct (runtime-p-raw-neg x p)
             :in-theory (enable runtime-p-raw-neg))))

  (defthm runtime-p-len-raw-add-upper-bound-local
    (<= (len (runtime-p-raw-add x y p)) (max (len x) (len y)))
    :rule-classes :linear
    :hints (("Goal" :induct (runtime-p-raw-add x y p)
             :in-theory (enable runtime-p-raw-add))))

  (defthm runtime-p-len-normalize-upper-bound-local
    (<= (len (runtime-p-normalize x p)) (len x))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable runtime-p-normalize))))

  (defthm runtime-p-len-normalized-raw-add-upper-bound-local
    (<= (len (runtime-p-normalize (runtime-p-raw-add x y p) p))
        (max (len x) (len y)))
    :hints (("Goal"
             :use ((:instance runtime-p-len-normalize-upper-bound-local
                              (x (runtime-p-raw-add x y p)))
                   (:instance runtime-p-len-raw-add-upper-bound-local))
             :do-not-induct t
             :in-theory (disable runtime-p-normalize runtime-p-raw-add))))

  (defthm runtime-p-canonical-atom-is-nil-local
    (implies (and (runtime-p-canonical-polynomial-p x p)
                  (not (consp x)))
             (equal x nil))
    :rule-classes nil
    :hints (("Goal" :in-theory (enable runtime-p-canonical-polynomial-p
                                        runtime-p-coefficient-list-p))))

  (defthm runtime-p-len-poly-sub-upper-bound-local
    (implies (and (runtime-p-canonical-polynomial-p x p)
                  (runtime-p-canonical-polynomial-p y p))
             (<= (len (runtime-p-poly-sub x y p)) (max (len x) (len y))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance runtime-p-len-raw-add-upper-bound-local
                              (x (runtime-p-normalize x p))
                              (y (runtime-p-normalize
                                  (runtime-p-raw-neg
                                   (runtime-p-normalize y p) p) p)))
                   (:instance runtime-p-len-normalize-upper-bound-local
                              (x (runtime-p-raw-add
                                  (runtime-p-normalize x p)
                                  (runtime-p-normalize
                                   (runtime-p-raw-neg
                                    (runtime-p-normalize y p) p) p) p)))
                   (:instance runtime-p-len-normalize-upper-bound-local (x x))
                   (:instance runtime-p-len-normalize-upper-bound-local (x y))
                   (:instance runtime-p-len-normalize-upper-bound-local
                              (x (runtime-p-raw-neg
                                  (runtime-p-normalize y p) p)))
                   (:instance runtime-p-len-normalized-raw-add-upper-bound-local
                              (x (runtime-p-normalize x p))
                              (y (runtime-p-normalize
                                  (runtime-p-raw-neg
                                   (runtime-p-normalize y p) p) p))))
             :in-theory (e/d (runtime-p-poly-sub runtime-p-poly-add
                                                 runtime-p-poly-neg)
                             (runtime-p-normalize runtime-p-raw-add
                              runtime-p-raw-neg
                              runtime-p-canonical-polynomial-p)))))

  (defthm runtime-p-sub-degree-below-common-bound-local
    (implies
     (and (runtime-p-canonical-polynomial-p x p)
          (runtime-p-canonical-polynomial-p y p)
          (or (not (consp x)) (< (runtime-p-poly-degree x p) bound))
          (or (not (consp y)) (< (runtime-p-poly-degree y p) bound)))
     (or (equal (runtime-p-poly-sub x y p) nil)
         (< (runtime-p-poly-degree (runtime-p-poly-sub x y p) p) bound)))
    :rule-classes nil
    :hints (("Goal"
             :use ((:instance runtime-p-len-raw-add-upper-bound-local
                              (x x)
                              (y (runtime-p-normalize
                                  (runtime-p-raw-neg y p) p)))
                   (:instance runtime-p-len-normalize-upper-bound-local
                              (x (runtime-p-raw-add
                                  x (runtime-p-normalize
                                     (runtime-p-raw-neg y p) p) p)))
                   (:instance runtime-p-len-normalize-upper-bound-local
                              (x (runtime-p-raw-neg y p)))
                   (:instance runtime-p-poly-degree-when-canonical-nonzero
                              (poly (runtime-p-poly-sub x y p)))
                   (:instance runtime-p-len-poly-sub-upper-bound-local)
                   (:instance runtime-p-canonical-atom-is-nil-local)
                   (:instance runtime-p-canonical-atom-is-nil-local (x y)))
             :in-theory (e/d (runtime-p-poly-sub runtime-p-poly-add
                                                 runtime-p-poly-neg)
                             (runtime-p-normalize
                              runtime-p-canonical-polynomial-p
                              runtime-p-poly-degree)))))

  (defthm runtime-p-poly-sub-equal-nil-implies-equal-local
    (implies (and (runtime-p-canonical-polynomial-p x p)
                  (runtime-p-canonical-polynomial-p y p)
                  (equal (runtime-p-poly-sub x y p) nil))
             (equal x y))
    :rule-classes nil
    :hints (("Goal"
             :use ((:instance runtime-p-poly-sub-reconstruction (x x) (y y)))
             :in-theory (disable runtime-p-poly-add runtime-p-poly-sub
                                 runtime-p-canonical-polynomial-p))))))

(defthm runtime-p-bounded-representatives-in-same-monic-coset-are-equal
  (implies
   (and (runtime-p-canonical-polynomial-p r1 p)
        (runtime-p-canonical-polynomial-p r2 p)
        (consp modulus)
        (equal (runtime-p-poly-leading-coefficient modulus p)
               (runtime-p-one p))
        (or (not (consp r1))
            (< (runtime-p-poly-degree r1 p)
               (runtime-p-poly-degree modulus p)))
        (or (not (consp r2))
            (< (runtime-p-poly-degree r2 p)
               (runtime-p-poly-degree modulus p)))
        (equal (runtime-p-poly-add (runtime-p-poly-mul q1 modulus p) r1 p)
               (runtime-p-poly-add (runtime-p-poly-mul q2 modulus p) r2 p)))
   (equal r1 r2))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-equal-reconstructions-difference-local)
                 (:instance runtime-p-sub-degree-below-common-bound-local
                            (x r2) (y r1)
                            (bound (runtime-p-poly-degree modulus p)))
                 (:instance runtime-p-poly-mul-nonzero-by-monic
                            (multiplier (runtime-p-poly-sub q1 q2 p))
                            (divisor modulus))
                 (:instance runtime-p-poly-mul-by-monic-degree-lower-bound
                            (multiplier (runtime-p-poly-sub q1 q2 p))
                            (divisor modulus))
                 (:instance runtime-p-poly-sub-equal-nil-implies-equal-local
                            (x r2) (y r1)))
           :in-theory (disable runtime-p-poly-add runtime-p-poly-sub
                               runtime-p-poly-mul runtime-p-poly-degree
                               runtime-p-poly-leading-coefficient
                               runtime-p-canonical-polynomial-p))))

(defthm runtime-p-monic-remainder-of-bounded-reconstruction
  (implies
   (and (consp (runtime-p-normalize g p))
        (equal (runtime-p-poly-leading-coefficient
                (runtime-p-normalize g p) p) (runtime-p-one p))
        (runtime-p-canonical-polynomial-p candidate p)
        (or (not (consp candidate))
            (< (runtime-p-poly-degree candidate p)
               (runtime-p-poly-degree (runtime-p-normalize g p) p)))
        (equal (runtime-p-normalize f p)
               (runtime-p-poly-add
                (runtime-p-poly-mul quotient (runtime-p-normalize g p) p)
                candidate p)))
   (equal (runtime-p-monic-remainder f g p) candidate))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-monic-projection-reconstruction)
                 (:instance runtime-p-monic-remainder-bound)
                 (:instance runtime-p-bounded-representatives-in-same-monic-coset-are-equal
                            (q1 (runtime-p-monic-quotient f g p))
                            (r1 (runtime-p-monic-remainder f g p))
                            (q2 quotient) (r2 candidate)
                            (modulus (runtime-p-normalize g p))))
           :in-theory (disable runtime-p-monic-remainder
                               runtime-p-monic-quotient runtime-p-normalize
                               runtime-p-poly-add runtime-p-poly-mul
                               runtime-p-poly-degree
                               runtime-p-poly-leading-coefficient
                               runtime-p-canonical-polynomial-p))))

(local
 (encapsulate
  ()
 (defthm runtime-p-poly-add-normalize-left-local
   (equal (runtime-p-poly-add (runtime-p-normalize x p) y p)
          (runtime-p-poly-add x y p))
   :hints (("Goal"
            :in-theory (enable runtime-p-poly-add))))

 (defthm runtime-p-add-modulus-multiple-reconstruction-local
   (equal
    (runtime-p-normalize
     (runtime-p-poly-add
      f (runtime-p-poly-mul q (runtime-p-normalize g p) p) p) p)
    (runtime-p-poly-add
     (runtime-p-poly-mul
      (runtime-p-poly-add (runtime-p-monic-quotient f g p) q p)
      (runtime-p-normalize g p) p)
     (runtime-p-monic-remainder f g p) p))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance runtime-p-monic-projection-reconstruction)
                  (:instance runtime-p-poly-mul-right-distributive
                             (x (runtime-p-monic-quotient f g p)) (y q)
                             (z (runtime-p-normalize g p)))
                  (:instance runtime-p-poly-add-associative
                             (x (runtime-p-poly-mul
                                 (runtime-p-monic-quotient f g p)
                                 (runtime-p-normalize g p) p))
                             (y (runtime-p-monic-remainder f g p))
                             (z (runtime-p-poly-mul q
                                  (runtime-p-normalize g p) p)))
                  (:instance runtime-p-poly-add-associative
                             (x (runtime-p-poly-mul
                                 (runtime-p-monic-quotient f g p)
                                 (runtime-p-normalize g p) p))
                             (y (runtime-p-poly-mul q
                                  (runtime-p-normalize g p) p))
                             (z (runtime-p-monic-remainder f g p)))
                  (:instance runtime-p-poly-add-commutative
                             (x (runtime-p-monic-remainder f g p))
                             (y (runtime-p-poly-mul q
                                  (runtime-p-normalize g p) p)))
                  (:instance runtime-p-normalize-when-canonical
                             (xs (runtime-p-poly-add
                                  f (runtime-p-poly-mul q
                                     (runtime-p-normalize g p) p) p)))
                  (:instance runtime-p-poly-add-of-normalizes
                             (x f)
                             (y (runtime-p-poly-mul q
                                  (runtime-p-normalize g p) p)))
                  (:instance runtime-p-poly-add-normalize-left-local
                             (x f)
                             (y (runtime-p-poly-mul q
                                  (runtime-p-normalize g p) p))))
            :in-theory (disable runtime-p-monic-quotient
                                runtime-p-monic-remainder runtime-p-normalize
                                runtime-p-poly-add runtime-p-poly-mul
                                ))))))

(defthm runtime-p-monic-remainder-of-poly-add-modulus-multiple
  (implies
   (and (consp (runtime-p-normalize g p))
        (equal (runtime-p-poly-leading-coefficient
                (runtime-p-normalize g p) p)
               (runtime-p-one p)))
   (equal
    (runtime-p-monic-remainder
     (runtime-p-poly-add
      f (runtime-p-poly-mul q (runtime-p-normalize g p) p) p)
     g p)
    (runtime-p-monic-remainder f g p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-add-modulus-multiple-reconstruction-local)
                 (:instance runtime-p-monic-remainder-of-bounded-reconstruction
                            (f (runtime-p-poly-add
                                f (runtime-p-poly-mul q
                                   (runtime-p-normalize g p) p) p))
                            (quotient (runtime-p-poly-add
                                       (runtime-p-monic-quotient f g p) q p))
                            (candidate (runtime-p-monic-remainder f g p)))
                 (:instance runtime-p-monic-remainder-bound))
           :in-theory (disable runtime-p-monic-remainder
                               runtime-p-monic-quotient runtime-p-normalize
                               runtime-p-poly-add runtime-p-poly-mul
                               runtime-p-poly-degree
                               runtime-p-poly-leading-coefficient
                               runtime-p-canonical-polynomial-p))))

(local
 (defthm runtime-p-empty-normalized-divisor-is-not-monic-local
   (implies (not (consp (runtime-p-normalize g p)))
            (not (equal (runtime-p-poly-leading-coefficient
                         (runtime-p-normalize g p) p)
                        (runtime-p-one p))))
   :hints (("Goal"
            :use ((:instance runtime-p-normalize-equal-nil-when-not-consp
                             (xs g))
                  (:instance runtime-p-poly-leading-coefficient-of-nil))
            :in-theory (enable runtime-p-one runtime-p-zero)))))

(defthm runtime-p-monic-remainder-idempotent
  (equal (runtime-p-monic-remainder
          (runtime-p-monic-remainder f g p) g p)
         (runtime-p-monic-remainder f g p))
  :rule-classes nil
  :hints (("Goal"
           :cases ((and (consp (runtime-p-normalize g p))
                        (equal (runtime-p-poly-leading-coefficient
                                (runtime-p-normalize g p) p)
                               (runtime-p-one p)))))
          ("Subgoal 1"
           :use ((:instance runtime-p-monic-remainder-of-bounded-reconstruction
                            (f (runtime-p-monic-remainder f g p))
                            (quotient nil)
                            (candidate (runtime-p-monic-remainder f g p)))
                 (:instance runtime-p-monic-remainder-bound)
                 (:instance runtime-p-canonical-atom-is-nil-local
                            (x (runtime-p-monic-remainder f g p))))
           :in-theory (disable runtime-p-monic-remainder runtime-p-normalize
                               runtime-p-poly-add runtime-p-poly-mul
                               runtime-p-poly-degree
                               runtime-p-poly-leading-coefficient
                               runtime-p-canonical-polynomial-p))
          ("Subgoal 2"
           :use ((:instance runtime-p-monic-divmod-inactive)
                 (:instance runtime-p-monic-divmod-inactive
                            (f (runtime-p-monic-remainder f g p)))
                 (:instance runtime-p-normalize-when-canonical
                            (xs (runtime-p-monic-remainder f g p)))
                 (:instance runtime-p-normalize-equal-nil-when-not-consp
                            (xs g))
                 (:instance runtime-p-poly-leading-coefficient-of-nil)
                 (:instance runtime-p-empty-normalized-divisor-is-not-monic-local))
           :in-theory (e/d (runtime-p-monic-remainder)
                           (runtime-p-monic-divmod runtime-p-normalize
                            runtime-p-poly-leading-coefficient
                            runtime-p-canonical-polynomial-p)))))
