(in-package "GPOLY")
(include-book "division-step")

(defthm canonical-degree-decrease-implies-length-decrease
  (implies (and (canonical-polynomial-p x)
                (canonical-polynomial-p y)
                (consp x)
                (or (not (consp y))
                    (< (poly-degree y) (poly-degree x))))
           (< (len y) (len x)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-degree-when-canonical-nonzero (p x))
                 (:instance poly-degree-when-canonical-nonzero (p y)))
           :in-theory (disable canonical-polynomial-p poly-degree))))

(defthm poly-division-step-core-length-decreases
  (implies (and (canonical-polynomial-p remainder)
                (canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (poly-degree divisor) (poly-degree remainder)))
           (< (len (cdr (poly-division-step-core remainder divisor)))
              (len remainder)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-division-step-core-degree-decreases)
                 (:instance canonical-degree-decrease-implies-length-decrease
                            (x remainder)
                            (y (cdr (poly-division-step-core remainder divisor)))))
           :in-theory (disable poly-division-step-core
                               canonical-polynomial-p poly-degree))))

; Shared transparent generator.  The recursive divisor is unchanged and the
; canonical remainder length is the termination measure.
(def-divmod-instance poly-divmod-core poly-divmod canonical-polynomial-p
  poly-degree poly-division-step-core poly-add normalize
  poly-division-step-core-length-decreases)

(defthm poly-divmod-core-accumulator-step-canonical
  (implies (and (canonical-polynomial-p quotient)
                (canonical-polynomial-p remainder)
                (canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (poly-degree divisor) (poly-degree remainder)))
           (canonical-polynomial-p
            (poly-add quotient
                      (car (poly-division-step-core remainder divisor)))))
  :hints (("Goal" :use ((:instance poly-division-step-core-term-properties)))))

(defthm poly-divmod-core-quotient-canonical
  (implies (and (canonical-polynomial-p quotient)
                (canonical-polynomial-p remainder)
                (canonical-polynomial-p divisor))
           (canonical-polynomial-p
            (car (poly-divmod-core quotient remainder divisor))))
  :hints (("Goal" :induct (poly-divmod-core quotient remainder divisor)
           :in-theory (e/d (poly-divmod-core)
                                    (poly-division-step-core poly-add poly-sub
                                     poly-mul monomial normalize raw-add raw-mul
                                     canonical-polynomial-p poly-degree)))))

(defthm poly-divmod-core-remainder-canonical
  (implies (and (canonical-polynomial-p quotient)
                (canonical-polynomial-p remainder)
                (canonical-polynomial-p divisor))
           (canonical-polynomial-p
            (cdr (poly-divmod-core quotient remainder divisor))))
  :hints (("Goal" :induct (poly-divmod-core quotient remainder divisor)
           :in-theory (e/d (poly-divmod-core)
                                    (poly-division-step-core poly-add poly-sub
                                     poly-mul monomial normalize raw-add raw-mul
                                     canonical-polynomial-p poly-degree)))))

(defthm poly-divmod-core-quotient-polynomial
  (implies (and (canonical-polynomial-p quotient)
                (canonical-polynomial-p remainder)
                (canonical-polynomial-p divisor))
           (polynomial-p (car (poly-divmod-core quotient remainder divisor))))
  :hints (("Goal" :use ((:instance poly-divmod-core-quotient-canonical))
           :in-theory (disable poly-divmod-core canonical-polynomial-p polynomial-p))))

(defthm poly-divmod-core-remainder-polynomial
  (implies (and (canonical-polynomial-p quotient)
                (canonical-polynomial-p remainder)
                (canonical-polynomial-p divisor))
           (polynomial-p (cdr (poly-divmod-core quotient remainder divisor))))
  :hints (("Goal" :use ((:instance poly-divmod-core-remainder-canonical))
           :in-theory (disable poly-divmod-core canonical-polynomial-p polynomial-p))))

(defthm poly-divmod-core-quotient-true-listp
  (implies (and (canonical-polynomial-p quotient)
                (canonical-polynomial-p remainder)
                (canonical-polynomial-p divisor))
           (true-listp (car (poly-divmod-core quotient remainder divisor))))
  :hints (("Goal" :use ((:instance poly-divmod-core-quotient-polynomial))
           :in-theory (enable polynomial-p))))

(defthm poly-divmod-core-remainder-true-listp
  (implies (and (canonical-polynomial-p quotient)
                (canonical-polynomial-p remainder)
                (canonical-polynomial-p divisor))
           (true-listp (cdr (poly-divmod-core quotient remainder divisor))))
  :hints (("Goal" :use ((:instance poly-divmod-core-remainder-polynomial))
           :in-theory (enable polynomial-p))))

(defthm poly-divmod-core-inactive
  (implies (and (canonical-polynomial-p quotient)
                (canonical-polynomial-p remainder)
                (canonical-polynomial-p divisor)
                (or (not (consp remainder))
                    (not (consp divisor))
                    (< (poly-degree remainder) (poly-degree divisor))))
           (equal (poly-divmod-core quotient remainder divisor)
                  (cons quotient remainder)))
  :hints (("Goal" :in-theory (enable poly-divmod-core))))

(defthm poly-divmod-accumulator-algebra
  (implies (and (polynomial-p quotient)
                (polynomial-p term)
                (polynomial-p divisor)
                (polynomial-p next)
                (polynomial-p remainder)
                (equal (poly-add (poly-mul term divisor) next) remainder))
           (equal (poly-add (poly-mul (poly-add quotient term) divisor) next)
                  (poly-add (poly-mul quotient divisor) remainder)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-mul-right-distributive
                            (x quotient) (y term) (z divisor))
                 (:instance poly-add-associative
                            (x (poly-mul quotient divisor))
                            (y (poly-mul term divisor))
                            (z next)))
           :in-theory (disable poly-add-associative))))

(defthm poly-divmod-core-reconstruction-invariant
  (implies (and (canonical-polynomial-p quotient)
                (canonical-polynomial-p remainder)
                (canonical-polynomial-p divisor))
           (equal (poly-add
                   (poly-mul
                    (car (poly-divmod-core quotient remainder divisor)) divisor)
                   (cdr (poly-divmod-core quotient remainder divisor)))
                  (poly-add (poly-mul quotient divisor) remainder)))
  :rule-classes nil
  :hints (("Goal"
           :induct (poly-divmod-core quotient remainder divisor)
           :in-theory (e/d (poly-divmod-core)
                           (poly-division-step-core poly-add poly-mul poly-sub
                            monomial normalize raw-add raw-mul
                            canonical-polynomial-p poly-degree)))
          ("Subgoal *1/1''"
           :use ((:instance poly-division-step-core-reconstruction)
                 (:instance poly-division-step-core-term-properties)
                 (:instance poly-division-step-core-next-polynomial)
                 (:instance poly-divmod-accumulator-algebra
                            (term (car (poly-division-step-core remainder divisor)))
                            (next (cdr (poly-division-step-core remainder divisor))))))))

(defthm canonical-polynomial-atom-is-nil
  (implies (and (canonical-polynomial-p p) (not (consp p)))
           (equal p nil))
  :rule-classes nil
  :hints (("Goal" :use ((:instance canonical-zero-polynomial-is-nil (xs p)))
           :in-theory (enable poly-zerop))))

(defthm poly-divmod-core-final-remainder-degree-bound
  (implies (and (canonical-polynomial-p quotient)
                (canonical-polynomial-p remainder)
                (canonical-polynomial-p divisor)
                (consp divisor))
           (let ((final-remainder
                  (cdr (poly-divmod-core quotient remainder divisor))))
             (or (equal final-remainder nil)
                 (< (poly-degree final-remainder)
                    (poly-degree divisor)))))
  :rule-classes nil
  :hints (("Goal"
           :induct (poly-divmod-core quotient remainder divisor)
           :in-theory (e/d (poly-divmod-core)
                           (poly-division-step-core poly-add poly-sub poly-mul
                            monomial normalize raw-add raw-mul
                            canonical-polynomial-p poly-degree)))
          ("Subgoal *1/2.2"
           :use ((:instance canonical-polynomial-atom-is-nil (p remainder))))
          ("Subgoal *1/2.1"
           :use ((:instance canonical-polynomial-atom-is-nil (p remainder))))))

(defthm poly-divmod-quotient-canonical
  (canonical-polynomial-p (mv-nth 0 (poly-divmod f g)))
  :hints (("Goal"
           :use ((:instance poly-divmod-core-quotient-canonical
                            (quotient nil) (remainder (normalize f))
                            (divisor (normalize g))))
           :in-theory (e/d (poly-divmod)
                           (poly-divmod-core normalize canonical-polynomial-p)))))

(defthm poly-divmod-remainder-canonical
  (canonical-polynomial-p (mv-nth 1 (poly-divmod f g)))
  :hints (("Goal"
           :use ((:instance poly-divmod-core-remainder-canonical
                            (quotient nil) (remainder (normalize f))
                            (divisor (normalize g))))
           :in-theory (e/d (poly-divmod)
                           (poly-divmod-core normalize canonical-polynomial-p)))))

(defthm poly-divmod-quotient-polynomial
  (polynomial-p (mv-nth 0 (poly-divmod f g)))
  :hints (("Goal" :use ((:instance poly-divmod-quotient-canonical))
           :in-theory (disable poly-divmod canonical-polynomial-p polynomial-p))))
(defthm poly-divmod-remainder-polynomial
  (polynomial-p (mv-nth 1 (poly-divmod f g)))
  :hints (("Goal" :use ((:instance poly-divmod-remainder-canonical))
           :in-theory (disable poly-divmod canonical-polynomial-p polynomial-p))))
(defthm poly-divmod-quotient-true-listp
  (true-listp (mv-nth 0 (poly-divmod f g)))
  :hints (("Goal" :use ((:instance poly-divmod-quotient-polynomial))
           :in-theory (enable polynomial-p))))
(defthm poly-divmod-remainder-true-listp
  (true-listp (mv-nth 1 (poly-divmod f g)))
  :hints (("Goal" :use ((:instance poly-divmod-remainder-polynomial))
           :in-theory (enable polynomial-p))))

(defthm poly-divmod-reconstruction
  (equal (poly-add (poly-mul (mv-nth 0 (poly-divmod f g)) (normalize g))
                   (mv-nth 1 (poly-divmod f g)))
         (normalize f))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-divmod-core-reconstruction-invariant
                            (quotient nil)
                            (remainder (normalize f))
                            (divisor (normalize g))))
           :in-theory (e/d (poly-divmod)
                           (poly-divmod-core poly-add poly-mul normalize)))))

(defthm poly-divmod-final-remainder-degree-bound
  (implies (consp (normalize g))
           (or (equal (mv-nth 1 (poly-divmod f g)) nil)
               (< (poly-degree (mv-nth 1 (poly-divmod f g)))
                  (poly-degree (normalize g)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-divmod-core-final-remainder-degree-bound
                            (quotient nil)
                            (remainder (normalize f))
                            (divisor (normalize g)))
                 (:instance poly-degree-when-canonical-nonzero
                            (p (normalize g))))
           :in-theory (e/d (poly-divmod)
                           (poly-divmod-core normalize poly-degree)))))

(defthm poly-divmod-zero-divisor
  (equal (poly-divmod f nil) (mv nil (normalize f)))
  :hints (("Goal" :in-theory (enable poly-divmod poly-divmod-core))))

(defthm poly-divmod-zero-dividend
  (equal (poly-divmod nil g) (mv nil nil))
  :hints (("Goal" :in-theory (enable poly-divmod poly-divmod-core))))

(defthm poly-divmod-larger-divisor
  (implies (< (poly-degree f) (poly-degree g))
           (equal (poly-divmod f g) (mv nil (normalize f))))
  :hints (("Goal" :in-theory (enable poly-divmod poly-divmod-core))))

(defthm true-listp-with-zero-length-is-nil
  (implies (and (true-listp x) (equal (len x) 0))
           (equal x nil))
  :rule-classes nil)

(defthm poly-divmod-divisor-one-remainder
  (equal (mv-nth 1 (poly-divmod f (polynomial-one))) nil)
  :hints (("Goal"
           :use ((:instance poly-divmod-final-remainder-degree-bound
                            (g (polynomial-one)))
                 (:instance poly-degree-lower-bound
                            (p (mv-nth 1 (poly-divmod f (polynomial-one)))))
                 (:instance poly-degree-equal-minus-one
                            (p (mv-nth 1 (poly-divmod f (polynomial-one)))))
                 (:instance normalize-when-canonical
                            (xs (mv-nth 1 (poly-divmod f (polynomial-one)))))
                 (:instance normalize-when-canonical
                            (xs (polynomial-one)))
                 (:instance canonical-polynomial-p-of-polynomial-one)
                 (:instance canonical-polynomial-atom-is-nil
                            (p (mv-nth 1 (poly-divmod f (polynomial-one)))))
                 (:instance poly-divmod-remainder-true-listp
                            (g (polynomial-one)))
                 (:instance true-listp-with-zero-length-is-nil
                            (x (mv-nth 1 (poly-divmod f (polynomial-one))))))
           :in-theory (disable poly-divmod normalize poly-degree
                               canonical-polynomial-p))))

(defthm poly-divmod-divisor-one
  (equal (mv-nth 0 (poly-divmod f (polynomial-one))) (normalize f))
  :hints (("Goal"
           :use ((:instance poly-divmod-reconstruction
                            (g (polynomial-one)))
                 (:instance poly-divmod-divisor-one-remainder)
                 (:instance normalize-when-canonical
                            (xs (mv-nth 0 (poly-divmod f (polynomial-one))))))
           :in-theory (disable poly-divmod poly-mul poly-add normalize))))

(defthm poly-divmod-deterministic
  (implies (and (equal f1 f2) (equal g1 g2))
           (equal (poly-divmod f1 g1) (poly-divmod f2 g2))))

(defthm poly-divmod-exact-division
  (implies (equal (mv-nth 1 (poly-divmod f g)) nil)
           (equal (normalize f)
                  (poly-mul (mv-nth 0 (poly-divmod f g))
                            (normalize g))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance poly-divmod-reconstruction)))))

; A narrow functional-instantiation package for concrete recursive instances.
(defthm poly-divmod-public-interface
  (and (canonical-polynomial-p (mv-nth 0 (poly-divmod f g)))
       (canonical-polynomial-p (mv-nth 1 (poly-divmod f g)))
       (equal (poly-add (poly-mul (mv-nth 0 (poly-divmod f g))
                                  (normalize g))
                        (mv-nth 1 (poly-divmod f g)))
              (normalize f))
       (implies (consp (normalize g))
                (or (equal (mv-nth 1 (poly-divmod f g)) nil)
                    (< (poly-degree (mv-nth 1 (poly-divmod f g)))
                       (poly-degree (normalize g))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-divmod-quotient-canonical)
                 (:instance poly-divmod-remainder-canonical)
                 (:instance poly-divmod-reconstruction)
                 (:instance poly-divmod-final-remainder-degree-bound)))))

; Focused symbolic regressions.  The constrained field deliberately has no
; concrete evaluator; POLYNOMIAL-ONE makes cancellation shapes field-generic.
(defthm poly-divmod-regression-malformed-atom
  (equal (poly-divmod 'malformed g) (mv nil nil)))
(defthm poly-divmod-regression-malformed-dotted-tail
  (equal (mv-nth 0 (poly-divmod (cons (gfield::field-one) 'bad-tail)
                                (polynomial-one)))
         (polynomial-one)))
(defthm poly-divmod-regression-one-cancellation
  (equal (mv-nth 0 (poly-divmod (monomial (gfield::field-one) 1)
                                (polynomial-one)))
         (monomial (gfield::field-one) 1)))
(defthm poly-divmod-regression-multiple-cancellations
  (equal (mv-nth 0 (poly-divmod
                    (poly-add (monomial (gfield::field-one) 2)
                              (polynomial-one))
                    (polynomial-one)))
         (normalize (poly-add (monomial (gfield::field-one) 2)
                              (polynomial-one))))
  :hints (("Goal"
           :use ((:instance poly-divmod-divisor-one
                            (f (poly-add (monomial (gfield::field-one) 2)
                                         (polynomial-one)))))
           :in-theory (disable poly-divmod))))
(defthm poly-divmod-regression-nonzero-remainder
  (equal (poly-divmod (polynomial-one)
                      (monomial (gfield::field-one) 1))
         (mv nil (polynomial-one))))

(verify-guards coefficient-list-p)
(verify-guards canonical-polynomial-p)
(verify-guards poly-divmod-core)
(verify-guards poly-divmod)
