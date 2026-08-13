(in-package "GPOLY")

(include-book "finite-field-euclidean-gcd")
(include-book "xgcd")

(defun finite-field-polynomial-one-for-xgcd ()
  (declare (xargs :guard t))
  (list (gfield::finite-field-one)))

(local
 (defun finite-field-poly-const-for-xgcd (a)
   (if (equal (gfield::finite-field-fix a)
              (gfield::finite-field-zero))
       nil
     (list (gfield::finite-field-fix a)))))

; This is deliberately the same remainder chain as the raw Euclidean GCD.
; DIVMOD is called once at each step so its quotient and remainder remain paired.
(defun finite-field-poly-extended-euclidean-gcd (first second)
  (declare
   (xargs
    :measure (len (finite-field-poly-normalize second))
    :hints
    (("Goal"
      :use ((:instance finite-field-poly-remainder-strict-length-bound
                       (dividend first) (modulus second))
            (:instance finite-field-poly-normalize-of-remainder
                       (dividend first) (modulus second))
            (:instance finite-field-poly-remainder-is-divmod-remainder
                       (f first) (g second)))
      :in-theory (disable finite-field-poly-normalize
                          finite-field-poly-remainder
                          finite-field-poly-divmod)))))
  (if (consp (finite-field-poly-normalize second))
      (mv-let (quotient remainder)
        (finite-field-poly-divmod first second)
        (mv-let (gcd s-next t-next)
          (finite-field-poly-extended-euclidean-gcd second remainder)
          (mv gcd
              t-next
              (finite-field-poly-sub
               s-next (finite-field-poly-mul t-next quotient)))))
    (mv (finite-field-poly-normalize first)
        (finite-field-polynomial-one-for-xgcd)
        nil)))

(verify-guards finite-field-polynomial-one-for-xgcd)
(verify-guards finite-field-poly-extended-euclidean-gcd)

(defthm finite-field-poly-extended-euclidean-gcd-zero-second
  (implies
   (not (consp (finite-field-poly-normalize second)))
   (equal (finite-field-poly-extended-euclidean-gcd first second)
          (mv (finite-field-poly-normalize first)
              (finite-field-polynomial-one-for-xgcd)
              nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (enable finite-field-poly-extended-euclidean-gcd))))

(defthm finite-field-poly-extended-euclidean-gcd-nonzero-second
  (implies
   (consp (finite-field-poly-normalize second))
   (equal
    (finite-field-poly-extended-euclidean-gcd first second)
    (mv-let (quotient remainder)
      (finite-field-poly-divmod first second)
      (mv-let (gcd s-next t-next)
        (finite-field-poly-extended-euclidean-gcd second remainder)
        (mv gcd t-next
            (finite-field-poly-sub
             s-next (finite-field-poly-mul t-next quotient)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (finite-field-poly-extended-euclidean-gcd)
                (finite-field-poly-divmod finite-field-poly-normalize
                 finite-field-poly-sub finite-field-poly-mul)))))

(local
 (defthm finite-field-poly-extended-euclidean-gcd-projections-canonical
   (and
    (finite-field-canonical-polynomial-p
     (mv-nth 0 (finite-field-poly-extended-euclidean-gcd first second)))
    (finite-field-canonical-polynomial-p
     (mv-nth 1 (finite-field-poly-extended-euclidean-gcd first second)))
    (finite-field-canonical-polynomial-p
     (mv-nth 2 (finite-field-poly-extended-euclidean-gcd first second))))
   :hints (("Goal"
            :induct (finite-field-poly-extended-euclidean-gcd first second)
            :in-theory
            (e/d (finite-field-poly-extended-euclidean-gcd
                  finite-field-polynomial-one-for-xgcd)
                 (finite-field-poly-normalize finite-field-poly-divmod))))))

(defthm finite-field-poly-extended-euclidean-gcd-gcd-canonical
  (finite-field-canonical-polynomial-p
   (mv-nth 0 (finite-field-poly-extended-euclidean-gcd first second)))
  :hints (("Goal" :use
           finite-field-poly-extended-euclidean-gcd-projections-canonical)))

(defthm finite-field-poly-extended-euclidean-gcd-first-coefficient-canonical
  (finite-field-canonical-polynomial-p
   (mv-nth 1 (finite-field-poly-extended-euclidean-gcd first second)))
  :hints (("Goal" :use
           finite-field-poly-extended-euclidean-gcd-projections-canonical)))

(defthm finite-field-poly-extended-euclidean-gcd-second-coefficient-canonical
  (finite-field-canonical-polynomial-p
   (mv-nth 2 (finite-field-poly-extended-euclidean-gcd first second)))
  :hints (("Goal" :use
           finite-field-poly-extended-euclidean-gcd-projections-canonical)))

(defthm finite-field-poly-normalize-of-extended-euclidean-gcd-gcd
  (equal (finite-field-poly-normalize
          (mv-nth 0 (finite-field-poly-extended-euclidean-gcd first second)))
         (mv-nth 0 (finite-field-poly-extended-euclidean-gcd first second)))
  :hints (("Goal" :use
           ((:instance finite-field-poly-normalize-when-canonical
                       (xs (mv-nth 0
                            (finite-field-poly-extended-euclidean-gcd
                             first second))))))))

(defthm finite-field-poly-normalize-of-extended-euclidean-gcd-first-coefficient
  (equal (finite-field-poly-normalize
          (mv-nth 1 (finite-field-poly-extended-euclidean-gcd first second)))
         (mv-nth 1 (finite-field-poly-extended-euclidean-gcd first second)))
  :hints (("Goal" :use
           ((:instance finite-field-poly-normalize-when-canonical
                       (xs (mv-nth 1
                            (finite-field-poly-extended-euclidean-gcd
                             first second))))))))

(defthm finite-field-poly-normalize-of-extended-euclidean-gcd-second-coefficient
  (equal (finite-field-poly-normalize
          (mv-nth 2 (finite-field-poly-extended-euclidean-gcd first second)))
         (mv-nth 2 (finite-field-poly-extended-euclidean-gcd first second)))
  :hints (("Goal" :use
           ((:instance finite-field-poly-normalize-when-canonical
                       (xs (mv-nth 2
                            (finite-field-poly-extended-euclidean-gcd
                             first second))))))))

(defthm finite-field-poly-extended-euclidean-gcd-gcd-is-euclidean-gcd
  (equal
   (mv-nth 0 (finite-field-poly-extended-euclidean-gcd first second))
   (finite-field-poly-euclidean-gcd first second))
  :hints (("Goal"
           :induct (finite-field-poly-extended-euclidean-gcd first second)
           :in-theory
           (e/d (finite-field-poly-extended-euclidean-gcd
                 finite-field-poly-euclidean-gcd
                 finite-field-poly-remainder)
                (finite-field-poly-divmod finite-field-poly-normalize)))))

; The recursive proof is direct over the production finite-field-prefixed
; operations.  Only this small multiplication-normalization ring fact reuses
; its generic counterpart by functional instantiation.
(local
 (defthm finite-field-poly-mul-normalize-right-for-xgcd
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
 (defthm finite-field-poly-add-zero-right-for-xgcd
   (equal (finite-field-poly-add x nil)
          (finite-field-poly-normalize x))
   :hints (("Goal"
            :use ((:instance finite-field-poly-add-commutative (y nil))
                  (:instance finite-field-poly-add-of-nil-left))
            :in-theory (disable finite-field-poly-add
                                finite-field-poly-normalize)))))

(local
 (defthm finite-field-poly-mul-left-distributive-for-xgcd
   (equal (finite-field-poly-mul x (finite-field-poly-add y z))
          (finite-field-poly-add (finite-field-poly-mul x y)
                                 (finite-field-poly-mul x z)))
   :hints (("Goal"
            :use ((:instance finite-field-poly-mul-commutative-for-reduction
                             (y (finite-field-poly-add y z)))
                  (:instance finite-field-poly-mul-right-distributive
                             (x y) (y z) (z x))
                  (:instance finite-field-poly-mul-commutative-for-reduction
                             (x y) (y x))
                  (:instance finite-field-poly-mul-commutative-for-reduction
                             (x z) (y x)))
            :in-theory (disable finite-field-poly-add finite-field-poly-mul)))))

(local
 (defthm finite-field-poly-extended-euclidean-gcd-bezout-step
   (implies
    (and (equal (finite-field-poly-add
                 (finite-field-poly-mul quotient second) remainder)
                (finite-field-poly-normalize first))
         (equal (finite-field-poly-add
                 (finite-field-poly-mul s-next second)
                 (finite-field-poly-mul t-next remainder))
                gcd))
    (equal
     (finite-field-poly-add
      (finite-field-poly-mul t-next first)
      (finite-field-poly-mul
       (finite-field-poly-sub
        s-next (finite-field-poly-mul t-next quotient))
       second))
     gcd))
   :hints
   (("Goal"
     :use ((:instance finite-field-poly-mul-right-distributive
                      (x s-next)
                      (y (finite-field-poly-neg
                          (finite-field-poly-mul t-next quotient)))
                      (z second))
           (:instance finite-field-poly-mul-associative-for-reduction
                      (x t-next) (y quotient) (z second))
           (:instance finite-field-poly-mul-of-poly-neg-left-total
                      (x (finite-field-poly-mul t-next quotient)) (y second))
           (:instance finite-field-poly-add-associative
                      (x (finite-field-poly-mul t-next first))
                      (y (finite-field-poly-mul s-next second))
                      (z (finite-field-poly-neg
                          (finite-field-poly-mul
                           (finite-field-poly-mul t-next quotient) second))))
           (:instance finite-field-poly-add-commutative
                      (x (finite-field-poly-mul t-next first))
                      (y (finite-field-poly-mul s-next second)))
           (:instance finite-field-poly-mul-left-distributive-for-xgcd
                      (x t-next)
                      (y (finite-field-poly-mul quotient second))
                      (z remainder))
           (:instance finite-field-poly-mul-normalize-right-for-xgcd
                      (x t-next) (y first))
           (:instance finite-field-poly-add-inverse-right
                      (x (finite-field-poly-mul
                          t-next (finite-field-poly-mul quotient second))))
           (:instance finite-field-poly-add-zero-right-for-xgcd
                      (x (finite-field-poly-mul t-next remainder)))
           (:instance finite-field-poly-normalize-when-canonical
                      (xs (finite-field-poly-mul t-next remainder)))
           (:instance finite-field-poly-add-associative
                      (x (finite-field-poly-mul
                          t-next (finite-field-poly-mul quotient second)))
                      (y (finite-field-poly-mul t-next remainder))
                      (z (finite-field-poly-neg
                          (finite-field-poly-mul
                           t-next (finite-field-poly-mul quotient second)))))
           (:instance finite-field-poly-add-associative
                      (x (finite-field-poly-mul t-next remainder))
                      (y (finite-field-poly-mul
                          t-next (finite-field-poly-mul quotient second)))
                      (z (finite-field-poly-neg
                          (finite-field-poly-mul
                           t-next (finite-field-poly-mul quotient second)))))
           (:instance finite-field-poly-add-commutative
                      (x (finite-field-poly-mul
                          t-next (finite-field-poly-mul quotient second)))
                      (y (finite-field-poly-mul t-next remainder)))
           (:instance finite-field-poly-add-associative
                      (x (finite-field-poly-mul s-next second))
                      (y (finite-field-poly-mul t-next first))
                      (z (finite-field-poly-mul
                          (finite-field-poly-neg
                           (finite-field-poly-mul t-next quotient)) second))))
     :in-theory
     (e/d (finite-field-poly-sub-definition)
          (finite-field-poly-divmod finite-field-poly-add
           finite-field-poly-mul finite-field-poly-neg
           finite-field-poly-normalize finite-field-poly-add-commutative
           finite-field-poly-mul-commutative-for-reduction))))))

(defthm finite-field-poly-extended-euclidean-gcd-bezout
  (equal
   (finite-field-poly-add
    (finite-field-poly-mul
     (mv-nth 1 (finite-field-poly-extended-euclidean-gcd first second)) first)
    (finite-field-poly-mul
     (mv-nth 2 (finite-field-poly-extended-euclidean-gcd first second)) second))
   (mv-nth 0 (finite-field-poly-extended-euclidean-gcd first second)))
  :hints
  (("Goal"
    :induct (finite-field-poly-extended-euclidean-gcd first second)
    :in-theory
    (e/d (finite-field-poly-extended-euclidean-gcd)
         (finite-field-poly-divmod finite-field-poly-normalize
          finite-field-poly-add finite-field-poly-mul finite-field-poly-sub
          finite-field-poly-sub-definition
          finite-field-poly-extended-euclidean-gcd-gcd-is-euclidean-gcd)))
   ("Subgoal *1/1"
    :use ((:instance finite-field-poly-divmod-reconstruction
                     (f first) (g second))
          (:instance finite-field-poly-extended-euclidean-gcd-bezout-step
                     (quotient (mv-nth 0
                                       (finite-field-poly-divmod first second)))
                     (remainder (mv-nth 1
                                        (finite-field-poly-divmod first second)))
                     (gcd (mv-nth 0
                                  (finite-field-poly-extended-euclidean-gcd
                                   second
                                   (mv-nth 1
                                           (finite-field-poly-divmod
                                            first second)))))
                     (s-next (mv-nth 1
                                     (finite-field-poly-extended-euclidean-gcd
                                      second
                                      (mv-nth 1
                                              (finite-field-poly-divmod
                                               first second)))))
                     (t-next (mv-nth 2
                                     (finite-field-poly-extended-euclidean-gcd
                                      second
                                      (mv-nth 1
                                              (finite-field-poly-divmod
                                               first second))))))))))

(defthm finite-field-poly-extended-euclidean-gcd-bezout-with-euclidean-gcd
  (equal
   (finite-field-poly-add
    (finite-field-poly-mul
     (mv-nth 1 (finite-field-poly-extended-euclidean-gcd first second)) first)
    (finite-field-poly-mul
     (mv-nth 2 (finite-field-poly-extended-euclidean-gcd first second)) second))
   (finite-field-poly-euclidean-gcd first second))
  :hints (("Goal" :use
           ((:instance finite-field-poly-extended-euclidean-gcd-bezout)
            (:instance
             finite-field-poly-extended-euclidean-gcd-gcd-is-euclidean-gcd))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-extended-euclidean-gcd-raw-specification
  (and
   (equal
    (mv-nth 0 (finite-field-poly-extended-euclidean-gcd first second))
    (finite-field-poly-euclidean-gcd first second))
   (equal
    (finite-field-poly-add
     (finite-field-poly-mul
      (mv-nth 1 (finite-field-poly-extended-euclidean-gcd first second)) first)
     (finite-field-poly-mul
      (mv-nth 2 (finite-field-poly-extended-euclidean-gcd first second)) second))
    (finite-field-poly-euclidean-gcd first second))
   (finite-field-canonical-polynomial-p
    (mv-nth 0 (finite-field-poly-extended-euclidean-gcd first second)))
   (finite-field-canonical-polynomial-p
    (mv-nth 1 (finite-field-poly-extended-euclidean-gcd first second)))
   (finite-field-canonical-polynomial-p
    (mv-nth 2 (finite-field-poly-extended-euclidean-gcd first second))))
  :rule-classes nil
  :hints (("Goal" :use
           ((:instance
             finite-field-poly-extended-euclidean-gcd-gcd-is-euclidean-gcd)
            (:instance
             finite-field-poly-extended-euclidean-gcd-bezout-with-euclidean-gcd)
            (:instance
             finite-field-poly-extended-euclidean-gcd-gcd-canonical)
            (:instance
             finite-field-poly-extended-euclidean-gcd-first-coefficient-canonical)
            (:instance
             finite-field-poly-extended-euclidean-gcd-second-coefficient-canonical))
           :in-theory (theory 'minimal-theory))))
