(in-package "GPOLY")

(include-book "runtime-p-divmod")

(defun runtime-p-poly-divisor-admissible-p (polynomial p)
  (declare (xargs :guard t))
  (let ((polynomial (runtime-p-normalize polynomial p)))
    (and (consp polynomial)
         (equal (runtime-p-mul
                 (runtime-p-poly-leading-coefficient polynomial p)
                 (runtime-p-inv
                  (runtime-p-poly-leading-coefficient polynomial p) p) p)
                (runtime-p-one p)))))

(defthm runtime-p-poly-divisor-admissible-p-of-normalize
  (equal (runtime-p-poly-divisor-admissible-p
          (runtime-p-normalize polynomial p) p)
         (runtime-p-poly-divisor-admissible-p polynomial p))
  :hints (("Goal" :in-theory (enable runtime-p-poly-divisor-admissible-p))))

(defthm runtime-p-poly-divisor-admissible-p-when-prime
  (implies (and (dm::primep (runtime-p-effective-modulus p))
                (consp (runtime-p-normalize polynomial p)))
           (runtime-p-poly-divisor-admissible-p polynomial p))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-division-step-prime-divisor-inverse-check
                            (divisor (runtime-p-normalize polynomial p)))
                 (:instance runtime-p-normalize-idempotent (xs polynomial)))
           :in-theory (enable runtime-p-poly-divisor-admissible-p))))

(local
 (defthm runtime-p-xgcd-remainder-length-decreases
   (implies (runtime-p-poly-divisor-admissible-p second p)
            (< (len (runtime-p-remainder first second p))
               (len (runtime-p-normalize second p))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance runtime-p-remainder-bound (f first) (g second))
                  (:instance runtime-p-canonical-polynomial-p-of-remainder
                             (f first) (g second))
                  (:instance runtime-p-poly-degree-when-canonical-nonzero
                             (poly (runtime-p-remainder first second p)))
                  (:instance runtime-p-poly-degree-when-canonical-nonzero
                             (poly (runtime-p-normalize second p))))
            :in-theory (enable runtime-p-poly-divisor-admissible-p)))))

; This is the sole recursive Euclidean chain.  At a composite effective
; modulus an inadmissible current divisor is a documented terminal state.
(defun runtime-p-extended-euclidean-gcd (first second p)
  (declare
   (xargs :guard t
          :measure (len (runtime-p-normalize second p))
          :hints (("Goal"
                   :use ((:instance runtime-p-xgcd-remainder-length-decreases))
                   :in-theory (disable runtime-p-remainder
                                       runtime-p-normalize)))))
  (if (runtime-p-poly-divisor-admissible-p second p)
      (mv-let (quotient remainder)
        (runtime-p-divmod first second p)
        (mv-let (gcd s-next t-next)
          (runtime-p-extended-euclidean-gcd second remainder p)
          (mv gcd t-next
              (runtime-p-poly-sub
               s-next (runtime-p-poly-mul t-next quotient p) p))))
    (mv (runtime-p-normalize first p)
        (runtime-p-polynomial-one p)
        nil)))

(defun runtime-p-euclidean-gcd (first second p)
  (declare (xargs :guard t))
  (mv-let (gcd s coefficient-t)
    (runtime-p-extended-euclidean-gcd first second p)
    (declare (ignore s coefficient-t))
    gcd))

(verify-guards runtime-p-poly-divisor-admissible-p)
(verify-guards runtime-p-extended-euclidean-gcd)
(verify-guards runtime-p-euclidean-gcd)

(defthm runtime-p-extended-euclidean-gcd-inactive
  (implies (not (runtime-p-poly-divisor-admissible-p second p))
           (equal (runtime-p-extended-euclidean-gcd first second p)
                  (mv (runtime-p-normalize first p)
                      (runtime-p-polynomial-one p) nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-p-extended-euclidean-gcd))))

(defthm runtime-p-extended-euclidean-gcd-active
  (implies (runtime-p-poly-divisor-admissible-p second p)
           (equal
            (runtime-p-extended-euclidean-gcd first second p)
            (mv-let (quotient remainder)
              (runtime-p-divmod first second p)
              (mv-let (gcd s-next t-next)
                (runtime-p-extended-euclidean-gcd second remainder p)
                (mv gcd t-next
                    (runtime-p-poly-sub
                     s-next (runtime-p-poly-mul t-next quotient p) p))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-p-extended-euclidean-gcd))))

(local
 (defthm runtime-p-xgcd-projections-canonical
   (and (runtime-p-canonical-polynomial-p
         (mv-nth 0 (runtime-p-extended-euclidean-gcd first second p)) p)
        (runtime-p-canonical-polynomial-p
         (mv-nth 1 (runtime-p-extended-euclidean-gcd first second p)) p)
        (runtime-p-canonical-polynomial-p
         (mv-nth 2 (runtime-p-extended-euclidean-gcd first second p)) p))
   :hints (("Goal"
            :induct (runtime-p-extended-euclidean-gcd first second p)
            :in-theory (e/d (runtime-p-extended-euclidean-gcd)
                            (runtime-p-divmod runtime-p-normalize))))))

(defthm runtime-p-extended-euclidean-gcd-gcd-canonical
  (runtime-p-canonical-polynomial-p
   (mv-nth 0 (runtime-p-extended-euclidean-gcd first second p)) p)
  :hints (("Goal" :use runtime-p-xgcd-projections-canonical)))

(defthm runtime-p-extended-euclidean-gcd-first-coefficient-canonical
  (runtime-p-canonical-polynomial-p
   (mv-nth 1 (runtime-p-extended-euclidean-gcd first second p)) p)
  :hints (("Goal" :use runtime-p-xgcd-projections-canonical)))

(defthm runtime-p-extended-euclidean-gcd-second-coefficient-canonical
  (runtime-p-canonical-polynomial-p
   (mv-nth 2 (runtime-p-extended-euclidean-gcd first second p)) p)
  :hints (("Goal" :use runtime-p-xgcd-projections-canonical)))

(defthm runtime-p-euclidean-gcd-is-first-xgcd-projection
  (equal (runtime-p-euclidean-gcd first second p)
         (mv-nth 0 (runtime-p-extended-euclidean-gcd first second p)))
  :hints (("Goal" :in-theory (enable runtime-p-euclidean-gcd))))

(local
 (defthm runtime-p-poly-mul-normalize-right-for-xgcd
   (equal (runtime-p-poly-mul x (runtime-p-normalize y p) p)
          (runtime-p-poly-mul x y p))
   :hints (("Goal"
            :use ((:instance runtime-p-poly-mul-of-normalizes
                             (x x) (y y))
                  (:instance runtime-p-poly-mul-of-normalizes
                             (x x) (y (runtime-p-normalize y p))))))))

(local
 (defthm runtime-p-xgcd-bezout-step
   (implies
    (and (equal (runtime-p-poly-add
                 (runtime-p-poly-mul quotient second p) remainder p)
                (runtime-p-normalize first p))
         (equal (runtime-p-poly-add
                 (runtime-p-poly-mul s-next second p)
                 (runtime-p-poly-mul t-next remainder p) p)
                gcd))
    (equal
     (runtime-p-poly-add
      (runtime-p-poly-mul t-next first p)
      (runtime-p-poly-mul
       (runtime-p-poly-sub s-next
                           (runtime-p-poly-mul t-next quotient p) p)
       second p) p)
     gcd))
   :hints
   (("Goal"
     :use ((:instance runtime-p-poly-mul-right-distributive
                      (x s-next)
                      (y (runtime-p-poly-neg
                          (runtime-p-poly-mul t-next quotient p) p))
                      (z second))
           (:instance runtime-p-poly-mul-associative
                      (x t-next) (y quotient) (z second))
           (:instance runtime-p-poly-mul-neg-left
                      (x (runtime-p-poly-mul t-next quotient p)) (y second))
           (:instance runtime-p-poly-add-associative
                      (x (runtime-p-poly-mul t-next first p))
                      (y (runtime-p-poly-mul s-next second p))
                      (z (runtime-p-poly-neg
                          (runtime-p-poly-mul
                           (runtime-p-poly-mul t-next quotient p) second p) p)))
           (:instance runtime-p-poly-add-commutative
                      (x (runtime-p-poly-mul t-next first p))
                      (y (runtime-p-poly-mul s-next second p)))
           (:instance runtime-p-poly-mul-left-distributive
                      (x t-next)
                      (y (runtime-p-poly-mul quotient second p))
                      (z remainder))
           (:instance runtime-p-poly-mul-normalize-right-for-xgcd
                      (x t-next) (y first))
           (:instance runtime-p-poly-add-inverse-right
                      (x (runtime-p-poly-mul
                          t-next (runtime-p-poly-mul quotient second p) p)))
           (:instance runtime-p-poly-add-zero-right
                      (x (runtime-p-poly-mul t-next remainder p)))
           (:instance runtime-p-poly-add-associative
                      (x (runtime-p-poly-mul
                          t-next (runtime-p-poly-mul quotient second p) p))
                      (y (runtime-p-poly-mul t-next remainder p))
                      (z (runtime-p-poly-neg
                          (runtime-p-poly-mul
                           t-next (runtime-p-poly-mul quotient second p) p) p)))
           (:instance runtime-p-poly-add-associative
                      (x (runtime-p-poly-mul t-next remainder p))
                      (y (runtime-p-poly-mul
                          t-next (runtime-p-poly-mul quotient second p) p))
                      (z (runtime-p-poly-neg
                          (runtime-p-poly-mul
                           t-next (runtime-p-poly-mul quotient second p) p) p)))
           (:instance runtime-p-poly-add-commutative
                      (x (runtime-p-poly-mul
                          t-next (runtime-p-poly-mul quotient second p) p))
                      (y (runtime-p-poly-mul t-next remainder p)))
           (:instance runtime-p-poly-add-associative
                      (x (runtime-p-poly-mul s-next second p))
                      (y (runtime-p-poly-mul t-next first p))
                      (z (runtime-p-poly-mul
                          (runtime-p-poly-neg
                           (runtime-p-poly-mul t-next quotient p) p)
                          second p))))
     :in-theory (e/d (runtime-p-poly-sub)
                     (runtime-p-poly-add runtime-p-poly-mul
                      runtime-p-poly-neg runtime-p-normalize))))))

(defthm runtime-p-extended-euclidean-gcd-bezout-core
  (equal
   (runtime-p-poly-add
    (runtime-p-poly-mul
     (mv-nth 1 (runtime-p-extended-euclidean-gcd first second p)) first p)
    (runtime-p-poly-mul
     (mv-nth 2 (runtime-p-extended-euclidean-gcd first second p)) second p) p)
   (mv-nth 0 (runtime-p-extended-euclidean-gcd first second p)))
  :rule-classes nil
  :hints
  (("Goal"
    :induct (runtime-p-extended-euclidean-gcd first second p)
    :in-theory (e/d (runtime-p-extended-euclidean-gcd
                     runtime-p-euclidean-gcd)
                    (runtime-p-divmod runtime-p-normalize
                     runtime-p-poly-add runtime-p-poly-mul runtime-p-poly-sub)))
   (and stable-under-simplificationp
        '(:use ((:instance runtime-p-poly-mul-one-left (x first))
                (:instance runtime-p-divmod-reconstruction
                           (f first) (g second))
                (:instance runtime-p-xgcd-bezout-step
                           (quotient (mv-nth 0 (runtime-p-divmod first second p)))
                           (remainder (mv-nth 1 (runtime-p-divmod first second p)))
                           (gcd (mv-nth 0
                            (runtime-p-extended-euclidean-gcd
                             second (mv-nth 1 (runtime-p-divmod first second p)) p)))
                           (s-next (mv-nth 1
                               (runtime-p-extended-euclidean-gcd
                                second (mv-nth 1 (runtime-p-divmod first second p)) p)))
                           (t-next (mv-nth 2
                               (runtime-p-extended-euclidean-gcd
                                second (mv-nth 1 (runtime-p-divmod first second p)) p)))))
          :in-theory (disable runtime-p-divmod runtime-p-normalize
                              runtime-p-poly-add runtime-p-poly-mul
                              runtime-p-poly-sub)))))


(defthm runtime-p-extended-euclidean-gcd-bezout
  (equal
   (runtime-p-poly-add
    (runtime-p-poly-mul
     (mv-nth 1 (runtime-p-extended-euclidean-gcd first second p)) first p)
    (runtime-p-poly-mul
     (mv-nth 2 (runtime-p-extended-euclidean-gcd first second p)) second p) p)
   (runtime-p-euclidean-gcd first second p))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-extended-euclidean-gcd-bezout-core)
                 (:instance runtime-p-euclidean-gcd-is-first-xgcd-projection))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-p-extended-euclidean-gcd-raw-specification
  (and (equal (runtime-p-euclidean-gcd first second p)
              (mv-nth 0 (runtime-p-extended-euclidean-gcd first second p)))
       (runtime-p-canonical-polynomial-p
        (mv-nth 0 (runtime-p-extended-euclidean-gcd first second p)) p)
       (runtime-p-canonical-polynomial-p
        (mv-nth 1 (runtime-p-extended-euclidean-gcd first second p)) p)
       (runtime-p-canonical-polynomial-p
        (mv-nth 2 (runtime-p-extended-euclidean-gcd first second p)) p)
       (equal
        (runtime-p-poly-add
         (runtime-p-poly-mul
          (mv-nth 1 (runtime-p-extended-euclidean-gcd first second p)) first p)
         (runtime-p-poly-mul
          (mv-nth 2 (runtime-p-extended-euclidean-gcd first second p)) second p) p)
        (runtime-p-euclidean-gcd first second p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-euclidean-gcd-is-first-xgcd-projection)
                 (:instance runtime-p-extended-euclidean-gcd-gcd-canonical)
                 (:instance runtime-p-extended-euclidean-gcd-first-coefficient-canonical)
                 (:instance runtime-p-extended-euclidean-gcd-second-coefficient-canonical)
                 (:instance runtime-p-extended-euclidean-gcd-bezout))
           :in-theory (theory 'minimal-theory))))
