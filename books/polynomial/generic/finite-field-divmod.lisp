(in-package "GPOLY")

(include-book "finite-field-division-step")

(set-default-hints nil)

(local (in-theory (disable finite-field-canonical-polynomial-p
                           finite-field-poly-degree
                           finite-field-poly-division-step-core)))

(def-divmod-instance
  finite-field-poly-divmod-core
  finite-field-poly-divmod
  finite-field-canonical-polynomial-p
  finite-field-poly-degree
  finite-field-poly-division-step-core
  finite-field-poly-add
  finite-field-poly-normalize
  finite-field-poly-division-step-core-length-decreases)

(def-divmod-projections-instance
  finite-field-poly-quotient
  finite-field-poly-remainder
  finite-field-poly-divmod)

(verify-guards finite-field-poly-divmod-core)
(verify-guards finite-field-poly-divmod)
(verify-guards finite-field-poly-quotient)
(verify-guards finite-field-poly-remainder)

(deftheory finite-field-divmod-definition-theory
  '(finite-field-poly-divmod-core
    finite-field-poly-divmod
    finite-field-poly-quotient
    finite-field-poly-remainder))

(defthm finite-field-poly-quotient-is-divmod-quotient
  (equal (finite-field-poly-quotient f g)
         (mv-nth 0 (finite-field-poly-divmod f g)))
  :hints (("Goal" :in-theory (enable finite-field-poly-quotient))))

(defthm finite-field-poly-remainder-is-divmod-remainder
  (equal (finite-field-poly-remainder f g)
         (mv-nth 1 (finite-field-poly-divmod f g)))
  :hints (("Goal" :in-theory (enable finite-field-poly-remainder))))

(defthm finite-field-poly-normalize-definition-for-divmod
  (equal (finite-field-poly-normalize poly)
         (finite-field-poly-trim-trailing-zeros
          (finite-field-poly-fix-coefficients poly)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable finite-field-poly-normalize))))


(defthm finite-field-poly-degree-when-normalize-not-consp
  (implies (not (consp (finite-field-poly-normalize poly)))
           (equal (finite-field-poly-degree poly) -1))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-degree-of-poly-normalize
                            (p poly))
                 (:instance finite-field-poly-degree-of-nil))
           :in-theory (enable finite-field-poly-degree))))

(defthm finite-field-poly-degree-when-normalize-consp
  (implies (consp (finite-field-poly-normalize poly))
           (equal (finite-field-poly-degree poly)
                  (+ -1 (len (finite-field-poly-normalize poly)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-degree-when-canonical-nonzero
                            (p (finite-field-poly-normalize poly)))
                 (:instance finite-field-canonical-polynomial-p-of-poly-normalize
                            (xs poly))
                 (:instance finite-field-poly-degree-of-poly-normalize
                            (p poly)))
           :in-theory (disable finite-field-poly-degree
                               finite-field-poly-normalize))))

(defthm finite-field-poly-degree-when-normalize-consp-expanded
  (implies (consp (finite-field-poly-normalize poly))
           (equal (finite-field-poly-degree poly)
                  (+ -1
                     (len (finite-field-poly-trim-trailing-zeros
                           (finite-field-poly-fix-coefficients poly))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-degree-when-normalize-consp)
                 (:instance finite-field-poly-normalize-definition-for-divmod))
           :in-theory (disable finite-field-poly-degree
                               finite-field-poly-normalize))))


(defthm finite-field-poly-degree-definition-for-divmod
  (equal (finite-field-poly-degree poly)
         (if (consp (finite-field-poly-normalize poly))
             (+ -1 (len (finite-field-poly-normalize poly)))
           -1))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable finite-field-poly-degree))))

; Aggregate public divmod interface remains the next boundary.

(defthm finite-field-poly-divmod-core-accumulator-step-canonical
  (implies (and (finite-field-canonical-polynomial-p quotient)
                (finite-field-canonical-polynomial-p remainder)
                (finite-field-canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (finite-field-poly-degree divisor)
                    (finite-field-poly-degree remainder)))
           (finite-field-canonical-polynomial-p
            (finite-field-poly-add
             quotient
             (car (finite-field-poly-division-step-core remainder divisor)))))
  :hints (("Goal"
           :use ((:instance finite-field-poly-division-step-core-term-properties))
           :in-theory (disable finite-field-poly-division-step-core
                               finite-field-poly-add
                               finite-field-poly-mul
                               finite-field-poly-raw-mul
                               finite-field-poly-normalize))))


; Direct core output canonicality remains the next checkpoint.
