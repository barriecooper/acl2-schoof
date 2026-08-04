(in-package "GPOLY")

(include-book "finite-field-monomial-division-support")
(include-book "division-step")

(set-default-hints nil)

(def-division-step-instance
  finite-field-poly-division-step-core
  finite-field-poly-division-step
  finite-field-poly-division-step-term
  finite-field-poly-division-step-next
  finite-field-poly-degree
  finite-field-poly-leading-coefficient
  finite-field-poly-monomial
  finite-field-poly-sub
  finite-field-poly-mul
  finite-field-poly-normalize
  finite-field-div)

(verify-guards finite-field-poly-division-step-core)
(verify-guards finite-field-poly-division-step)
(verify-guards finite-field-poly-division-step-term)
(verify-guards finite-field-poly-division-step-next)

(deftheory finite-field-division-step-definition-theory
  '(finite-field-poly-division-step-core
    finite-field-poly-division-step
    finite-field-poly-division-step-term
    finite-field-poly-division-step-next))

(defthm finite-field-poly-division-step-core-inactive
  (implies (or (not (consp remainder))
               (not (consp divisor))
               (< (finite-field-poly-degree remainder)
                  (finite-field-poly-degree divisor)))
           (equal (finite-field-poly-division-step-core remainder divisor)
                  (cons nil remainder)))
  :hints (("Goal" :in-theory (enable finite-field-poly-division-step-core))))

(defthm finite-field-divisor-leading-coefficient-nonzero-for-division-step
  (implies (and (finite-field-canonical-polynomial-p divisor) (consp divisor))
           (not (equal (finite-field-poly-leading-coefficient divisor)
                       (gfield::finite-field-zero))))
  :hints (("Goal"
           :use ((:instance finite-field-poly-leading-coefficient-nonzero-when-canonical-nonzero
                            (p divisor))))))

(defthm finite-field-divisor-leading-coefficient-inverse-nonzero-for-division-step
  (implies (and (finite-field-canonical-polynomial-p divisor) (consp divisor))
           (not (equal (gfield::finite-field-inv
                        (finite-field-poly-leading-coefficient divisor))
                       (gfield::finite-field-zero))))
  :hints (("Goal"
           :use ((:instance finite-field-inv-nonzero
                            (y (finite-field-poly-leading-coefficient divisor)))
                 (:instance finite-field-element-p-of-poly-leading-coefficient
                            (p divisor))
                 (:instance finite-field-divisor-leading-coefficient-nonzero-for-division-step)))))

(defthm finite-field-poly-division-step-core-term-properties
  (implies (and (finite-field-canonical-polynomial-p remainder)
                (finite-field-canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (finite-field-poly-degree divisor)
                    (finite-field-poly-degree remainder)))
           (let ((term (car (finite-field-poly-division-step-core remainder divisor))))
             (and (finite-field-canonical-polynomial-p term)
                  (consp term)
                  (equal (finite-field-poly-degree term)
                         (- (finite-field-poly-degree remainder)
                            (finite-field-poly-degree divisor)))
                  (equal (finite-field-poly-leading-coefficient term)
                         (finite-field-div
                          (finite-field-poly-leading-coefficient remainder)
                          (finite-field-poly-leading-coefficient divisor))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-degree-of-monomial
                            (a (finite-field-div
                                (finite-field-poly-leading-coefficient remainder)
                                (finite-field-poly-leading-coefficient divisor)))
                            (n (- (finite-field-poly-degree remainder)
                                  (finite-field-poly-degree divisor))))
                 (:instance finite-field-poly-leading-coefficient-of-monomial
                            (a (finite-field-div
                                (finite-field-poly-leading-coefficient remainder)
                                (finite-field-poly-leading-coefficient divisor)))
                            (n (- (finite-field-poly-degree remainder)
                                  (finite-field-poly-degree divisor))))
                 (:instance finite-field-div-nonzero
                            (x (finite-field-poly-leading-coefficient remainder))
                            (y (finite-field-poly-leading-coefficient divisor)))
                 (:instance finite-field-poly-leading-coefficient-nonzero-when-canonical-nonzero
                            (p remainder))
                 (:instance finite-field-poly-leading-coefficient-nonzero-when-canonical-nonzero
                            (p divisor))
                 (:instance finite-field-element-p-of-poly-leading-coefficient
                            (p remainder))
                 (:instance finite-field-element-p-of-poly-leading-coefficient
                            (p divisor))
                 (:instance finite-field-poly-normalize-when-canonical (xs remainder))
                 (:instance finite-field-poly-normalize-when-canonical (xs divisor)))
           :in-theory (enable finite-field-poly-division-step-core))))
