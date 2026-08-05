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


; Public divmod interface functional instantiation remains the next boundary.
