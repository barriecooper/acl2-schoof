(in-package "GPOLY")

(include-book "finite-field-euclidean-interface")

; These clients deliberately disable the implementation and consume only the
; public symbolic endpoints.
(defthm finite-field-euclidean-interface-regression-self-and-zero
  (and (finite-field-poly-divides-p polynomial polynomial)
       (finite-field-poly-divides-p polynomial nil))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-divides-p-self
                            (dividend polynomial))
                 (:instance finite-field-poly-divides-p-zero
                            (divisor polynomial)))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-euclidean-interface-regression-exact-multiple
  (finite-field-poly-divides-p
   divisor (finite-field-poly-mul multiplier divisor))
  :rule-classes nil
  :hints (("Goal" :use ((:instance finite-field-poly-divides-p-of-multiple))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-euclidean-interface-regression-normalization
  (and (equal (finite-field-poly-divides-p
               (finite-field-poly-normalize divisor) dividend)
              (finite-field-poly-divides-p divisor dividend))
       (equal (finite-field-poly-divides-p
               divisor (finite-field-poly-normalize dividend))
              (finite-field-poly-divides-p divisor dividend)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-divides-p-of-normalize-divisor)
                 (:instance finite-field-poly-divides-p-of-normalize-dividend))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-euclidean-interface-regression-total-inputs
  (and (finite-field-poly-divides-p 'malformed 'malformed)
       (finite-field-poly-divides-p '(1 . malformed-tail) nil)
       (finite-field-poly-divides-p '(1 0 0) '(1 0 0)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-divides-p-self
                            (dividend 'malformed))
                 (:instance finite-field-poly-divides-p-zero
                            (divisor '(1 . malformed-tail)))
                 (:instance finite-field-poly-divides-p-self
                            (dividend '(1 0 0))))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-euclidean-interface-regression-forward-step
  (implies (and (finite-field-poly-divides-p divisor first)
                (finite-field-poly-divides-p divisor second))
           (finite-field-poly-divides-p
            divisor (finite-field-poly-remainder first second)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-divides-p-euclidean-step-iff))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-euclidean-interface-regression-reverse-step
  (implies (and (finite-field-poly-divides-p divisor second)
                (finite-field-poly-divides-p
                 divisor (finite-field-poly-remainder first second)))
           (finite-field-poly-divides-p divisor first))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-divides-p-euclidean-step-iff))
           :in-theory (theory 'minimal-theory))))
