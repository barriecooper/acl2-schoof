(in-package "GPOLY")

(include-book "division-polynomial-base")
(include-book "f11-division-polynomial")
(include-book "../polynomial/generic/f11-finite-field-instance-regression")

; A semantic transport of the generic index-3 base equation to the existing
; transparent F11 implementation.  This is not a concrete curve evaluation.
(defthm f11-division-polynomial-base-index-3-from-finite-field-instance
  (equal
   (f11-division-polynomial-base 3 a b)
   (let* ((a (gfield::f11-fix a))
          (b (gfield::f11-fix b))
          (a2 (gfield::f11-mul a a)))
     (f11-normalize
      (list (gfield::f11-neg a2)
            (gfield::f11-mul (f11-natural-coefficient 12) b)
            (gfield::f11-mul (f11-natural-coefficient 6) a)
            (gfield::f11-zero)
            (f11-natural-coefficient 3)))))
  :rule-classes nil
  :hints
  (("Goal"
    :by (:functional-instance
         finite-field-division-polynomial-base-index-3
         (gfield::finite-field-element-p gfield::f11-element-p)
         (gfield::finite-field-fix gfield::f11-fix)
         (gfield::finite-field-zero gfield::f11-zero)
         (gfield::finite-field-one gfield::f11-one)
         (gfield::finite-field-add gfield::f11-add)
         (gfield::finite-field-mul gfield::f11-mul)
         (gfield::finite-field-neg gfield::f11-neg)
         (gfield::finite-field-inv gfield::f11-inv)
         (gfield::finite-field-rank gfield::f11-fix)
         (gfield::finite-field-unrank gfield::f11-fix)
         (gfield::finite-field-bound (lambda () 11))
         (finite-field-poly-fix-coefficients f11-fix-coefficients)
         (finite-field-poly-trim-trailing-zeros f11-trim-trailing-zeros)
         (finite-field-poly-normalize f11-normalize)
         (finite-field-natural-coefficient f11-natural-coefficient)
         (finite-field-division-polynomial-base-spec
          f11-division-polynomial-base)
         (finite-field-division-polynomial-base
          f11-division-polynomial-base))
    :in-theory (theory 'minimal-theory))
   (and stable-under-simplificationp
        (list
         :use (theory 'gfield::f11-finite-field-context-instance-theory)
         :in-theory
         (list 'quote
               (union-theories
                (theory 'gfield::f11-finite-field-context-instance-theory)
                (union-theories
                 '((:definition nfix)
                  (:definition zp)
                  (:definition gfield::f11-zero)
                  (:definition gfield::f11-one)
                  (:definition f11-fix-coefficients)
                  (:definition f11-trim-trailing-zeros)
                  (:definition f11-normalize)
                  (:definition f11-natural-coefficient)
                   (:definition f11-division-polynomial-base))
                 (theory 'minimal-theory))))))))
