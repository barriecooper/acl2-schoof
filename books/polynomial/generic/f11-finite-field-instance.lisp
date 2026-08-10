(in-package "GPOLY")

(include-book "finite-field-instance")
(include-book "../../curve/f11-golden")
(include-book "../../field/f11-finite-field-context")

; Complete joint-context substitution:
; element/fix/zero/one/add/mul/neg/inv map to the named F11 operations,
; rank and unrank both map to F11-FIX, the bound maps to 11, and the generic
; coefficient fixer maps to the existing transparent F11 definition.
(defthm f11-len-of-poly-fix-coefficients-from-finite-field-instance
  (equal (len (f11-fix-coefficients xs)) (len xs))
  :rule-classes nil
  :hints
  (("Goal"
    :by (:functional-instance
         finite-field-len-of-poly-fix-coefficients
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
         (finite-field-poly-fix-coefficients f11-fix-coefficients))
    :in-theory (theory 'minimal-theory))
   (and stable-under-simplificationp
        (list
         :use (theory 'gfield::f11-finite-field-context-instance-theory)
         :in-theory
         (list 'quote
               (union-theories
                '((:definition f11-fix-coefficients))
                (theory 'minimal-theory)))))))
