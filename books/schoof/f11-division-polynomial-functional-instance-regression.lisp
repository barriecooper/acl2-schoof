(in-package "GPOLY")

(include-book "f11-division-polynomial-functional-instance")

; Regression-named compatibility client.  Reusable functional-instance
; transports live in the production book included above.
(defthm f11-division-polynomial-functional-instance-minimal-theory-client
  (equal (f11-division-polynomial-base
          n (gfield::f11-fix a) (gfield::f11-fix b))
         (f11-division-polynomial-base n a b))
  :hints
  (("Goal"
    :use f11-division-polynomial-base-of-coefficient-fixes-from-finite-field-instance
    :in-theory (theory 'minimal-theory))))
