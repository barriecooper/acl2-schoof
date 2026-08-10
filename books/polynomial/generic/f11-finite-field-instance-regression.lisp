(in-package "GPOLY")

(include-book "f11-finite-field-instance")

; Regression compatibility client for the production F11 polynomial instance.
(defthm f11-finite-field-instance-minimal-theory-client
  (equal (len (f11-fix-coefficients xs)) (len xs))
  :hints (("Goal"
           :use f11-len-of-poly-fix-coefficients-from-finite-field-instance
           :in-theory (theory 'minimal-theory))))
