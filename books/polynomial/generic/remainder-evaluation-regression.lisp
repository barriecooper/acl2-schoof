(in-package "GPOLY")

(include-book "remainder-evaluation")

(defthm eval-of-poly-remainder-at-root-minimal-theory-client
  (implies (equal (eval modulus x) (gfield::field-zero))
           (equal (eval (poly-remainder polynomial modulus) x)
                  (eval polynomial x)))
  :rule-classes nil
  :hints (("Goal"
           :use eval-of-poly-remainder-at-root
           :in-theory (theory 'minimal-theory))))
