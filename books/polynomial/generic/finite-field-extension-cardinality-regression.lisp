(in-package "GPOLY")

(include-book "finite-field-extension-cardinality")
(include-book "finite-field-fixed-modulus-carrier-regression")
(include-book "f7x2-cardinality")

(defthm finite-field-extension-cardinality-minimal-theory-client
  (equal (finite-field-extension-representative-count modulus)
         (expt (nfix (gfield::finite-field-bound))
               (finite-field-fixed-modulus-coefficient-count modulus)))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use finite-field-extension-representative-count-equals-radix-power)))

(defthm finite-field-extension-degree-cardinality-minimal-theory-client
  (implies (consp (finite-field-poly-normalize modulus))
           (equal (finite-field-extension-representative-count modulus)
                  (expt (nfix (gfield::finite-field-bound))
                        (finite-field-poly-degree
                         (finite-field-poly-normalize modulus)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use finite-field-extension-representative-count-equals-degree-power)))

(assert-event
 (and (equal (f7-fixed-modulus-coefficient-count '(1 0 1)) 2)
      (equal (f7-fixed-modulus-coefficient-vector-coding-bound '(1 0 1)) 49)
      (equal (len (f7-fixed-modulus-elements '(1 0 1))) 49)
      (equal (f7x2-cardinality) 49)
      (equal (f7-fixed-modulus-unrank '(1 0 1) 0) (f7x2-unrank 0))
      (equal (f7-fixed-modulus-unrank '(1 0 1) 48) (f7x2-unrank 48))
      (equal (f7-fixed-modulus-reconstruct '(3 0)) (f7x2-fix '(3 0)))
      (equal (f7-fixed-modulus-reconstruct '(bad 0)) (f7x2-fix '(bad 0)))
      (equal (f7-fixed-modulus-elements nil) (list nil))))
