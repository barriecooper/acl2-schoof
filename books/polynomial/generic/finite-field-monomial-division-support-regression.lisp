(in-package "GPOLY")

(include-book "finite-field-monomial-division-support")
(include-book "f7-division")

(defthm finite-field-support-minimal-client-monomial-degree
  (implies (not (equal (gfield::finite-field-fix a)
                       (gfield::finite-field-zero)))
           (equal (finite-field-poly-degree (finite-field-poly-monomial a n))
                  (nfix n)))
  :rule-classes nil
  :hints (("Goal" :use finite-field-poly-degree-of-monomial
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-support-minimal-client-monomial-leading-coefficient
  (implies (not (equal (gfield::finite-field-fix a)
                       (gfield::finite-field-zero)))
           (equal (finite-field-poly-leading-coefficient
                   (finite-field-poly-monomial a n))
                  (gfield::finite-field-fix a)))
  :rule-classes nil
  :hints (("Goal" :use finite-field-poly-leading-coefficient-of-monomial
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-support-minimal-client-div-nonzero
  (implies (and (not (equal (gfield::finite-field-fix x)
                            (gfield::finite-field-zero)))
                (not (equal (gfield::finite-field-fix y)
                            (gfield::finite-field-zero))))
           (not (equal (finite-field-div x y)
                       (gfield::finite-field-zero))))
  :rule-classes nil
  :hints (("Goal" :use finite-field-div-nonzero
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-support-minimal-client-div-mul-denominator
  (implies (not (equal (gfield::finite-field-fix y)
                       (gfield::finite-field-zero)))
           (equal (gfield::finite-field-mul (finite-field-div x y) y)
                  (gfield::finite-field-fix x)))
  :rule-classes nil
  :hints (("Goal" :use finite-field-div-mul-denominator
           :in-theory (theory 'minimal-theory))))

(assert-event (equal (gfield::f7-div 3 2) 5))
(assert-event (not (equal (gfield::f7-div 3 2) 0)))
(assert-event (equal (gfield::f7-mul (gfield::f7-div 3 2) 2) 3))
(assert-event (equal (f7-zero-prefix 3 '(2)) '(0 0 0 2)))
(assert-event (equal (f7-poly-shift '(2) 3) '(0 0 0 2)))
(assert-event (equal (f7-monomial 2 3) '(0 0 0 2)))
(assert-event (equal (f7-poly-degree (f7-monomial 2 3)) 3))
(assert-event (equal (f7-poly-leading-coefficient (f7-monomial 2 3)) 2))
