(in-package "GPOLY")
(include-book "coefficient")

(defthm coefficient-interface-regressions
  (and (equal (poly-coefficient 0 nil) (gfield::field-zero))
       (equal (poly-coefficient 1 (list x y)) (gfield::field-fix y))
       (equal (poly-coefficient 4 (list x y)) (gfield::field-zero))
       (equal (poly-coefficient 2 'atom) (gfield::field-zero))
       (equal (poly-coefficient 2 (cons x (cons y 'tail)))
              (gfield::field-zero))
       (equal (poly-coefficient n (normalize polynomial))
              (poly-coefficient n polynomial))
       (same-polynomial-coefficients-p count polynomial polynomial))
  :rule-classes nil)

(defthm canonical-equality-reconstruction-regression
  (implies (and (canonical-polynomial-p first)
                (canonical-polynomial-p second)
                (same-polynomial-coefficients-p
                 (max (len first) (len second)) first second))
           (equal first second))
  :rule-classes nil
  :hints (("Goal" :use canonical-polynomial-extensionality)))

(defthm unequal-length-canonical-agreement-regression
  (implies (and (canonical-polynomial-p first)
                (canonical-polynomial-p second)
                (not (equal (len first) (len second))))
           (not (same-polynomial-coefficients-p
                 (max (len first) (len second)) first second)))
  :rule-classes nil
  :hints
  (("Goal"
    :use canonical-polynomials-have-equal-length-from-coefficient-agreement)))
