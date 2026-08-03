(in-package "GPOLY")
(include-book "derivative")

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

(defthm coefficient-addition-regression
  (equal (poly-coefficient n (poly-add first second))
         (gfield::field-add (poly-coefficient n first)
                            (poly-coefficient n second)))
  :hints (("Goal" :use poly-coefficient-of-poly-add
           :in-theory (disable poly-add))))

(defthm coefficient-scaling-regression
  (equal (poly-coefficient n (poly-scale scalar polynomial))
         (gfield::field-mul scalar (poly-coefficient n polynomial)))
  :hints (("Goal" :use poly-coefficient-of-poly-scale
           :in-theory (disable poly-scale))))

(defthm coefficient-product-regression
  (equal (poly-coefficient n (poly-mul first second))
         (poly-convolution-sum n first second))
  :hints (("Goal" :use poly-coefficient-of-poly-mul
           :in-theory (disable poly-mul))))

(defthm convolution-two-term-regression
  (equal (poly-convolution-sum 1 first second)
         (gfield::field-add
          (gfield::field-mul (poly-coefficient 0 first)
                             (poly-coefficient 1 second))
          (gfield::field-mul (poly-coefficient 1 first)
                             (poly-coefficient 0 second))))
  :hints (("Goal" :in-theory (enable poly-convolution-sum
                                      poly-convolution-sum-aux))))


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
