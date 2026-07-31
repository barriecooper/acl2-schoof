(in-package "GFIELD")

(include-book "affine-inverse-secant-repeated-root")

(defthm field-repeated-root-relation-client-regression
  (implies
   (and (equal (field-sub (field-mul yc yc) (field-mul ya ya))
               (field-mul (field-sub xc xa) factor))
        (equal (field-mul slope (field-sub xc xa))
               (field-add yc ya))
        (field-element-p xa) (field-element-p xc)
        (field-element-p factor)
        (not (equal xc xa)))
   (equal (field-mul slope (field-sub yc ya)) factor))
  :rule-classes nil
  :hints (("Goal" :use ((:instance
                          field-secant-line-and-curve-factorization-imply-repeated-root-relation
                          (r slope) (curve-factor factor)))
           :in-theory (theory 'minimal-theory))))

(defthm affine-repeated-root-relation-client-regression
  (implies
   (and (affine-opposite-y-infinity-relation-p a b infinity)
        (affine-distinct-x-secant-relation-p b c slope output)
        (equal (affine-coordinates-x output)
               (affine-coordinates-x a)))
   (equal
    (field-mul (field-fix slope)
               (field-sub (affine-coordinates-y c)
                          (affine-coordinates-y a)))
    (field-add
     (field-add
      (field-add
       (field-mul (affine-coordinates-x c) (affine-coordinates-x c))
       (field-mul (affine-coordinates-x c) (affine-coordinates-x a)))
      (field-mul (affine-coordinates-x a) (affine-coordinates-x a)))
     (field-fix (short-weierstrass-a)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance
                          affine-inverse-secant-coincident-x-implies-repeated-root-relation
                          (r slope) (u output)))
           :in-theory (theory 'minimal-theory))))
