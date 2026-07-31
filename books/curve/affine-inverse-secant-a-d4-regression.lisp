(in-package "GFIELD")

(include-book "affine-inverse-secant-a-d4")

(defthm field-inverse-secant-a-d4-client-regression
  (implies
   (and
    (equal
     (field-mul slope (field-sub yc ya))
     (field-add
      (field-add
       (field-add (field-mul xc xc) (field-mul xc xa))
       (field-mul xa xa))
      coefficient))
    (equal (field-mul slope (field-sub xc xa)) (field-add yc ya))
    (equal (field-mul slope slope) (field-add (field-add xc xa) xa)))
   (equal
    (field-mul (field-neg slope) (field-add ya ya))
    (field-add
     (field-mul
      (field-add (field-add (field-one) (field-one)) (field-one))
      (field-mul xa xa))
     coefficient)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance
                          field-repeated-root-and-secant-output-imply-tangent-equation
                          (r slope) (curve-a coefficient)))
           :in-theory (theory 'minimal-theory))))

(defthm affine-inverse-secant-a-d4-client-regression
  (implies
   (and (affine-opposite-y-infinity-relation-p a b infinity)
        (affine-distinct-x-secant-relation-p b c slope output)
        (equal (affine-coordinates-x output)
               (affine-coordinates-x a)))
   (equal
    (field-mul (field-neg (field-fix slope))
               (field-add (affine-coordinates-y a)
                          (affine-coordinates-y a)))
    (field-add
     (field-mul
      (field-add (field-add (field-one) (field-one)) (field-one))
      (field-mul (affine-coordinates-x a)
                 (affine-coordinates-x a)))
     (field-fix (short-weierstrass-a)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance
                          affine-inverse-secant-coincident-x-implies-tangent-equation
                          (r slope) (u output)))
           :in-theory (theory 'minimal-theory))))
