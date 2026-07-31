(in-package "GFIELD")

(include-book "affine-inverse-secant-self-inverse")

(defthm short-weierstrass-common-root-discriminant-client-regression
  (implies
   (and
    (equal
     (field-add
      (field-mul
       (field-add (field-add (field-one) (field-one)) (field-one))
       (field-mul x x))
      (field-fix (short-weierstrass-a)))
     (field-zero))
    (equal
     (field-add
      (field-mul (field-mul x x) x)
      (field-add (field-mul (field-fix (short-weierstrass-a)) x)
                 (field-fix (short-weierstrass-b))))
     (field-zero)))
   (equal (short-weierstrass-discriminant-expression) (field-zero)))
  :rule-classes nil
  :hints
  (("Goal" :use ((:instance
                   short-weierstrass-common-root-implies-discriminant-zero))
    :in-theory (theory 'minimal-theory))))

(defthm affine-inverse-secant-self-inverse-client-regression
  (implies
   (and
    (short-weierstrass-characteristic-p)
    (affine-opposite-y-infinity-relation-p a b infinity)
    (affine-distinct-x-secant-relation-p b c slope output)
    (equal (affine-coordinates-x output) (affine-coordinates-x a)))
   (not (equal (affine-coordinates-y a)
               (field-neg (affine-coordinates-y a)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance affine-inverse-secant-coincident-x-excludes-self-inverse
                     (r slope) (u output)))
    :in-theory (theory 'minimal-theory))))
