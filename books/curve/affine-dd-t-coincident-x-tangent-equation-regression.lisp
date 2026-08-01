(in-package "GFIELD")

(include-book "affine-dd-t-coincident-x-tangent-equation")

(defthm affine-dd-t-coincident-x-tangent-equation-client-regression
 (implies
  (and
   (affine-distinct-x-secant-relation-p a b p-slope c)
   (affine-distinct-x-secant-relation-p b c r-slope q)
   (affine-doubling-relation-p c t-slope d)
   (equal (affine-coordinates-x q) (affine-coordinates-x a)))
  (equal
   (field-mul
    (field-sub (field-add (field-fix p-slope) (field-fix t-slope))
               (field-fix r-slope))
    (field-add (affine-coordinates-y a) (affine-coordinates-y a)))
   (field-add
    (field-mul (field-add (field-add (field-one) (field-one)) (field-one))
               (field-mul (affine-coordinates-x a)
                          (affine-coordinates-x a)))
    (field-fix (short-weierstrass-a)))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance affine-dd-t-coincident-x-tangent-equation))
          :in-theory (theory 'minimal-theory))))
