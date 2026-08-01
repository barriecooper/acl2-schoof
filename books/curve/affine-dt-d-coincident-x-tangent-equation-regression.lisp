(in-package "GFIELD")

(include-book "affine-dt-d-coincident-x-tangent-equation")

(defthm affine-dt-d-coincident-x-tangent-equation-client-regression
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p-slope p-output)
    (affine-doubling-relation-p b t-slope q-output)
    (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
    (equal (affine-coordinates-x q-output) (affine-coordinates-x a)))
   (equal
    (field-mul
     (field-sub
      (field-add (field-fix p-slope) (field-fix q-slope))
      (field-fix t-slope))
     (field-add (affine-coordinates-y a) (affine-coordinates-y a)))
    (field-add
     (field-mul
      (field-add (field-add (field-one) (field-one)) (field-one))
      (field-mul (affine-coordinates-x a) (affine-coordinates-x a)))
     (field-fix (short-weierstrass-a)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance affine-dt-d-coincident-x-tangent-equation))
    :in-theory (theory 'minimal-theory))))
