(in-package "GFIELD")
(include-book "affine-dt-d-coincident-x-output-x")

(defthm affine-dt-d-coincident-x-output-x-equation-client-regression
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
        (affine-doubling-relation-p b t-slope q-output)
        (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
        (equal (affine-coordinates-x q-output) (affine-coordinates-x a)))
   (equal
    (field-add (field-add (affine-coordinates-x r-output)
                          (affine-coordinates-x a))
               (affine-coordinates-x a))
    (field-mul
     (field-sub (field-add (field-fix p-slope) (field-fix q-slope))
                (field-fix t-slope))
     (field-sub (field-add (field-fix p-slope) (field-fix q-slope))
                (field-fix t-slope)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance affine-dt-d-coincident-x-output-x-equation))
           :in-theory (theory 'minimal-theory))))
