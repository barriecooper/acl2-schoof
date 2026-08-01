(in-package "GFIELD")
(include-book "affine-dt-d-outer-distinct-x-slope")

(defthm affine-dt-d-outer-distinct-x-slope-equation-client-regression
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p-slope p-output)
    (affine-doubling-relation-p b t-slope q-output)
    (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
    (not (equal (affine-coordinates-x q-output) (affine-coordinates-x a))))
   (equal
    (field-mul
     (field-sub (field-add (field-fix p-slope) (field-fix q-slope))
                (field-fix t-slope))
     (field-sub (affine-coordinates-x q-output) (affine-coordinates-x a)))
    (field-sub (affine-coordinates-y q-output) (affine-coordinates-y a))))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance affine-dt-d-outer-distinct-x-slope-equation))
   :in-theory (theory 'minimal-theory))))
