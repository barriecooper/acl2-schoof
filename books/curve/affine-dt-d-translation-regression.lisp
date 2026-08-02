(in-package "GFIELD")

(include-book "affine-dt-d-translation")

(defthm affine-dt-d-translation-client-regression
  (implies
   (and
    (affine-distinct-x-secant-relation-p
     a b p-slope p-output)
    (affine-doubling-relation-p
     b t-slope q-output)
    (affine-distinct-x-secant-relation-p
     p-output b q-slope r-output))
   (or
    (affine-distinct-x-secant-relation-p
     a
     q-output
     (field-sub
      (field-add (field-fix p-slope)
                 (field-fix q-slope))
      (field-fix t-slope))
     r-output)
    (affine-doubling-relation-p
     a
     (field-sub
      (field-add (field-fix p-slope)
                 (field-fix q-slope))
      (field-fix t-slope))
     r-output)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance affine-dt-d-translation))
    :in-theory (theory 'minimal-theory))))
