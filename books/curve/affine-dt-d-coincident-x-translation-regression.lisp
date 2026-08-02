(in-package "GFIELD")

(include-book "affine-dt-d-coincident-x-translation")

(defthm affine-dt-d-coincident-x-translation-client-regression
  (implies
   (and
    (affine-distinct-x-secant-relation-p
     a b p-slope p-output)
    (affine-doubling-relation-p
     b t-slope q-output)
    (affine-distinct-x-secant-relation-p
     p-output b q-slope r-output)
    (equal
     (affine-coordinates-x q-output)
     (affine-coordinates-x a)))
   (affine-doubling-relation-p
    a
    (field-sub
     (field-add (field-fix p-slope)
                (field-fix q-slope))
     (field-fix t-slope))
    r-output))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance affine-dt-d-coincident-x-translation))
    :in-theory (theory 'minimal-theory))))
