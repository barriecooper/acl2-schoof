(in-package "GFIELD")

(include-book "affine-td-d-translation")

(defthm affine-td-d-translation-client-regression
  (implies
   (and
    (affine-doubling-relation-p a t-slope p-output)
    (affine-distinct-x-secant-relation-p a b p-slope q-output)
    (affine-distinct-x-secant-relation-p
     a q-output q-slope r-output))
   (or
    (affine-distinct-x-secant-relation-p
     p-output b
     (field-sub
      (field-add (field-fix p-slope) (field-fix q-slope))
      (field-fix t-slope))
     r-output)
    (affine-doubling-relation-p
     b
     (field-sub
      (field-add (field-fix p-slope) (field-fix q-slope))
      (field-fix t-slope))
     r-output)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance affine-td-d-translation))
    :in-theory (theory 'minimal-theory))))
