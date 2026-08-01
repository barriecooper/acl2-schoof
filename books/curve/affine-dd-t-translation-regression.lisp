(in-package "GFIELD")

(include-book "affine-dd-t-translation")

(defthm affine-dd-t-translation-client-regression
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p-slope c)
    (affine-distinct-x-secant-relation-p b c r-slope q)
    (affine-doubling-relation-p c t-slope d))
   (or
    (affine-distinct-x-secant-relation-p
     a
     q
     (field-sub
      (field-add (field-fix p-slope)
                 (field-fix t-slope))
      (field-fix r-slope))
     d)
    (affine-doubling-relation-p
     a
     (field-sub
      (field-add (field-fix p-slope)
                 (field-fix t-slope))
      (field-fix r-slope))
     d)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance affine-dd-t-translation))
    :in-theory (theory 'minimal-theory))))
