(in-package "GFIELD")

(include-book "affine-dd-t-coincident-x-translation")

(defthm affine-dd-t-coincident-x-translation-client-regression
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p-slope c)
    (affine-distinct-x-secant-relation-p b c r-slope q)
    (affine-doubling-relation-p c t-slope d)
    (equal
     (affine-coordinates-x q)
     (affine-coordinates-x a)))
   (affine-doubling-relation-p
    a
    (field-sub
     (field-add (field-fix p-slope)
                (field-fix t-slope))
     (field-fix r-slope))
    d))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance affine-dd-t-coincident-x-translation))
    :in-theory (theory 'minimal-theory))))
