(in-package "GFIELD")

(include-book "affine-dd-t-outer-distinct-x-translation")

(defthm affine-dd-t-outer-distinct-x-translation-client-regression
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p c)
    (affine-distinct-x-secant-relation-p b c r q)
    (affine-doubling-relation-p c t-slope d)
    (not
     (equal (affine-coordinates-x q)
            (affine-coordinates-x a))))
   (affine-distinct-x-secant-relation-p
    a
    q
    (field-sub
     (field-add (field-fix p)
                (field-fix t-slope))
     (field-fix r))
    d))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance affine-dd-t-outer-distinct-x-translation))
    :in-theory (theory 'minimal-theory))))
