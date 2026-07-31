(in-package "GFIELD")
(include-book "affine-dd-t-outer-distinct-x-output-x")
(defthm affine-dd-t-outer-distinct-x-output-x-equation-client-regression
  (implies
   (and (affine-distinct-x-secant-relation-p a b p c)
        (affine-distinct-x-secant-relation-p b c r q)
        (affine-doubling-relation-p c t-slope d)
        (not (equal (affine-coordinates-x q) (affine-coordinates-x a))))
   (equal
    (field-add (field-add (affine-coordinates-x d) (affine-coordinates-x a))
               (affine-coordinates-x q))
    (field-mul (field-sub (field-add (field-fix p) (field-fix t-slope)) (field-fix r))
               (field-sub (field-add (field-fix p) (field-fix t-slope)) (field-fix r)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance affine-dd-t-outer-distinct-x-output-x-equation))
            :in-theory (theory 'minimal-theory))))
