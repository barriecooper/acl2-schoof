(in-package "GFIELD")
(include-book "affine-dd-t-coincident-x-output-x")

(defthm affine-dd-t-coincident-x-output-x-client-regression
  (implies
   (and (affine-distinct-x-secant-relation-p a b p c)
        (affine-distinct-x-secant-relation-p b c r q)
        (affine-doubling-relation-p c t d)
        (equal (affine-coordinates-x q) (affine-coordinates-x a)))
   (equal (field-add (field-add (affine-coordinates-x d)
                                (affine-coordinates-x a))
                     (affine-coordinates-x a))
          (field-mul (field-sub (field-add (field-fix p) (field-fix t))
                                (field-fix r))
                     (field-sub (field-add (field-fix p) (field-fix t))
                                (field-fix r)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance affine-dd-t-coincident-x-output-x-equation
                                   (p-slope p) (r-slope r) (t-slope t)))
           :in-theory (theory 'minimal-theory))))
