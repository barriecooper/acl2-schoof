(in-package "GFIELD")

(include-book "affine-dd-t-coincident-x-output-y")

(defthm affine-dd-t-coincident-x-output-y-client-regression
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p-slope c)
    (affine-distinct-x-secant-relation-p b c r-slope q)
    (affine-doubling-relation-p c t-slope d)
    (equal (affine-coordinates-x q) (affine-coordinates-x a)))
   (equal
    (field-add (affine-coordinates-y d) (affine-coordinates-y a))
    (field-mul
     (field-sub (field-add (field-fix p-slope) (field-fix t-slope))
                (field-fix r-slope))
     (field-sub (affine-coordinates-x a)
                (affine-coordinates-x d)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance affine-dd-t-coincident-x-output-y-equation))
    :in-theory (theory 'minimal-theory))))
