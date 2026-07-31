(in-package "GFIELD")

(include-book "affine-dd-t-coincident-x-ordinate")

(defthm affine-dd-t-coincident-x-ordinate-client-regression
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope c)
        (affine-distinct-x-secant-relation-p b c r-slope q)
        (affine-doubling-relation-p c t-slope d)
        (equal (affine-coordinates-x q)
               (affine-coordinates-x a)))
   (equal (affine-coordinates-y q)
          (affine-coordinates-y a)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance affine-dd-t-coincident-x-implies-ordinate-equality))
    :in-theory (theory 'minimal-theory))))
