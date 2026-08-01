(in-package "GFIELD")

(include-book "affine-dt-d-coincident-x-ordinate")

(defthm affine-dt-d-coincident-x-ordinate-client-regression
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p-slope p-output)
    (affine-doubling-relation-p b t-slope q-output)
    (affine-distinct-x-secant-relation-p
     p-output b q-slope r-output)
    (equal (affine-coordinates-x q-output)
           (affine-coordinates-x a)))
   (equal (affine-coordinates-y q-output)
          (affine-coordinates-y a)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  affine-dt-d-coincident-x-implies-ordinate-equality))
           :in-theory (theory 'minimal-theory))))
