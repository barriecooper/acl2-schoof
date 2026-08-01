(in-package "GFIELD")

(include-book "affine-dt-d-coincident-x-tangent-domain")

(defthm affine-dt-d-coincident-x-tangent-domain-client-regression
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
   (not
    (equal
     (affine-coordinates-y a)
     (field-neg (affine-coordinates-y a)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance affine-dt-d-coincident-x-excludes-self-inverse))
    :in-theory (theory 'minimal-theory))))
