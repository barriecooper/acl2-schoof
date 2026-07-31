(in-package "GFIELD")

(include-book "affine-dd-t-coincident-x-tangent-domain")

(defthm affine-dd-t-coincident-x-tangent-domain-client-regression
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p-slope c)
    (affine-distinct-x-secant-relation-p b c r-slope q)
    (affine-doubling-relation-p c t-slope d)
    (equal
     (affine-coordinates-x q)
     (affine-coordinates-x a)))
   (not
    (equal
     (affine-coordinates-y a)
     (field-neg (affine-coordinates-y a)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance affine-dd-t-coincident-x-excludes-self-inverse))
    :in-theory (theory 'minimal-theory))))
