(in-package "GFIELD")

(include-book "affine-pair-curve-classification")
(include-book "affine-dt-opposite-y-propagation")

(defthm affine-dt-d-coincident-x-implies-ordinate-equality
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
  :hints
  (("Goal"
    :do-not '(preprocess)
    :use
    ((:instance short-weierstrass-equal-x-implies-equal-or-neg-y
                (p a) (q q-output))
     (:instance affine-dt-opposite-y-propagates-to-left-output
                (infinity (curve-point-infinity))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-secant-relation-p
       affine-doubling-relation-p
       affine-opposite-y-infinity-relation-p
       curve-point-fix-of-infinity)))))
