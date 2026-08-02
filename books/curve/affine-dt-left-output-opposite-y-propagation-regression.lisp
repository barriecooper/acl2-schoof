(in-package "GFIELD")

(include-book "affine-dt-left-output-opposite-y-propagation")

(defthm affine-dt-left-output-opposite-y-propagation-client-regression
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
        (affine-doubling-relation-p b t-slope q-output)
        (affine-opposite-y-infinity-relation-p p-output b infinity))
   (affine-opposite-y-infinity-relation-p a q-output infinity))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      affine-dt-left-output-opposite-y-propagates-to-right-output))
    :in-theory (theory 'minimal-theory))))
