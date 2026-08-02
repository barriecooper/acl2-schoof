(in-package "GFIELD")

(include-book "affine-td-opposite-y-propagation")

(defthm affine-td-opposite-y-propagation-client-regression
  (implies
   (and (affine-doubling-relation-p a t-slope p-output)
        (affine-distinct-x-secant-relation-p a b p-slope q-output)
        (affine-opposite-y-infinity-relation-p p-output b infinity))
   (affine-opposite-y-infinity-relation-p a q-output infinity))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance
           affine-td-left-output-opposite-y-propagates-to-right-output))
    :in-theory (theory 'minimal-theory))))
