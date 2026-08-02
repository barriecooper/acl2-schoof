(in-package "GFIELD")

(include-book "affine-mixed-outer-doubling-impossibility")

(defthm affine-dt-left-outer-doubling-impossible-client-regression
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p-slope p-output)
    (affine-doubling-relation-p b t-slope q-output)
    (equal (affine-coordinates-fix p-output)
           (affine-coordinates-fix b)))
   nil)
  :rule-classes nil
  :hints (("Goal" :use (affine-dt-left-outer-doubling-impossible)
           :in-theory (theory 'minimal-theory))))

(defthm affine-td-right-outer-doubling-impossible-client-regression
  (implies
   (and
    (affine-doubling-relation-p a t-slope p-output)
    (affine-distinct-x-secant-relation-p a b p-slope q-output)
    (equal (affine-coordinates-fix q-output)
           (affine-coordinates-fix a)))
   nil)
  :rule-classes nil
  :hints (("Goal" :use (affine-td-right-outer-doubling-impossible)
           :in-theory (theory 'minimal-theory))))
