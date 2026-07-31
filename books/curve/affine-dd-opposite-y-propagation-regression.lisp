(in-package "GFIELD")

(include-book "affine-dd-opposite-y-propagation")

(defthm affine-dd-opposite-y-propagation-client-regression
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope p)
        (affine-distinct-x-secant-relation-p b c r-slope q)
        (affine-opposite-y-infinity-relation-p p c infinity))
   (affine-opposite-y-infinity-relation-p a q infinity))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance affine-dd-opposite-y-propagates-to-other-tree))
    :in-theory (theory 'minimal-theory))))

(defthm affine-dd-opposite-y-left-tree-client-regression
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope c)
        (affine-distinct-x-secant-relation-p b c r-slope q)
        (affine-opposite-y-infinity-relation-p a q infinity))
   (affine-opposite-y-infinity-relation-p c c infinity))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance affine-dd-opposite-y-propagates-to-left-tree))
    :in-theory (theory 'minimal-theory))))
