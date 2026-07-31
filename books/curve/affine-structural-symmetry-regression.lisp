(in-package "GFIELD")

(include-book "curve-point-addition-commutativity")

(defthm affine-distinct-x-secant-reversal-client-regression
  (implies
   (affine-distinct-x-secant-relation-p first second slope output)
   (affine-distinct-x-secant-relation-p second first slope output))
  :rule-classes nil
  :hints (("Goal" :use ((:instance affine-distinct-x-secant-relation-p-reverse))
           :in-theory (theory 'minimal-theory))))

(defthm affine-opposite-y-symmetry-client-regression
  (implies
   (affine-opposite-y-infinity-relation-p first second output)
   (affine-opposite-y-infinity-relation-p second first output))
  :rule-classes nil
  :hints (("Goal" :use ((:instance affine-opposite-y-infinity-relation-p-symmetric))
           :in-theory (theory 'minimal-theory))))
