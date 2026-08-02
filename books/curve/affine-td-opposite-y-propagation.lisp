(in-package "GFIELD")

(include-book "affine-dt-opposite-y-propagation")
(include-book "curve-point-addition-commutativity")

; Maintained T/D orientation: A+A=P, A+B=Q, and P=-B imply A=-Q.
; This is the point-order mirror of the right-to-left D/T propagation theorem.
(defthm affine-td-left-output-opposite-y-propagates-to-right-output
  (implies
   (and (affine-doubling-relation-p a t-slope p-output)
        (affine-distinct-x-secant-relation-p a b p-slope q-output)
        (affine-opposite-y-infinity-relation-p p-output b infinity))
   (affine-opposite-y-infinity-relation-p a q-output infinity))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance affine-distinct-x-secant-relation-p-reverse
                (first a) (second b) (slope p-slope) (output q-output))
     (:instance affine-opposite-y-infinity-relation-p-symmetric
                (first p-output) (second b) (output infinity))
     (:instance affine-dt-opposite-y-propagates-to-left-output
                (a b) (b a)
                (p-slope p-slope) (p-output q-output)
                (t-slope t-slope) (q-output p-output)
                (infinity infinity))
     (:instance affine-opposite-y-infinity-relation-p-symmetric
                (first q-output) (second a) (output infinity)))
    :in-theory (theory 'minimal-theory))))
