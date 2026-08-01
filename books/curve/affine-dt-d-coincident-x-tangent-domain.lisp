(in-package "GFIELD")

(include-book "affine-dt-d-coincident-x-ordinate")

; Under the temporary self-inverse assumption at A, the certified ordinate
; equality constructs the exceptional relation from A to Q.  Mixed D/T
; propagation then contradicts the distinct-x domain of the second secant.
(defthm affine-dt-d-coincident-x-excludes-self-inverse
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
    :do-not '(preprocess)
    :use
    ((:instance affine-dt-d-coincident-x-implies-ordinate-equality)
     (:instance affine-dt-opposite-y-propagates-to-left-output
                (infinity (curve-point-infinity))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-secant-relation-p
       affine-doubling-relation-p
       affine-opposite-y-infinity-relation-p
       curve-point-fix-of-infinity)))))
