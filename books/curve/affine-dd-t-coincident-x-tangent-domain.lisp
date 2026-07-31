(in-package "GFIELD")

(include-book "affine-dd-t-coincident-x-ordinate")

; Under the temporary self-inverse assumption at A, the certified ordinate
; equality constructs the exceptional relation from A to Q.  Mirrored DD-O
; propagation then contradicts the tangent domain already present at C.
(defthm affine-dd-t-coincident-x-excludes-self-inverse
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
    :do-not '(preprocess)
    :use
    ((:instance affine-dd-t-coincident-x-implies-ordinate-equality)
     (:instance affine-dd-opposite-y-propagates-to-left-tree
                (infinity (curve-point-infinity))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-secant-relation-p
       affine-doubling-relation-p
       affine-opposite-y-infinity-relation-p
       curve-point-fix-of-infinity)))))
