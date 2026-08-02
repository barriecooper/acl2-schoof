(in-package "GFIELD")

(include-book "affine-pair-curve-classification")
(include-book "affine-dd-opposite-y-propagation")
(include-book "affine-doubling-relation")

; The opposite-y alternative for A,Q constructs the semantic exceptional
; relation locally.  Mirrored DD-O propagation then makes C opposite to itself,
; contradicting precisely the tangent-domain conjunct of doubling at C.
(defthm affine-dd-t-coincident-x-implies-ordinate-equality
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope c)
        (affine-distinct-x-secant-relation-p b c r-slope q)
        (affine-doubling-relation-p c t-slope d)
        (equal (affine-coordinates-x q)
               (affine-coordinates-x a)))
   (equal (affine-coordinates-y q)
          (affine-coordinates-y a)))
  :rule-classes nil
  :hints
  (("Goal"
    :do-not '(preprocess)
    :use
    ((:instance short-weierstrass-equal-x-implies-equal-or-neg-y
                (p a) (q q))
     (:instance affine-dd-opposite-y-propagates-to-left-tree
                (a a) (b b) (p-slope p-slope) (p c)
                (c c) (r-slope r-slope) (q q)
                (infinity (curve-point-infinity))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-secant-relation-p
       affine-doubling-relation-p
       affine-opposite-y-infinity-relation-p
       curve-point-fix-of-infinity)))))
