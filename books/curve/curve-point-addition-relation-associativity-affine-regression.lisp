(in-package "GFIELD")

(include-book "curve-point-addition-relation-associativity-affine")

; Public-interface regression: the client uses only Candidate C, with every
; extraction, matrix-cell, relation, classifier, and fixer definition opaque.
(defthm curve-point-addition-relation-associative-for-affine-inputs-client-regression
  (implies
   (and
    (short-weierstrass-characteristic-p)
    (short-weierstrass-affine-point-p a)
    (short-weierstrass-affine-point-p b)
    (short-weierstrass-affine-point-p c)
    (curve-point-addition-relation-p
     (curve-point-affine-coordinates a)
     (curve-point-affine-coordinates b)
     ab)
    (curve-point-addition-relation-p
     (curve-point-affine-coordinates b)
     (curve-point-affine-coordinates c)
     bc)
    (curve-point-addition-relation-p
     ab (curve-point-affine-coordinates c) left)
    (curve-point-addition-relation-p
     (curve-point-affine-coordinates a) bc right))
   (equal (curve-point-fix left)
          (curve-point-fix right)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance curve-point-addition-relation-associative-for-affine-inputs))
    :in-theory (theory 'minimal-theory))))
