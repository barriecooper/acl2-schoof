(in-package "GFIELD")

(include-book "affine-dd-t-outer-distinct-x-output-y")

; The three scalar endpoints have exactly the clauses required by the public
; secant relation.  Curve membership comes directly from the two input secants
; and the tangent relation; only fixing of the reconstructed witness remains
; to be normalized here.
(defthm affine-dd-t-outer-distinct-x-translation
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p c)
    (affine-distinct-x-secant-relation-p b c r q)
    (affine-doubling-relation-p c t-slope d)
    (not
     (equal (affine-coordinates-x q)
            (affine-coordinates-x a))))
   (affine-distinct-x-secant-relation-p
    a
    q
    (field-sub
     (field-add (field-fix p)
                (field-fix t-slope))
     (field-fix r))
    d))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance affine-dd-t-outer-distinct-x-slope-equation)
     (:instance affine-dd-t-outer-distinct-x-output-x-equation)
     (:instance affine-dd-t-outer-distinct-x-output-y-equation))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-secant-relation-p
       affine-doubling-relation-p
       field-sub field-fix-of-add field-fix-of-neg
       field-fix-idempotent)))))
