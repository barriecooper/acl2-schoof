(in-package "GFIELD")

(include-book "affine-dt-d-outer-distinct-x-output-y")

; Direct semantic packaging of the three public scalar endpoints.  The input
; relations supply all curve-membership clauses, while the public outer
; disequality supplies the secant domain; only witness fixing is normalized.
(defthm affine-dt-d-outer-distinct-x-translation
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p-slope p-output)
    (affine-doubling-relation-p b t-slope q-output)
    (affine-distinct-x-secant-relation-p
     p-output b q-slope r-output)
    (not
     (equal (affine-coordinates-x q-output)
            (affine-coordinates-x a))))
   (affine-distinct-x-secant-relation-p
    a
    q-output
    (field-sub
     (field-add (field-fix p-slope)
                (field-fix q-slope))
     (field-fix t-slope))
    r-output))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance affine-dt-d-outer-distinct-x-slope-equation)
     (:instance affine-dt-d-outer-distinct-x-output-x-equation)
     (:instance affine-dt-d-outer-distinct-x-output-y-equation))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-secant-relation-p
       affine-doubling-relation-p
       field-sub field-fix-of-add field-fix-of-neg
       field-fix-idempotent)))))
