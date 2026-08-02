(in-package "GFIELD")

(include-book "affine-dt-d-coincident-x-output-y")

(local
 (defthm field-two-times-local
   (equal (field-mul (field-add (field-one) (field-one)) x)
          (field-add x x))
   :hints
   (("Goal"
     :in-theory (enable field-mul-left-distributive
                        field-fix-of-mul)))))

; Package the certified coincident-x domain and scalar endpoints directly into
; the public doubling relation.  The two secant relations supply curve
; membership; no coordinate reconstruction is repeated here.
(defthm affine-dt-d-coincident-x-translation
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
   (affine-doubling-relation-p
    a
    (field-sub
     (field-add (field-fix p-slope)
                (field-fix q-slope))
     (field-fix t-slope))
    r-output))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance affine-dt-d-coincident-x-excludes-self-inverse)
     (:instance affine-dt-d-coincident-x-tangent-equation)
     (:instance affine-dt-d-coincident-x-output-x-equation)
     (:instance affine-dt-d-coincident-x-output-y-equation))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-secant-relation-p
       affine-doubling-relation-p
       field-sub field-fix-of-add field-fix-of-neg
       field-fix-idempotent field-add-associative
       field-two-times-local)))))
