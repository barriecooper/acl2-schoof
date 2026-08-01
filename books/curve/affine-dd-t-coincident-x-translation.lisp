(in-package "GFIELD")

(include-book "affine-dd-t-coincident-x-output-y")

(local
 (defthm field-two-times-local
   (equal (field-mul (field-add (field-one) (field-one)) x)
          (field-add x x))
   :hints
   (("Goal"
     :in-theory (enable field-mul-left-distributive
                        field-fix-of-mul)))))

; Package the certified coincident-x domain and scalar endpoints directly into
; the public doubling relation.  Curve membership is inherited from the first
; input secant and the input doubling relation; no coordinate reconstruction is
; repeated here.
(defthm affine-dd-t-coincident-x-translation
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p-slope c)
    (affine-distinct-x-secant-relation-p b c r-slope q)
    (affine-doubling-relation-p c t-slope d)
    (equal
     (affine-coordinates-x q)
     (affine-coordinates-x a)))
   (affine-doubling-relation-p
    a
    (field-sub
     (field-add (field-fix p-slope)
                (field-fix t-slope))
     (field-fix r-slope))
    d))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance affine-dd-t-coincident-x-implies-ordinate-equality)
     (:instance affine-dd-t-coincident-x-excludes-self-inverse)
     (:instance affine-dd-t-coincident-x-tangent-equation)
     (:instance affine-dd-t-coincident-x-output-x-equation)
     (:instance affine-dd-t-coincident-x-output-y-equation))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-secant-relation-p
       affine-doubling-relation-p
       field-sub field-fix-of-add field-fix-of-neg
       field-fix-idempotent field-add-associative
       field-two-times-local)))))
