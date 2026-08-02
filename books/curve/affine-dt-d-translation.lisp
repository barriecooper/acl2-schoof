(in-package "GFIELD")

(include-book "affine-dt-d-coincident-x-translation")
(include-book "affine-dt-d-outer-distinct-x-translation")

; The two certified left-outer-secant branches are exhaustive on the equality
; of the right outer inputs' x-coordinates.  Their witness is deliberately
; identical, so this boundary performs only the semantic case split.
(defthm affine-dt-d-translation
  (implies
   (and
    (affine-distinct-x-secant-relation-p
     a b p-slope p-output)
    (affine-doubling-relation-p
     b t-slope q-output)
    (affine-distinct-x-secant-relation-p
     p-output b q-slope r-output))
   (or
    (affine-distinct-x-secant-relation-p
     a
     q-output
     (field-sub
      (field-add (field-fix p-slope)
                 (field-fix q-slope))
      (field-fix t-slope))
     r-output)
    (and
     (equal (affine-coordinates-fix a)
            (affine-coordinates-fix q-output))
     (affine-doubling-relation-p
      a
      (field-sub
       (field-add (field-fix p-slope)
                  (field-fix q-slope))
       (field-fix t-slope))
      r-output))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance affine-dt-d-coincident-x-translation)
          (:instance affine-dt-d-coincident-x-implies-ordinate-equality)
          (:instance affine-dt-d-outer-distinct-x-translation))
    :cases ((equal (affine-coordinates-x q-output)
                   (affine-coordinates-x a)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-coordinates-fix affine-coordinates-make)))))
