(in-package "GFIELD")

(include-book "affine-dd-t-coincident-x-translation")
(include-book "affine-dd-t-outer-distinct-x-translation")

; The two certified DD-T branches are exhaustive on outer x-coordinate
; equality.  Keep their common witness syntactically unchanged and expose only
; the three input relations at this public semantic boundary.
(defthm affine-dd-t-translation
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p-slope c)
    (affine-distinct-x-secant-relation-p b c r-slope q)
    (affine-doubling-relation-p c t-slope d))
   (or
    (affine-distinct-x-secant-relation-p
     a
     q
     (field-sub
      (field-add (field-fix p-slope)
                 (field-fix t-slope))
      (field-fix r-slope))
     d)
    (affine-doubling-relation-p
     a
     (field-sub
      (field-add (field-fix p-slope)
                 (field-fix t-slope))
      (field-fix r-slope))
     d)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance affine-dd-t-coincident-x-translation)
          (:instance affine-dd-t-outer-distinct-x-translation
                     (p p-slope)
                     (r r-slope)))
    :cases ((equal (affine-coordinates-x q)
                   (affine-coordinates-x a)))
    :in-theory (theory 'minimal-theory))))
