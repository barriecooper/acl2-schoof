(in-package "GFIELD")

(include-book "affine-dt-d-translation")
(include-book "curve-point-addition-commutativity")

; Structural point-order mirror of AFFINE-DT-D-TRANSLATION.  Reversing the
; triple sends A,A,B to B,A,A, so the right outer secant A+Q is the left
; outer secant Q+A of the maintained D/T orientation.  Secant reversal
; preserves each witness; no scalar identity is used here.
(defthm affine-td-d-translation
  (implies
   (and
    (affine-doubling-relation-p
     a t-slope p-output)
    (affine-distinct-x-secant-relation-p
     a b p-slope q-output)
    (affine-distinct-x-secant-relation-p
     a q-output q-slope r-output))
   (or
    (affine-distinct-x-secant-relation-p
     p-output
     b
     (field-sub
      (field-add (field-fix p-slope)
                 (field-fix q-slope))
      (field-fix t-slope))
     r-output)
    (and
     (equal (affine-coordinates-fix p-output)
            (affine-coordinates-fix b))
     (affine-doubling-relation-p
      b
      (field-sub
       (field-add (field-fix p-slope)
                  (field-fix q-slope))
       (field-fix t-slope))
      r-output))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance affine-distinct-x-secant-relation-p-reverse
                (first a) (second b) (slope p-slope) (output q-output))
     (:instance affine-distinct-x-secant-relation-p-reverse
                (first a) (second q-output)
                (slope q-slope) (output r-output))
     (:instance affine-dt-d-translation
                (a b) (b a)
                (p-output q-output) (q-output p-output)
                (p-slope p-slope) (q-slope q-slope)
                (t-slope t-slope) (r-output r-output))
     (:instance affine-distinct-x-secant-relation-p-reverse
                (first b) (second p-output)
                (slope (field-sub
                        (field-add (field-fix p-slope)
                                   (field-fix q-slope))
                        (field-fix t-slope)))
                (output r-output)))
    :in-theory (theory 'minimal-theory))))
