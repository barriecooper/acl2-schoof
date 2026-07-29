(in-package "GFIELD")

(include-book "affine-same-point-non-opposite-closure")

; A classifier-free and division-free specification of affine doubling.
; SLOPE is an explicit tangent witness.  The non-self-inverse y conjunct is
; the mathematical domain condition for the finite tangent branch.
(defun affine-doubling-relation-p (input slope output)
  (and
   (short-weierstrass-affine-point-p input)
   (not (equal (affine-coordinates-y input)
               (field-neg (affine-coordinates-y input))))
   (equal
    (field-mul
     (field-fix slope)
     (field-add (affine-coordinates-y input)
                (affine-coordinates-y input)))
    (field-add
     (field-mul
      (field-add (field-add (field-one) (field-one))
                 (field-one))
      (field-mul (affine-coordinates-x input)
                 (affine-coordinates-x input)))
     (field-fix (short-weierstrass-a))))
   (equal
    (field-add
     (affine-coordinates-x output)
     (field-mul (field-add (field-one) (field-one))
                (affine-coordinates-x input)))
    (field-mul (field-fix slope) (field-fix slope)))
   (equal
    (field-add (affine-coordinates-y output)
               (affine-coordinates-y input))
    (field-mul
     (field-fix slope)
     (field-sub (affine-coordinates-x input)
                (affine-coordinates-x output))))
   (short-weierstrass-affine-point-p output)))

(defthm affine-doubling-relation-p-of-fixes
  (equal
   (affine-doubling-relation-p
    (affine-coordinates-fix input)
    (field-fix slope)
    (affine-coordinates-fix output))
   (affine-doubling-relation-p input slope output))
  :hints
  (("Goal"
    :use
    ((:instance short-weierstrass-affine-point-p-of-fix
                (coordinates input))
     (:instance short-weierstrass-affine-point-p-of-fix
                (coordinates output)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-doubling-relation-p
       affine-coordinates-x-of-fix
       affine-coordinates-y-of-fix
       field-fix-idempotent)))))

(local
 (defthm field-mul-right-cancel-forward-local
   (implies
    (and (not (equal (field-fix denominator) (field-zero)))
         (equal (field-mul left denominator)
                (field-mul right denominator)))
    (equal (field-fix left) (field-fix right)))
   :hints
   (("Goal"
     :use ((:instance field-mul-left-cancel-forward
                      (x denominator) (y left) (z right))
           (:instance field-mul-commutative (x left) (y denominator))
           (:instance field-mul-commutative (x right) (y denominator)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-add-right-cancel-forward-local
   (implies
    (equal (field-add left common) (field-add right common))
    (equal (field-fix left) (field-fix right)))
   :hints
   (("Goal"
     :use ((:instance field-add-left-cancel-forward
                      (x common) (y left) (z right))
           (:instance field-add-commutative (x left) (y common))
           (:instance field-add-commutative (x right) (y common)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm non-self-inverse-y-implies-tangent-denominator-nonzero-local
   (implies
    (not (equal (affine-coordinates-y input)
                (field-neg (affine-coordinates-y input))))
    (not (equal
          (field-add (affine-coordinates-y input)
                     (affine-coordinates-y input))
          (field-zero))))
   :hints
   (("Goal"
     :use ((:instance field-additive-inverse-unique
                      (x (affine-coordinates-y input))
                      (y (affine-coordinates-y input))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-element-p-of-affine-coordinates-y
        field-fix-when-field-element-p))))))

(defthm affine-doubling-relation-slope-unique
  (implies
   (and (affine-doubling-relation-p input slope-a output-a)
        (affine-doubling-relation-p input slope-b output-b))
   (equal (field-fix slope-a) (field-fix slope-b)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (non-self-inverse-y-implies-tangent-denominator-nonzero-local
     (:instance field-mul-right-cancel-forward-local
                (left (field-fix slope-a))
                (right (field-fix slope-b))
                (denominator
                 (field-add (affine-coordinates-y input)
                            (affine-coordinates-y input)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-doubling-relation-p
       field-element-p-of-add
       field-fix-when-field-element-p
       field-fix-idempotent)))))

(defthm affine-doubling-relation-output-unique-at-fixed-slope
  (implies
   (and (affine-doubling-relation-p input slope-a output-a)
        (affine-doubling-relation-p input slope-b output-b)
        (equal (field-fix slope-a) (field-fix slope-b)))
   (equal (affine-coordinates-fix output-a)
          (affine-coordinates-fix output-b)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance field-add-right-cancel-forward-local
                (left (affine-coordinates-x output-a))
                (right (affine-coordinates-x output-b))
                (common
                 (field-mul (field-add (field-one) (field-one))
                            (affine-coordinates-x input))))
     (:instance field-add-right-cancel-forward-local
                (left (affine-coordinates-y output-a))
                (right (affine-coordinates-y output-b))
                (common (affine-coordinates-y input))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-doubling-relation-p
       affine-coordinates-fix
       affine-coordinates-make
       field-fix-when-field-element-p
       field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-coordinates-y
       field-fix-of-add
       field-fix-idempotent
       field-mul-fixed-congruence
       field-sub
       field-neg-of-fix)))))

(defthm affine-doubling-relation-unique
  (implies
   (and (affine-doubling-relation-p input slope-a output-a)
        (affine-doubling-relation-p input slope-b output-b))
   (and (equal (field-fix slope-a) (field-fix slope-b))
        (equal (affine-coordinates-fix output-a)
               (affine-coordinates-fix output-b))))
  :rule-classes nil
  :hints
  (("Goal"
    :use (affine-doubling-relation-slope-unique
          affine-doubling-relation-output-unique-at-fixed-slope)
    :in-theory (theory 'minimal-theory))))

(local
 (defthm non-self-inverse-y-implies-same-point-classification-local
   (implies
    (not (equal (affine-coordinates-y input)
                (field-neg (affine-coordinates-y input))))
    (equal (affine-pair-classify input input)
           :same-point-non-opposite))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance
            affine-pair-classify-same-point-non-opposite-characterization
            (first input) (second input)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(affine-coordinates-x-of-fix
        affine-coordinates-y-of-fix))))))

(defthm affine-same-point-non-opposite-output-satisfies-doubling-relation
  (implies
   (and (short-weierstrass-affine-point-p input)
        (not (equal (affine-coordinates-y input)
                    (field-neg (affine-coordinates-y input)))))
   (affine-doubling-relation-p
    input
    (affine-same-point-non-opposite-slope input)
    (affine-same-point-non-opposite-output input)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (non-self-inverse-y-implies-same-point-classification-local
     (:instance
      affine-same-point-non-opposite-slope-reconstructs-tangent-numerator
      (first input) (second input))
     (:instance affine-same-point-non-opposite-output-x-rearrangement
                (first input))
     (:instance affine-same-point-non-opposite-output-y-rearrangement
                (first input))
     (:instance
      short-weierstrass-affine-point-p-of-affine-same-point-non-opposite-output
      (first input) (second input)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-doubling-relation-p
       field-fix-of-affine-same-point-non-opposite-slope
       affine-coordinates-x-of-affine-same-point-non-opposite-output
       affine-coordinates-y-of-affine-same-point-non-opposite-output)))))

(verify-guards affine-doubling-relation-p)
