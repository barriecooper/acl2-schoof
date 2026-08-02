(in-package "GFIELD")

(include-book "curve-point-addition-relation")

(local
 (defthm infinity-is-not-tagged-affine-local
   (not (equal (curve-point-affine-coordinates coordinates)
               (curve-point-infinity)))
   :hints (("Goal" :in-theory
            (enable curve-point-affine-coordinates curve-point-infinity)))))

(local
 (defthm affine-fix-of-curve-point-get-local
   (equal (affine-coordinates-fix
           (curve-point-affine-coordinates-get point))
          (curve-point-affine-coordinates-get point))
   :hints (("Goal" :in-theory
            (enable curve-point-affine-coordinates-get)))))

; Expose one full semantic relation on affine operands as the three geometric
; relations used by the associativity assembly.  The witnesses below are the
; witnesses already selected by CURVE-POINT-ADDITION-RELATION-P; no branch is
; recomputed and the infinity case deliberately has no affine payload.
(defthm curve-point-addition-relation-affine-case-coverage
  (implies
   (and
    (short-weierstrass-affine-point-p a)
    (short-weierstrass-affine-point-p b)
    (curve-point-addition-relation-p
     (curve-point-affine-coordinates a)
     (curve-point-affine-coordinates b)
     output))
   (or
    (let ((payload (curve-point-affine-coordinates-get
                    (curve-point-fix output)))
          (slope (field-div
                  (field-sub (affine-coordinates-y (affine-coordinates-fix b))
                             (affine-coordinates-y (affine-coordinates-fix a)))
                  (field-sub (affine-coordinates-x (affine-coordinates-fix b))
                             (affine-coordinates-x (affine-coordinates-fix a))))))
      (and
       (equal (curve-point-fix output)
              (curve-point-affine-coordinates (affine-coordinates-fix payload)))
       (affine-distinct-x-secant-relation-p
        (affine-coordinates-fix a) (affine-coordinates-fix b)
        slope payload)))
    (affine-opposite-y-infinity-relation-p a b output)
    (let ((payload (curve-point-affine-coordinates-get
                    (curve-point-fix output)))
          (tangent
           (field-div
            (field-add
             (field-mul
              (field-add (field-add (field-one) (field-one)) (field-one))
              (field-mul (affine-coordinates-x (affine-coordinates-fix a))
                         (affine-coordinates-x (affine-coordinates-fix a))))
             (field-fix (short-weierstrass-a)))
            (field-add (affine-coordinates-y (affine-coordinates-fix a))
                       (affine-coordinates-y (affine-coordinates-fix a))))))
      (and
       (equal (curve-point-fix output)
              (curve-point-affine-coordinates (affine-coordinates-fix payload)))
       (equal (affine-coordinates-fix a)
              (affine-coordinates-fix b))
       (affine-doubling-relation-p (affine-coordinates-fix a) tangent payload)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance curve-point-addition-case-coverage
                (first (curve-point-affine-coordinates a))
                (second (curve-point-affine-coordinates b)))
     (:instance short-weierstrass-curve-point-p-of-affine
                (coordinates a))
     (:instance short-weierstrass-curve-point-p-of-affine
                (coordinates b))
     (:instance short-weierstrass-affine-point-p-of-fix
                (coordinates a))
     (:instance short-weierstrass-affine-point-p-of-fix
                (coordinates b))
     (:instance infinity-is-not-tagged-affine-local
                (coordinates (affine-coordinates-fix a)))
     (:instance infinity-is-not-tagged-affine-local
                (coordinates (affine-coordinates-fix b)))
     (:instance affine-fix-of-curve-point-get-local
                (point (curve-point-fix output)))
     (:instance affine-pair-classify-not-same-x-other-for-curve-points
                (first a) (second b)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(curve-point-addition-relation-p
       curve-point-left-infinity-identity-relation-p
       curve-point-right-infinity-identity-relation-p
       curve-point-fix-of-affine-coordinates
       curve-point-infinity-p-of-affine-coordinates
       curve-point-affine-coordinates-get-of-constructor
       curve-point-fix-idempotent
       affine-coordinates-fix-idempotent
       affine-distinct-x-secant-relation-p-of-fixes
       affine-opposite-y-infinity-relation-p-of-fixes
       affine-doubling-relation-p-of-fixes
       affine-coordinates-fix-when-affine-coordinates-p)))))

(defthm curve-point-addition-relation-output-determinate-under-fixed-operands
  (implies
   (and
    (curve-point-addition-relation-p first-a second-a output-a)
    (curve-point-addition-relation-p first-b second-b output-b)
    (equal (curve-point-fix first-a) (curve-point-fix first-b))
    (equal (curve-point-fix second-a) (curve-point-fix second-b)))
   (equal (curve-point-fix output-a) (curve-point-fix output-b)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance curve-point-addition-relation-output-determinate
                (first (curve-point-fix first-a))
                (second (curve-point-fix second-a))
                (output-a (curve-point-fix output-a))
                (output-b (curve-point-fix output-b)))
     (:instance curve-point-addition-relation-p-of-fixes
                (first first-a) (second second-a) (output output-a))
     (:instance curve-point-addition-relation-p-of-fixes
                (first first-b) (second second-b) (output output-b)))
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(curve-point-fix-idempotent)))))
