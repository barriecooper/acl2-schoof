(in-package "GFIELD")

(include-book "curve-point-pair-output-point")

; Independent, classifier-free semantics for the affine inverse branch.  The
; distinguished result is compared after full-point fixing so that the
; relation respects the established total representation semantics.
(defun affine-opposite-y-infinity-relation-p (first second output)
  (and (short-weierstrass-affine-point-p first)
       (short-weierstrass-affine-point-p second)
       (equal (affine-coordinates-x first)
              (affine-coordinates-x second))
       (equal (affine-coordinates-y second)
              (field-neg (affine-coordinates-y first)))
       (equal (curve-point-fix output)
              (curve-point-infinity))))

(defthm affine-opposite-y-infinity-relation-p-of-fixes
  (equal (affine-opposite-y-infinity-relation-p
          (affine-coordinates-fix first)
          (affine-coordinates-fix second)
          (curve-point-fix output))
         (affine-opposite-y-infinity-relation-p first second output))
  :hints
  (("Goal"
    :use ((:instance short-weierstrass-affine-point-p-of-fix
                     (coordinates first))
          (:instance short-weierstrass-affine-point-p-of-fix
                     (coordinates second)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-opposite-y-infinity-relation-p
       affine-coordinates-x-of-fix
       affine-coordinates-y-of-fix
       curve-point-fix-idempotent)))))

(defthm affine-opposite-y-infinity-relation-p-symmetric
  (implies
   (affine-opposite-y-infinity-relation-p first second output)
   (affine-opposite-y-infinity-relation-p second first output))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance field-neg-of-neg
                     (x (affine-coordinates-y first))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-opposite-y-infinity-relation-p
       field-element-p-of-affine-coordinates-y
       field-fix-when-field-element-p)))))

(defthm affine-opposite-y-infinity-relation-output-determinate
  (implies
   (and (affine-opposite-y-infinity-relation-p first second output-a)
        (affine-opposite-y-infinity-relation-p first second output-b))
   (equal (curve-point-fix output-a)
          (curve-point-fix output-b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable affine-opposite-y-infinity-relation-p))))

(defthm affine-opposite-y-output-point-satisfies-infinity-relation
  (implies
   (and (short-weierstrass-affine-point-p first)
        (short-weierstrass-affine-point-p second)
        (equal (affine-coordinates-x first)
               (affine-coordinates-x second))
        (equal (affine-coordinates-y second)
               (field-neg (affine-coordinates-y first))))
   (affine-opposite-y-infinity-relation-p
    first second (affine-opposite-y-output-point first second)))
  :rule-classes nil
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-opposite-y-infinity-relation-p
       affine-opposite-y-output-point-is-infinity
       curve-point-fix-of-infinity)))))

; These two relations specify the two ordered infinity branches independently
; of classification and dispatch.  Membership is applied to fixed operands so
; every ACL2 object has exactly the meaning assigned by CURVE-POINT-FIX.
(defun curve-point-left-infinity-identity-relation-p (first second output)
  (and (short-weierstrass-curve-point-p (curve-point-fix first))
       (short-weierstrass-curve-point-p (curve-point-fix second))
       (equal (curve-point-fix first) (curve-point-infinity))
       (equal (curve-point-fix output) (curve-point-fix second))))

(defun curve-point-right-infinity-identity-relation-p (first second output)
  (and (short-weierstrass-curve-point-p (curve-point-fix first))
       (short-weierstrass-curve-point-p (curve-point-fix second))
       (equal (curve-point-fix second) (curve-point-infinity))
       (equal (curve-point-fix output) (curve-point-fix first))))

(defthm curve-point-left-infinity-identity-relation-p-of-fixes
  (equal (curve-point-left-infinity-identity-relation-p
          (curve-point-fix first) (curve-point-fix second)
          (curve-point-fix output))
         (curve-point-left-infinity-identity-relation-p first second output))
  :hints (("Goal" :in-theory
           (enable curve-point-left-infinity-identity-relation-p))))

(defthm curve-point-right-infinity-identity-relation-p-of-fixes
  (equal (curve-point-right-infinity-identity-relation-p
          (curve-point-fix first) (curve-point-fix second)
          (curve-point-fix output))
         (curve-point-right-infinity-identity-relation-p first second output))
  :hints (("Goal" :in-theory
           (enable curve-point-right-infinity-identity-relation-p))))

(defthm curve-point-left-infinity-identity-relation-output-determinate
  (implies
   (and (curve-point-left-infinity-identity-relation-p first second output-a)
        (curve-point-left-infinity-identity-relation-p first second output-b))
   (equal (curve-point-fix output-a) (curve-point-fix output-b)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (enable curve-point-left-infinity-identity-relation-p))))

(defthm curve-point-right-infinity-identity-relation-output-determinate
  (implies
   (and (curve-point-right-infinity-identity-relation-p first second output-a)
        (curve-point-right-infinity-identity-relation-p first second output-b))
   (equal (curve-point-fix output-a) (curve-point-fix output-b)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (enable curve-point-right-infinity-identity-relation-p))))

(defthm curve-point-pair-output-point-satisfies-left-infinity-identity-relation
  (implies
   (short-weierstrass-curve-point-p point)
   (curve-point-left-infinity-identity-relation-p
    (curve-point-infinity) point
    (curve-point-pair-output-point (curve-point-infinity) point)))
  :rule-classes nil
  :hints
  (("Goal"
    :use (short-weierstrass-curve-point-p-of-infinity)
    :in-theory
    (enable curve-point-left-infinity-identity-relation-p
            curve-point-pair-output-point-of-infinity-left
            curve-point-fix-when-representation-p
            short-weierstrass-curve-point-p
            curve-point-representation-p))))

(defthm curve-point-pair-output-point-satisfies-right-infinity-identity-relation
  (implies
   (short-weierstrass-curve-point-p point)
   (curve-point-right-infinity-identity-relation-p
    point (curve-point-infinity)
    (curve-point-pair-output-point point (curve-point-infinity))))
  :rule-classes nil
  :hints
  (("Goal"
    :use (short-weierstrass-curve-point-p-of-infinity)
    :in-theory
    (enable curve-point-right-infinity-identity-relation-p
            curve-point-pair-output-point-of-infinity-right
            curve-point-fix-when-representation-p
            short-weierstrass-curve-point-p
            curve-point-representation-p))))

(verify-guards affine-opposite-y-infinity-relation-p)
(verify-guards curve-point-left-infinity-identity-relation-p)
(verify-guards curve-point-right-infinity-identity-relation-p)
