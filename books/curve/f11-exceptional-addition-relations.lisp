(in-package "GFIELD")

(include-book "exceptional-addition-relations")
(include-book "f11-curve-point-pair-output-point")
(include-book "f11-affine-opposite-y-output-point")
(include-book "f11-short-weierstrass")

(defun f11-affine-opposite-y-infinity-relation-p (first second output)
  (and (f11-short-weierstrass-affine-point-p first)
       (f11-short-weierstrass-affine-point-p second)
       (equal (f11-affine-coordinates-x first)
              (f11-affine-coordinates-x second))
       (equal (f11-affine-coordinates-y second)
              (f11-neg (f11-affine-coordinates-y first)))
       (equal (f11-curve-point-fix output)
              (f11-curve-point-infinity))))

(defun f11-curve-point-left-infinity-identity-relation-p
  (first second output)
  (and (f11-short-weierstrass-curve-point-p (f11-curve-point-fix first))
       (f11-short-weierstrass-curve-point-p (f11-curve-point-fix second))
       (equal (f11-curve-point-fix first) (f11-curve-point-infinity))
       (equal (f11-curve-point-fix output) (f11-curve-point-fix second))))

(defun f11-curve-point-right-infinity-identity-relation-p
  (first second output)
  (and (f11-short-weierstrass-curve-point-p (f11-curve-point-fix first))
       (f11-short-weierstrass-curve-point-p (f11-curve-point-fix second))
       (equal (f11-curve-point-fix second) (f11-curve-point-infinity))
       (equal (f11-curve-point-fix output) (f11-curve-point-fix first))))

(assert-event
 (let* ((first '(2 4))
        (second '(2 7))
        (output (f11-affine-opposite-y-output-point first second)))
   (and (f11-short-weierstrass-affine-point-p first)
        (f11-short-weierstrass-affine-point-p second)
        (equal (f11-affine-coordinates-x first)
               (f11-affine-coordinates-x second))
        (equal (f11-affine-coordinates-y second)
               (f11-neg (f11-affine-coordinates-y first)))
        (equal output '(:infinity))
        (f11-affine-opposite-y-infinity-relation-p first second output))))

(assert-event
 (let ((point '(:affine (2 4))))
   (and
    (f11-curve-point-left-infinity-identity-relation-p
     '(:infinity) point
     (f11-curve-point-pair-output-point '(:infinity) point))
    (equal (f11-curve-point-pair-output-point '(:infinity) point) point)
    (f11-curve-point-right-infinity-identity-relation-p
     point '(:infinity)
     (f11-curve-point-pair-output-point point '(:infinity)))
    (equal (f11-curve-point-pair-output-point point '(:infinity)) point))))

(verify-guards f11-affine-opposite-y-infinity-relation-p)
(verify-guards f11-curve-point-left-infinity-identity-relation-p)
(verify-guards f11-curve-point-right-infinity-identity-relation-p)
