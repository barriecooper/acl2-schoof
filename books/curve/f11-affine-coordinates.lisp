(in-package "GFIELD")

(include-book "affine-coordinates")
(include-book "f11-short-weierstrass")

; Concrete F11 instance of the generic two-list boundary.  As in the generic
; interface, every malformed outer representation denotes (0 0).
(defun f11-affine-coordinates-make (x y)
  (list (f11-fix x) (f11-fix y)))

(defun f11-affine-coordinates-x (coordinates)
  (if (and (true-listp coordinates) (equal (len coordinates) 2))
      (f11-fix (car coordinates))
    (f11-zero)))

(defun f11-affine-coordinates-y (coordinates)
  (if (and (true-listp coordinates) (equal (len coordinates) 2))
      (f11-fix (cadr coordinates))
    (f11-zero)))

(defun f11-affine-coordinates-fix (coordinates)
  (f11-affine-coordinates-make (f11-affine-coordinates-x coordinates)
                               (f11-affine-coordinates-y coordinates)))

(defun f11-affine-coordinates-p (coordinates)
  (equal (f11-affine-coordinates-fix coordinates) coordinates))

(defun f11-short-weierstrass-affine-point-p (coordinates)
  (f11-short-weierstrass-equation-p
   (f11-affine-coordinates-x coordinates)
   (f11-affine-coordinates-y coordinates)))

(assert-event (equal (f11-affine-coordinates-make 2 4) '(2 4)))
(assert-event (equal (f11-affine-coordinates-x '(2 4)) 2))
(assert-event (equal (f11-affine-coordinates-y '(2 4)) 4))
(assert-event (equal (f11-affine-coordinates-fix '(13 15)) '(2 4)))
(assert-event (f11-short-weierstrass-affine-point-p '(2 4)))
(assert-event (not (f11-short-weierstrass-affine-point-p '(2 5))))
(assert-event (f11-short-weierstrass-affine-point-p '(13 15)))
(assert-event (equal (f11-affine-coordinates-fix '(bad nil)) '(0 0)))
(assert-event (equal (f11-affine-coordinates-fix 'bad) '(0 0)))
(assert-event (equal (f11-affine-coordinates-fix '(2 4 7)) '(0 0)))
(assert-event (equal (f11-affine-coordinates-fix '(2 . 4)) '(0 0)))
(assert-event
 (equal (f11-affine-coordinates-fix
         (f11-affine-coordinates-fix '(13 15)))
        '(2 4)))

(verify-guards f11-affine-coordinates-make)
(verify-guards f11-affine-coordinates-x)
(verify-guards f11-affine-coordinates-y)
(verify-guards f11-affine-coordinates-fix)
(verify-guards f11-affine-coordinates-p)
(verify-guards f11-short-weierstrass-affine-point-p)
