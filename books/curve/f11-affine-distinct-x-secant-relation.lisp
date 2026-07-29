(in-package "GFIELD")

(include-book "affine-distinct-x-secant-relation")
(include-book "f11-affine-distinct-x-output")
(include-book "f11-short-weierstrass")

; Named-field substitution into the transparent relation for focused
; execution.  This is a concrete regression instance, not an alternative
; generic specification.
(defun f11-affine-distinct-x-secant-relation-p
     (first second slope output)
   (and
    (f11-short-weierstrass-affine-point-p first)
    (f11-short-weierstrass-affine-point-p second)
    (not (equal (f11-affine-coordinates-x first)
                (f11-affine-coordinates-x second)))
    (equal
     (f11-mul
      (f11-fix slope)
      (f11-add (f11-affine-coordinates-x second)
               (f11-neg (f11-affine-coordinates-x first))))
     (f11-add (f11-affine-coordinates-y second)
              (f11-neg (f11-affine-coordinates-y first))))
    (equal
     (f11-add
      (f11-add (f11-affine-coordinates-x output)
               (f11-affine-coordinates-x first))
      (f11-affine-coordinates-x second))
     (f11-mul (f11-fix slope) (f11-fix slope)))
    (equal
     (f11-add (f11-affine-coordinates-y output)
              (f11-affine-coordinates-y first))
     (f11-mul
      (f11-fix slope)
      (f11-add (f11-affine-coordinates-x first)
               (f11-neg (f11-affine-coordinates-x output)))))
    (f11-short-weierstrass-affine-point-p output)))

(assert-event
 (let* ((first '(2 4))
        (second '(3 5))
        (slope (f11-affine-distinct-x-slope first second))
        (output (f11-affine-distinct-x-output first second)))
   (and (equal slope 1)
        (equal output '(7 2))
        (f11-affine-distinct-x-secant-relation-p
         first second slope output))))

(verify-guards f11-affine-distinct-x-secant-relation-p)
