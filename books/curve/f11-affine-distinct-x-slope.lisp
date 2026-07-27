(in-package "GFIELD")

(include-book "affine-distinct-x-slope")
(include-book "f11-affine-pair-classification")

; Concrete execution instance of the generic transparent formula.  This is
; not a second mathematical specification: it substitutes the named F11
; operations and accessors into the generic body, following the existing F11
; curve regression pattern.
(defun f11-affine-distinct-x-slope (first second)
  (f11-div
   (f11-add (f11-affine-coordinates-y second)
            (f11-neg (f11-affine-coordinates-y first)))
   (f11-add (f11-affine-coordinates-x second)
            (f11-neg (f11-affine-coordinates-x first)))))

; Denominator one.
(assert-event (equal (f11-affine-distinct-x-slope '(2 4) '(3 9)) 5))

; Nontrivial inverse: numerator 4, denominator 2, inverse 6, slope 2.
(assert-event
 (and (equal (f11-add (f11-affine-coordinates-y '(3 6))
                      (f11-neg (f11-affine-coordinates-y '(1 2)))) 4)
      (equal (f11-add (f11-affine-coordinates-x '(3 6))
                      (f11-neg (f11-affine-coordinates-x '(1 2)))) 2)
      (equal (f11-inv 2) 6)
      (equal (f11-affine-distinct-x-slope '(1 2) '(3 6)) 2)
      (equal (f11-mul 2 (f11-affine-distinct-x-slope '(1 2) '(3 6))) 4)
      (equal (f11-affine-pair-classify '(1 2) '(3 6)) :distinct-x)))

; Negative numerator fixes to 8: 2 / 1 in the ordered formula is 8.
(assert-event (equal (f11-affine-distinct-x-slope '(1 5) '(2 2)) 8))

; Noncanonical representatives fix to (1,2) and (3,6).
(assert-event (equal (f11-affine-distinct-x-slope '(12 13) '(14 17)) 2))

; A malformed first coordinate denotes (0,0): numerator 6, denominator 3,
; inverse 4, and total slope 2.
(assert-event
 (and (equal (f11-affine-coordinates-fix 'bad) '(0 0))
      (equal (f11-add (f11-affine-coordinates-y '(3 6))
                      (f11-neg (f11-affine-coordinates-y 'bad))) 6)
      (equal (f11-add (f11-affine-coordinates-x '(3 6))
                      (f11-neg (f11-affine-coordinates-x 'bad))) 3)
      (equal (f11-inv 3) 4)
      (equal (f11-affine-distinct-x-slope 'bad '(3 6)) 2)))

; Equal x lies outside the theorem's intended branch.  Total FIELD-DIV
; programming semantics give denominator zero, inverse zero, and slope zero.
(assert-event
 (and (not (equal (f11-affine-pair-classify '(2 4) '(2 7)) :distinct-x))
      (equal (f11-add (f11-affine-coordinates-y '(2 7))
                      (f11-neg (f11-affine-coordinates-y '(2 4)))) 3)
      (equal (f11-add (f11-affine-coordinates-x '(2 7))
                      (f11-neg (f11-affine-coordinates-x '(2 4)))) 0)
      (equal (f11-inv 0) 0)
      (equal (f11-affine-distinct-x-slope '(2 4) '(2 7)) 0)))

(verify-guards f11-affine-distinct-x-slope)
