(in-package "GFIELD")
(include-book "xcert-semantics")
(include-book "f11-affine-distinct-x-output")

; A=(2,4), B=(3,5), C=(2,4).  Both inner outputs are (7,2), so all
; four ordered pairs used by the public semantic theorem are distinct-x.
(assert-event
 (let* ((a '(2 4)) (b '(3 5)) (c '(2 4))
        (ab (f11-affine-distinct-x-output a b))
        (bc (f11-affine-distinct-x-output b c)))
   (and (f11-short-weierstrass-affine-point-p a)
        (f11-short-weierstrass-affine-point-p b)
        (f11-short-weierstrass-affine-point-p c)
        (equal ab '(7 2)) (equal bc '(7 2))
        (equal (f11-affine-pair-classify a b) :distinct-x)
        (equal (f11-affine-pair-classify b c) :distinct-x)
        (equal (f11-affine-pair-classify ab c) :distinct-x)
        (equal (f11-affine-pair-classify a bc) :distinct-x)
        (equal (f11-affine-distinct-x-slope a b) 1)
        (equal (f11-affine-distinct-x-slope ab c) 4)
        (equal (f11-affine-distinct-x-slope b c) 1)
        (equal (f11-affine-distinct-x-slope a bc) 4)
        (equal (f11-affine-coordinates-x
                (f11-affine-distinct-x-output ab c)) 7)
        (equal (f11-affine-coordinates-x
                (f11-affine-distinct-x-output a bc)) 7)
        (equal (f11-affine-coordinates-y
                (f11-affine-distinct-x-output ab c)) 9)
        (equal (f11-affine-coordinates-y
                (f11-affine-distinct-x-output a bc)) 9)
        (equal (f11-affine-distinct-x-output ab c)
               (f11-affine-distinct-x-output a bc))
        (equal (f11-affine-distinct-x-output ab c) '(7 9))
        (equal
         (f11-add
          (f11-add (f11-affine-distinct-x-slope a b)
                   (f11-affine-distinct-x-slope ab c))
          (f11-neg (f11-add (f11-affine-distinct-x-slope b c)
                            (f11-affine-distinct-x-slope a bc))))
         (f11-zero)))))
