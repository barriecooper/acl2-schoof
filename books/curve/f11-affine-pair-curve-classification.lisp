(in-package "GFIELD")

(include-book "affine-pair-curve-classification")
(include-book "f11-affine-pair-classification")

; The generic theorem is the logical boundary.  These focused F11 executions
; validate its intended same-curve cases and the retained off-curve fallback.
(assert-event
 (and (f11-short-weierstrass-affine-point-p '(2 4))
      (not (equal (f11-affine-pair-classify '(2 4) '(2 4))
                  :same-x-other))))
(assert-event
 (and (f11-short-weierstrass-affine-point-p '(2 4))
      (f11-short-weierstrass-affine-point-p '(2 7))
      (equal (f11-affine-pair-classify '(2 4) '(2 7)) :opposite-y)
      (equal (f11-affine-pair-classify '(2 7) '(2 4)) :opposite-y)))
(assert-event
 (and (f11-short-weierstrass-affine-point-p '(2 4))
      (f11-short-weierstrass-affine-point-p '(3 5))
      (equal (f11-affine-pair-classify '(2 4) '(3 5)) :distinct-x)))
(assert-event
 (and (f11-short-weierstrass-affine-point-p '(13 15))
      (f11-short-weierstrass-affine-point-p '(13 18))
      (equal (f11-affine-pair-classify '(13 15) '(13 18)) :opposite-y)))
(assert-event
 (and (not (f11-short-weierstrass-affine-point-p '(2 5)))
      (equal (f11-affine-pair-classify '(2 4) '(2 5)) :same-x-other)))
(assert-event
 (and (not (f11-short-weierstrass-affine-point-p '(0 0)))
      (equal (f11-affine-pair-classify '(0 0) '(0 0)) :opposite-y)))
