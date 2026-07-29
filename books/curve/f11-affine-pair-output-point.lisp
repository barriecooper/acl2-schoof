(in-package "GFIELD")

(include-book "affine-pair-output-point")
(include-book "f11-affine-distinct-x-output-point")
(include-book "f11-affine-opposite-y-output-point")
(include-book "f11-affine-same-point-non-opposite-output-point")
(include-book "f11-affine-pair-curve-classification")

(defun f11-affine-pair-output-point (first second)
  (let ((classification (f11-affine-pair-classify first second)))
    (cond ((equal classification :distinct-x)
           (f11-affine-distinct-x-output-point first second))
          ((equal classification :opposite-y)
           (f11-affine-opposite-y-output-point first second))
          ((equal classification :same-point-non-opposite)
           (f11-affine-same-point-non-opposite-output-point first))
          (t (f11-curve-point-infinity)))))

; Valid-input integration covers all three geometrically reachable branches.
(assert-event
 (and
  (equal (f11-affine-pair-output-point '(2 4) '(3 5))
         '(:affine (7 2)))
  (equal (f11-affine-pair-output-point '(2 4) '(2 7)) '(:infinity))
  (equal (f11-affine-pair-output-point '(2 4) '(2 4))
         '(:affine (5 9)))
  (f11-curve-point-representation-p
   (f11-affine-pair-output-point '(2 4) '(3 5)))
  (f11-curve-point-representation-p
   (f11-affine-pair-output-point '(2 4) '(2 7)))
  (f11-curve-point-representation-p
   (f11-affine-pair-output-point '(2 4) '(2 4)))
  (f11-short-weierstrass-curve-point-p
   (f11-affine-pair-output-point '(2 4) '(3 5)))
  (f11-short-weierstrass-curve-point-p
   (f11-affine-pair-output-point '(2 4) '(2 7)))
  (f11-short-weierstrass-curve-point-p
   (f11-affine-pair-output-point '(2 4) '(2 4)))
  (not (f11-curve-point-infinity-p
        (f11-affine-pair-output-point '(2 4) '(3 5))))
  (f11-curve-point-infinity-p
   (f11-affine-pair-output-point '(2 4) '(2 7)))
  (equal (f11-curve-point-affine-coordinates-get
          (f11-affine-pair-output-point '(2 4) '(2 4)))
         '(5 9))))

; This off-curve :same-x-other execution tests only the documented fallback.
(assert-event
 (and (equal (f11-affine-pair-classify '(2 4) '(2 5)) :same-x-other)
      (equal (f11-affine-pair-output-point '(2 4) '(2 5)) '(:infinity))
      (f11-curve-point-representation-p
       (f11-affine-pair-output-point '(2 4) '(2 5)))))

; Malformed inputs retain total affine fixing; they happen to classify as the
; self-inverse opposite-y case, independently of the fallback convention.
(assert-event
 (equal (f11-affine-pair-output-point 'bad '(0 0)) '(:infinity)))

(verify-guards f11-affine-pair-output-point)
