(in-package "GFIELD")

(include-book "curve-point-addition-relation")
(include-book "f11-affine-distinct-x-secant-relation")
(include-book "f11-affine-doubling-relation")
(include-book "f11-exceptional-addition-relations")

; Concrete substitution of the independent generic relation.  The slope
; arguments are mathematical field quotients and select no output branch.
(defun f11-curve-point-addition-relation-p (first second output)
  (let* ((first (f11-curve-point-fix first))
         (second (f11-curve-point-fix second))
         (output (f11-curve-point-fix output))
         (p (f11-curve-point-affine-coordinates-get first))
         (q (f11-curve-point-affine-coordinates-get second))
         (r (f11-curve-point-affine-coordinates-get output)))
    (and
     (f11-short-weierstrass-curve-point-p first)
     (f11-short-weierstrass-curve-point-p second)
     (or (f11-curve-point-left-infinity-identity-relation-p first second output)
         (f11-curve-point-right-infinity-identity-relation-p first second output)
         (and (equal first (f11-curve-point-affine-coordinates p))
              (equal second (f11-curve-point-affine-coordinates q))
              (or
               (and (equal output (f11-curve-point-affine-coordinates r))
                    (f11-affine-distinct-x-secant-relation-p
                     p q
                     (f11-div (f11-add (f11-affine-coordinates-y q)
                                       (f11-neg (f11-affine-coordinates-y p)))
                              (f11-add (f11-affine-coordinates-x q)
                                       (f11-neg (f11-affine-coordinates-x p))))
                     r))
               (f11-affine-opposite-y-infinity-relation-p p q output)
               (and (equal p q)
                    (equal output (f11-curve-point-affine-coordinates r))
                    (f11-affine-doubling-relation-p
                     p
                     (f11-div
                      (f11-add
                       (f11-mul (f11-add (f11-add (f11-one) (f11-one))
                                         (f11-one))
                                (f11-mul (f11-affine-coordinates-x p)
                                         (f11-affine-coordinates-x p)))
                       (f11-fix (f11-short-weierstrass-a)))
                      (f11-add (f11-affine-coordinates-y p)
                               (f11-affine-coordinates-y p)))
                     r))))))))

(assert-event
 (let ((infinity '(:infinity))
       (p '(:affine (2 4)))
       (q '(:affine (3 5)))
       (negative-p '(:affine (2 7))))
   (and
    (f11-curve-point-addition-relation-p
     infinity p (f11-curve-point-pair-output-point infinity p))
    (f11-curve-point-addition-relation-p
     p infinity (f11-curve-point-pair-output-point p infinity))
    (f11-curve-point-addition-relation-p
     infinity infinity
     (f11-curve-point-pair-output-point infinity infinity))
    (f11-curve-point-addition-relation-p
     p q (f11-curve-point-pair-output-point p q))
    (f11-curve-point-addition-relation-p
     p p (f11-curve-point-pair-output-point p p))
    (f11-curve-point-addition-relation-p
     p negative-p (f11-curve-point-pair-output-point p negative-p)))))

(verify-guards f11-curve-point-addition-relation-p)
