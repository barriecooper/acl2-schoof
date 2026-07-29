(in-package "GFIELD")
(include-book "curve-point-addition-commutativity")
(include-book "f11-curve-point-addition-relation")

(assert-event
 (let ((infinity '(:infinity)) (p '(:affine (2 4)))
       (q '(:affine (3 5))) (negative-p '(:affine (2 7))))
   (and
    (equal (f11-curve-point-pair-output-point p q)
           (f11-curve-point-pair-output-point q p))
    (f11-curve-point-addition-relation-p
     p q (f11-curve-point-pair-output-point p q))
    (f11-curve-point-addition-relation-p
     q p (f11-curve-point-pair-output-point p q))
    (equal (f11-curve-point-pair-output-point p p)
           (f11-curve-point-pair-output-point p p))
    (equal (f11-curve-point-pair-output-point p negative-p)
           (f11-curve-point-pair-output-point negative-p p))
    (equal (f11-curve-point-pair-output-point infinity p)
           (f11-curve-point-pair-output-point p infinity)))))
