(in-package "GFIELD")

(include-book "curve-point-addition-relation")
(include-book "point-negation")

; The inverse law is first established at the independent semantic boundary.
; The executable corollary below then follows from dispatcher soundness and
; fixed-output determinacy, without reopening the dispatcher's case tree.
(local
 (defthm curve-point-member-shape-local
   (implies
    (short-weierstrass-curve-point-p point)
    (or (equal point (curve-point-infinity))
        (equal point
               (curve-point-affine-coordinates
                (curve-point-affine-coordinates-get point)))))
   :rule-classes nil
   :hints
   (("Goal"
     :in-theory (enable short-weierstrass-curve-point-p
                        curve-point-representation-p)))))

(defthm curve-point-addition-relation-p-of-point-and-neg
  (implies
   (short-weierstrass-curve-point-p point)
   (curve-point-addition-relation-p
    point (curve-point-neg point) (curve-point-infinity)))
  :rule-classes nil
  :hints
  (("Goal"
    :use (curve-point-member-shape-local
          (:instance short-weierstrass-curve-point-p-of-neg
                     (point point)))
    :in-theory
    (enable curve-point-addition-relation-p
            affine-opposite-y-infinity-relation-p
            curve-point-right-infinity-identity-relation-p
            curve-point-neg
            short-weierstrass-curve-point-p
            curve-point-representation-p))))

(defthm curve-point-pair-output-point-of-point-and-neg
  (implies
   (short-weierstrass-curve-point-p point)
   (equal (curve-point-pair-output-point point (curve-point-neg point))
          (curve-point-infinity)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance curve-point-addition-relation-output-determinate
                (first point)
                (second (curve-point-neg point))
                (output-a
                 (curve-point-pair-output-point point
                                                (curve-point-neg point)))
                (output-b (curve-point-infinity)))
     (:instance curve-point-pair-output-point-satisfies-addition-relation
                (first point)
                (second (curve-point-neg point)))
     (:instance curve-point-addition-relation-p-of-point-and-neg)
     (:instance short-weierstrass-curve-point-p-of-neg
                (point point)))
    :in-theory
    (enable curve-point-fix-when-representation-p))))
