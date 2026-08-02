(in-package "GFIELD")

(include-book "curve-point-addition-relation-associativity-affine")

(local
 (defthm curve-point-addition-relation-p-of-fixed-operands-local
   (equal (curve-point-addition-relation-p
           (curve-point-fix first) (curve-point-fix second) output)
          (curve-point-addition-relation-p first second output))
   :hints
   (("Goal"
     :use
     ((:instance curve-point-addition-relation-p-of-fixes)
      (:instance curve-point-addition-relation-p-of-fixes
                 (first (curve-point-fix first))
                 (second (curve-point-fix second))))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(curve-point-fix-idempotent))))))

(local
 (defthm curve-point-addition-relation-p-of-fixed-second-local
   (equal (curve-point-addition-relation-p
           first (curve-point-fix second) output)
          (curve-point-addition-relation-p first second output))
   :hints
   (("Goal"
     :use
     ((:instance curve-point-addition-relation-p-of-fixed-operands-local)
      (:instance curve-point-addition-relation-p-of-fixed-operands-local
                 (second (curve-point-fix second))))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(curve-point-fix-idempotent))))))

(local
 (defthm curve-point-addition-relation-p-of-fixed-first-local
   (equal (curve-point-addition-relation-p
           (curve-point-fix first) second output)
          (curve-point-addition-relation-p first second output))
   :hints
   (("Goal"
     :use
     ((:instance curve-point-addition-relation-p-of-fixed-operands-local)
      (:instance curve-point-addition-relation-p-of-fixed-operands-local
                 (first (curve-point-fix first))))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(curve-point-fix-idempotent))))))

; Full tagged semantic associativity.  The proof only separates an original
; infinity input from three valid tagged affine inputs; it does not mention the
; executable dispatcher or inspect any geometric relation.
(defthm curve-point-addition-relation-associative
  (implies
   (and
    (short-weierstrass-characteristic-p)
    (short-weierstrass-curve-point-p a)
    (short-weierstrass-curve-point-p b)
    (short-weierstrass-curve-point-p c)

    (curve-point-addition-relation-p a b ab)
    (curve-point-addition-relation-p b c bc)
    (curve-point-addition-relation-p ab c left)
    (curve-point-addition-relation-p a bc right))
   (equal (curve-point-fix left)
          (curve-point-fix right)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (curve-point-addition-relation-associative-when-original-infinity
     (:instance short-weierstrass-curve-point-non-infinity-representation
                (point a))
     (:instance short-weierstrass-curve-point-non-infinity-representation
                (point b))
     (:instance short-weierstrass-curve-point-non-infinity-representation
                (point c))
     (:instance curve-point-addition-relation-p-of-fixed-operands-local
                (first a) (second b) (output ab))
     (:instance curve-point-addition-relation-p-of-fixed-operands-local
                (first b) (second c) (output bc))
     (:instance curve-point-addition-relation-p-of-fixed-second-local
                (first ab) (second c) (output left))
     (:instance curve-point-addition-relation-p-of-fixed-first-local
                (first a) (second bc) (output right))
     (:instance curve-point-addition-relation-associative-for-affine-inputs
                (a (curve-point-affine-coordinates-get (curve-point-fix a)))
                (b (curve-point-affine-coordinates-get (curve-point-fix b)))
                (c (curve-point-affine-coordinates-get (curve-point-fix c)))))
    :in-theory (theory 'minimal-theory))))
