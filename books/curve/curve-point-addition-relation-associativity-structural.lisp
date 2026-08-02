(in-package "GFIELD")

(include-book "curve-addition-structural-interface")

; Structural consequences of the semantic branch relations.  The public
; theorems below deliberately mention only relation witnesses and fixed
; outputs; in particular, they do not depend on the executable dispatcher.

(local
 (defthm opposite-y-relation-chain-implies-fixed-endpoints-equal-local
   (implies
    (and (affine-opposite-y-infinity-relation-p a b ab)
         (affine-opposite-y-infinity-relation-p b c bc))
    (equal (affine-coordinates-fix a)
           (affine-coordinates-fix c)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-pair-classify-opposite-y-characterization
                 (first a) (second b))
      (:instance affine-pair-classify-opposite-y-characterization
                 (first b) (second c))
      (:instance affine-pair-classify-opposite-y-chain-implies-fixed-endpoints-equal))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(affine-opposite-y-infinity-relation-p
        affine-coordinates-x-of-fix
        affine-coordinates-y-of-fix))))))

(local
 (defthm opposite-y-relation-left-identity-witness-local
   (implies
    (and (affine-opposite-y-infinity-relation-p a b ab)
         (affine-opposite-y-infinity-relation-p b c bc))
    (curve-point-addition-relation-p
     ab (curve-point-affine-coordinates c)
     (curve-point-affine-coordinates c)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance short-weierstrass-curve-point-p-of-affine
                      (coordinates c))
           (:instance short-weierstrass-curve-point-p-of-affine
                      (coordinates (affine-coordinates-fix c)))
           (:instance short-weierstrass-affine-point-p-of-fix
                      (coordinates c))
           short-weierstrass-curve-point-p-of-infinity)
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(affine-opposite-y-infinity-relation-p
        curve-point-addition-relation-p
        curve-point-left-infinity-identity-relation-p
        curve-point-fix-idempotent
        curve-point-fix-of-affine-coordinates
        affine-coordinates-fix-idempotent))))))

(local
 (defthm opposite-y-relation-implies-left-infinity-outer-local
   (implies
    (and (affine-opposite-y-infinity-relation-p a b ab)
         (affine-opposite-y-infinity-relation-p b c bc)
         (curve-point-addition-relation-p
          ab (curve-point-affine-coordinates c) left))
    (equal (curve-point-fix left)
           (curve-point-fix (curve-point-affine-coordinates c))))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     (opposite-y-relation-left-identity-witness-local
      (:instance curve-point-addition-relation-output-determinate
                 (first ab)
                 (second (curve-point-affine-coordinates c))
                 (output-a left)
                 (output-b (curve-point-affine-coordinates c))))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(curve-point-fix-idempotent))))))

(local
 (defthm opposite-y-relation-right-identity-witness-local
   (implies
    (and (affine-opposite-y-infinity-relation-p a b ab)
         (affine-opposite-y-infinity-relation-p b c bc))
    (curve-point-addition-relation-p
     (curve-point-affine-coordinates a) bc
     (curve-point-affine-coordinates a)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance short-weierstrass-curve-point-p-of-affine
                      (coordinates a))
           (:instance short-weierstrass-curve-point-p-of-affine
                      (coordinates (affine-coordinates-fix a)))
           (:instance short-weierstrass-affine-point-p-of-fix
                      (coordinates a))
           short-weierstrass-curve-point-p-of-infinity)
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(affine-opposite-y-infinity-relation-p
        curve-point-addition-relation-p
        curve-point-right-infinity-identity-relation-p
        curve-point-fix-idempotent
        curve-point-fix-of-affine-coordinates
        affine-coordinates-fix-idempotent))))))

(local
 (defthm opposite-y-relation-implies-right-infinity-outer-local
   (implies
    (and (affine-opposite-y-infinity-relation-p a b ab)
         (affine-opposite-y-infinity-relation-p b c bc)
         (curve-point-addition-relation-p
          (curve-point-affine-coordinates a) bc right))
    (equal (curve-point-fix right)
           (curve-point-fix (curve-point-affine-coordinates a))))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     (opposite-y-relation-right-identity-witness-local
      (:instance curve-point-addition-relation-output-determinate
                 (first (curve-point-affine-coordinates a))
                 (second bc)
                 (output-a right)
                 (output-b (curve-point-affine-coordinates a))))
     :in-theory (theory 'minimal-theory)))))

(defthm curve-point-addition-relation-associative-when-both-inner-opposite-y
  (implies
   (and
    (affine-opposite-y-infinity-relation-p a b ab)
    (affine-opposite-y-infinity-relation-p b c bc)
    (curve-point-addition-relation-p
     ab (curve-point-affine-coordinates c) left)
    (curve-point-addition-relation-p
     (curve-point-affine-coordinates a) bc right))
   (equal (curve-point-fix left)
          (curve-point-fix right)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (opposite-y-relation-chain-implies-fixed-endpoints-equal-local
     opposite-y-relation-implies-left-infinity-outer-local
     opposite-y-relation-implies-right-infinity-outer-local)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(curve-point-fix-of-affine-coordinates)))))

(local
 (defthm addition-relation-has-left-infinity-identity-witness-local
   (implies
    (and (curve-point-addition-relation-p first second output)
         (equal (curve-point-fix first) (curve-point-infinity)))
    (curve-point-addition-relation-p first second second))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (enable curve-point-addition-relation-p
                    curve-point-left-infinity-identity-relation-p)))))

(local
 (defthm addition-relation-left-infinity-output-local
   (implies
    (and (curve-point-addition-relation-p first second output)
         (equal (curve-point-fix first) (curve-point-infinity)))
    (equal (curve-point-fix output) (curve-point-fix second)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     (addition-relation-has-left-infinity-identity-witness-local
      (:instance curve-point-addition-relation-output-determinate
                 (output-a output) (output-b second)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm addition-relation-has-right-infinity-identity-witness-local
   (implies
    (and (curve-point-addition-relation-p first second output)
         (equal (curve-point-fix second) (curve-point-infinity)))
    (curve-point-addition-relation-p first second first))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (enable curve-point-addition-relation-p
                    curve-point-right-infinity-identity-relation-p)))))

(local
 (defthm addition-relation-right-infinity-output-local
   (implies
    (and (curve-point-addition-relation-p first second output)
         (equal (curve-point-fix second) (curve-point-infinity)))
    (equal (curve-point-fix output) (curve-point-fix first)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     (addition-relation-has-right-infinity-identity-witness-local
      (:instance curve-point-addition-relation-output-determinate
                 (output-a output) (output-b first)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm relation-output-determinate-under-fixed-operands-local
   (implies
    (and (curve-point-addition-relation-p first-a second-a output-a)
         (curve-point-addition-relation-p first-b second-b output-b)
         (equal (curve-point-fix first-a) (curve-point-fix first-b))
         (equal (curve-point-fix second-a) (curve-point-fix second-b)))
    (equal (curve-point-fix output-a) (curve-point-fix output-b)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance curve-point-addition-relation-output-determinate
                 (first (curve-point-fix first-a))
                 (second (curve-point-fix second-a))
                 (output-a (curve-point-fix output-a))
                 (output-b (curve-point-fix output-b)))
      (:instance curve-point-addition-relation-p-of-fixes
                 (first first-a) (second second-a) (output output-a))
      (:instance curve-point-addition-relation-p-of-fixes
                 (first first-b) (second second-b) (output output-b)))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(curve-point-fix-idempotent))))))

(defthm curve-point-addition-relation-associative-when-both-inner-doubling
  (implies
   (and
    (curve-point-addition-relation-p a b ab)
    (curve-point-addition-relation-p b c bc)
    (curve-point-addition-relation-p ab c left)
    (curve-point-addition-relation-p a bc right)
    (equal (curve-point-fix a) (curve-point-fix b))
    (equal (curve-point-fix b) (curve-point-fix c)))
   (equal (curve-point-fix left)
          (curve-point-fix right)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance relation-output-determinate-under-fixed-operands-local
                (first-a a) (second-a b) (output-a ab)
                (first-b b) (second-b c) (output-b bc))
     (:instance curve-point-addition-relation-p-commutative
                (first ab) (second c) (output left))
     (:instance relation-output-determinate-under-fixed-operands-local
                (first-a c) (second-a ab) (output-a left)
                (first-b a) (second-b bc) (output-b right)))
    :in-theory (theory 'minimal-theory))))

(local
 (defthm relation-associative-when-first-infinity-local
   (implies
    (and (curve-point-addition-relation-p a b ab)
         (curve-point-addition-relation-p b c bc)
         (curve-point-addition-relation-p ab c left)
         (curve-point-addition-relation-p a bc right)
         (equal (curve-point-fix a) (curve-point-infinity)))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance addition-relation-left-infinity-output-local
                 (first a) (second b) (output ab))
      (:instance addition-relation-left-infinity-output-local
                 (first a) (second bc) (output right))
      (:instance relation-output-determinate-under-fixed-operands-local
                 (first-a ab) (second-a c) (output-a left)
                 (first-b b) (second-b c) (output-b bc)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm relation-associative-when-second-infinity-local
   (implies
    (and (curve-point-addition-relation-p a b ab)
         (curve-point-addition-relation-p b c bc)
         (curve-point-addition-relation-p ab c left)
         (curve-point-addition-relation-p a bc right)
         (equal (curve-point-fix b) (curve-point-infinity)))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance addition-relation-right-infinity-output-local
                 (first a) (second b) (output ab))
      (:instance addition-relation-left-infinity-output-local
                 (first b) (second c) (output bc))
      (:instance relation-output-determinate-under-fixed-operands-local
                 (first-a ab) (second-a c) (output-a left)
                 (first-b a) (second-b bc) (output-b right)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm relation-associative-when-third-infinity-local
   (implies
    (and (curve-point-addition-relation-p a b ab)
         (curve-point-addition-relation-p b c bc)
         (curve-point-addition-relation-p ab c left)
         (curve-point-addition-relation-p a bc right)
         (equal (curve-point-fix c) (curve-point-infinity)))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance addition-relation-right-infinity-output-local
                 (first b) (second c) (output bc))
      (:instance addition-relation-right-infinity-output-local
                 (first ab) (second c) (output left))
      (:instance relation-output-determinate-under-fixed-operands-local
                 (first-a a) (second-a bc) (output-a right)
                 (first-b a) (second-b b) (output-b ab)))
     :in-theory (theory 'minimal-theory)))))

(defthm curve-point-addition-relation-associative-when-original-infinity
  (implies
   (and
    (curve-point-addition-relation-p a b ab)
    (curve-point-addition-relation-p b c bc)
    (curve-point-addition-relation-p ab c left)
    (curve-point-addition-relation-p a bc right)
    (or (equal (curve-point-fix a) (curve-point-infinity))
        (equal (curve-point-fix b) (curve-point-infinity))
        (equal (curve-point-fix c) (curve-point-infinity))))
   (equal (curve-point-fix left)
          (curve-point-fix right)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (relation-associative-when-first-infinity-local
     relation-associative-when-second-infinity-local
     relation-associative-when-third-infinity-local)
    :in-theory (theory 'minimal-theory))))
