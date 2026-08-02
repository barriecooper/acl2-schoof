(in-package "GFIELD")

(include-book "curve-point-addition-relation-affine-interface")
(include-book "curve-point-addition-relation-associativity-structural")
(include-book "affine-dd-secant-associativity")
(include-book "affine-dd-t-translation")
(include-book "affine-dd-opposite-y-propagation")
(include-book "affine-dt-d-translation")
(include-book "affine-dt-left-output-opposite-y-propagation")
(include-book "affine-td-d-translation")
(include-book "affine-td-opposite-y-propagation")
(include-book "affine-inverse-secant-translation")
(include-book "affine-inverse-tangent-translation")
(include-book "curve-point-addition-commutativity")

; These packaging lemmas are the only places in this assembly book where the
; full relation is opened.  Matrix cells use them as bounded semantic bridges.
(local
 (defthm secant-relation-has-selected-slope-local
   (implies
    (affine-distinct-x-secant-relation-p a b slope output)
    (affine-distinct-x-secant-relation-p
     a b (affine-distinct-x-slope a b) output))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-distinct-x-output-satisfies-secant-relation
                 (first a) (second b))
      (:instance affine-distinct-x-secant-relation-slope-unique
                 (first a) (second b)
                 (slope-a slope) (output-a output)
                 (slope-b (affine-distinct-x-slope a b))
                 (output-b (affine-distinct-x-output a b))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(affine-distinct-x-secant-relation-p
        field-fix-of-affine-distinct-x-slope
        field-mul-fixed-congruence))))))

(local
 (defthm secant-relation-packages-as-full-addition-local
   (implies
    (affine-distinct-x-secant-relation-p a b slope output)
    (curve-point-addition-relation-p
     (curve-point-affine-coordinates a)
     (curve-point-affine-coordinates b)
     (curve-point-affine-coordinates output)))
   :rule-classes nil
   :hints
   (("Goal"
     :use (secant-relation-has-selected-slope-local
           (:instance short-weierstrass-curve-point-p-of-affine
                      (coordinates (affine-coordinates-fix a)))
           (:instance short-weierstrass-curve-point-p-of-affine
                      (coordinates (affine-coordinates-fix b)))
           (:instance short-weierstrass-affine-point-p-of-fix (coordinates a))
           (:instance short-weierstrass-affine-point-p-of-fix (coordinates b))
           (:instance short-weierstrass-affine-point-p-of-fix (coordinates output)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(curve-point-addition-relation-p
        affine-distinct-x-secant-relation-p
        affine-distinct-x-slope
        curve-point-fix-of-affine-coordinates
        curve-point-affine-coordinates-get-of-constructor
        affine-coordinates-fix-idempotent
        affine-coordinates-x-of-fix
        affine-coordinates-y-of-fix))))))

(local
 (defthm doubling-relation-has-selected-slope-local
   (implies
    (affine-doubling-relation-p a slope output)
    (affine-doubling-relation-p
     a (affine-same-point-non-opposite-slope a) output))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-same-point-non-opposite-output-satisfies-doubling-relation
                 (input a))
      (:instance affine-doubling-relation-slope-unique
                 (input a) (slope-a slope) (output-a output)
                 (slope-b (affine-same-point-non-opposite-slope a))
                 (output-b (affine-same-point-non-opposite-output a))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(affine-doubling-relation-p
        field-fix-of-affine-same-point-non-opposite-slope
        field-mul-fixed-congruence))))))

(local
 (defthm doubling-relation-packages-as-full-addition-local
   (implies
    (affine-doubling-relation-p a slope output)
    (curve-point-addition-relation-p
     (curve-point-affine-coordinates a)
     (curve-point-affine-coordinates a)
     (curve-point-affine-coordinates output)))
   :rule-classes nil
   :hints
   (("Goal"
     :use (doubling-relation-has-selected-slope-local
           (:instance short-weierstrass-curve-point-p-of-affine
                      (coordinates (affine-coordinates-fix a)))
           (:instance short-weierstrass-affine-point-p-of-fix (coordinates a))
           (:instance short-weierstrass-affine-point-p-of-fix (coordinates output)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(curve-point-addition-relation-p
        affine-doubling-relation-p
        affine-same-point-non-opposite-slope
        curve-point-fix-of-affine-coordinates
        curve-point-affine-coordinates-get-of-constructor
        affine-coordinates-fix-idempotent
        affine-coordinates-x-of-fix
        affine-coordinates-y-of-fix))))))

(local
 (defthm opposite-y-relation-packages-as-full-addition-local
   (implies
    (affine-opposite-y-infinity-relation-p a b output)
    (curve-point-addition-relation-p
     (curve-point-affine-coordinates a)
     (curve-point-affine-coordinates b)
     output))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance short-weierstrass-curve-point-p-of-affine
                      (coordinates (affine-coordinates-fix a)))
           (:instance short-weierstrass-curve-point-p-of-affine
                      (coordinates (affine-coordinates-fix b)))
           (:instance short-weierstrass-affine-point-p-of-fix (coordinates a))
           (:instance short-weierstrass-affine-point-p-of-fix (coordinates b)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(curve-point-addition-relation-p
        affine-opposite-y-infinity-relation-p
        curve-point-fix-of-affine-coordinates
        curve-point-affine-coordinates-get-of-constructor
        affine-coordinates-fix-idempotent
        affine-coordinates-x-of-fix
        affine-coordinates-y-of-fix
        curve-point-fix-of-infinity))))))
