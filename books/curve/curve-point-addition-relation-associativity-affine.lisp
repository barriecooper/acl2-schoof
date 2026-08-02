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

; O/O matrix cell.  The extracted opposite-y relations already have exactly
; the structural theorem's witness orientation; no packaging or case split is
; involved.
(local
 (defthm curve-point-addition-relation-associative-affine-o-o-cell-local
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
     ((:instance
       curve-point-addition-relation-associative-when-both-inner-opposite-y))
     :in-theory (theory 'minimal-theory)))))

; T/T matrix cell.  The extraction interface records the repeated fixed inputs;
; tangent witnesses and tangent equations play no role in this structural cell.
(local
 (defthm curve-point-addition-relation-associative-affine-t-t-cell-local
   (implies
    (and
     (affine-doubling-relation-p a ab-tangent-slope ab-payload)
     (equal (affine-coordinates-fix a) (affine-coordinates-fix b))
     (equal (curve-point-fix ab)
            (curve-point-affine-coordinates
             (affine-coordinates-fix ab-payload)))
     (affine-doubling-relation-p b bc-tangent-slope bc-payload)
     (equal (affine-coordinates-fix b) (affine-coordinates-fix c))
     (equal (curve-point-fix bc)
            (curve-point-affine-coordinates
             (affine-coordinates-fix bc-payload)))
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates a)
      (curve-point-affine-coordinates b) ab)
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates b)
      (curve-point-affine-coordinates c) bc)
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
     ((:instance
       curve-point-addition-relation-associative-when-both-inner-doubling
       (a (curve-point-affine-coordinates a))
       (b (curve-point-affine-coordinates b))
       (c (curve-point-affine-coordinates c))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(curve-point-fix-of-affine-coordinates))))))

; Relation congruence used after inner determinacy has aligned an extracted
; tagged payload with the supplied inner witness.  This changes operands only;
; output comparison remains the responsibility of fixed-operands determinacy.
(local
 (defthm addition-relation-transport-fixed-operands-local
   (implies
    (and
     (curve-point-addition-relation-p first-a second-a output)
     (equal (curve-point-fix first-a) (curve-point-fix first-b))
     (equal (curve-point-fix second-a) (curve-point-fix second-b)))
    (curve-point-addition-relation-p first-b second-b output))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance curve-point-addition-relation-p-of-fixes
                 (first first-a) (second second-a) (output output))
      (:instance curve-point-addition-relation-p-of-fixes
                 (first first-b) (second second-b) (output output)))
     :in-theory (theory 'minimal-theory)))))
