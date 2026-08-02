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
(include-book "affine-mixed-outer-doubling-impossibility")
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

; D/D, outer D/D.  The only cross-tree step is the certified arbitrary-witness
; secant associativity boundary; the tagged equalities merely lift its affine
; fixer equality to the two supplied full-point witnesses.
(local
 (defthm affine-d-d-outer-d-d-cell-local
   (implies
    (and
     (affine-distinct-x-secant-relation-p a b ab-slope ab-payload)
     (affine-distinct-x-secant-relation-p b c bc-slope bc-payload)
     (affine-distinct-x-secant-relation-p
      ab-payload c left-slope left-payload)
     (affine-distinct-x-secant-relation-p
      a bc-payload right-slope right-payload)
     (equal (curve-point-fix left)
            (curve-point-affine-coordinates
             (affine-coordinates-fix left-payload)))
     (equal (curve-point-fix right)
            (curve-point-affine-coordinates
             (affine-coordinates-fix right-payload))))
    (equal (curve-point-fix left)
           (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-dd-secant-relation-associative-when-all-distinct-x
                 (p-slope ab-slope) (r-slope bc-slope)
                 (ab ab-payload) (bc bc-payload)
                 (q-slope left-slope) (left left-payload)
                 (tt-slope right-slope) (right right-payload)))
     :in-theory (theory 'minimal-theory)))))

; Affine relation congruence for the fixed payload equalities returned by
; bounded extraction.  The slope and output witnesses are not changed.
(local
 (defthm secant-relation-transport-fixed-operands-local
   (implies
    (and
     (affine-distinct-x-secant-relation-p
      first-a second-a slope output)
     (equal (affine-coordinates-fix first-a)
            (affine-coordinates-fix first-b))
     (equal (affine-coordinates-fix second-a)
            (affine-coordinates-fix second-b)))
    (affine-distinct-x-secant-relation-p
     first-b second-b slope output))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-distinct-x-secant-relation-p-of-fixes
                 (first first-a) (second second-a)
                 (slope slope) (output output))
      (:instance affine-distinct-x-secant-relation-p-of-fixes
                 (first first-b) (second second-b)
                 (slope slope) (output output)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(affine-coordinates-fix-idempotent field-fix-idempotent))))))

; D/D, outer T/D.  Fixed operand pair for determinacy:
;   (tagged a, tagged bc-payload).
; Family-derived output: tagged left-payload, packaged from DD-T translation.
; Supplied output: right, from the transported right outer relation.
(local
 (defthm affine-d-d-outer-t-d-cell-local
   (implies
    (and
     (affine-distinct-x-secant-relation-p a b ab-slope ab-payload)
     (affine-distinct-x-secant-relation-p b c bc-slope bc-payload)
     (affine-doubling-relation-p
      ab-payload left-tangent-slope left-payload)
     (equal (affine-coordinates-fix ab-payload)
            (affine-coordinates-fix c))
     (equal (curve-point-fix left)
            (curve-point-affine-coordinates
             (affine-coordinates-fix left-payload)))
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates a)
      (curve-point-affine-coordinates bc-payload)
      right))
    (equal (curve-point-fix left)
           (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-dd-t-translation
                 (p-slope ab-slope) (r-slope bc-slope)
                 (c ab-payload) (q bc-payload)
                 (t-slope left-tangent-slope) (d left-payload))
      (:instance secant-relation-transport-fixed-operands-local
                 (first-a b) (second-a c)
                 (first-b b) (second-b ab-payload)
                 (slope bc-slope) (output bc-payload))
      (:instance secant-relation-packages-as-full-addition-local
                 (a a) (b bc-payload)
                 (slope (field-sub
                         (field-add (field-fix ab-slope)
                                    (field-fix left-tangent-slope))
                         (field-fix bc-slope)))
                 (output left-payload))
      (:instance doubling-relation-packages-as-full-addition-local
                 (a a)
                 (slope (field-sub
                         (field-add (field-fix ab-slope)
                                    (field-fix left-tangent-slope))
                         (field-fix bc-slope)))
                 (output left-payload))
      (:instance
       curve-point-addition-relation-output-determinate-under-fixed-operands
       (first-a (curve-point-affine-coordinates a))
       (second-a (curve-point-affine-coordinates bc-payload))
       (output-a (curve-point-affine-coordinates left-payload))
       (first-b (curve-point-affine-coordinates a))
       (second-b (curve-point-affine-coordinates bc-payload))
       (output-b right))
      (:instance
       curve-point-addition-relation-output-determinate-under-fixed-operands
       (first-a (curve-point-affine-coordinates a))
       (second-a (curve-point-affine-coordinates a))
       (output-a (curve-point-affine-coordinates left-payload))
       (first-b (curve-point-affine-coordinates a))
       (second-b (curve-point-affine-coordinates bc-payload))
       (output-b right)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(curve-point-fix-of-affine-coordinates
        affine-coordinates-fix-idempotent
        field-fix-idempotent))))))

; Doubling relation congruence for a fixed-equal extracted tangent input.
(local
 (defthm doubling-relation-transport-fixed-input-local
   (implies
    (and
     (affine-doubling-relation-p input-a slope output)
     (equal (affine-coordinates-fix input-a)
            (affine-coordinates-fix input-b)))
    (affine-doubling-relation-p input-b slope output))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-doubling-relation-p-of-fixes
                 (input input-a) (slope slope) (output output))
      (:instance affine-doubling-relation-p-of-fixes
                 (input input-b) (slope slope) (output output)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(affine-coordinates-fix-idempotent field-fix-idempotent))))))

; D/D, outer D/T, obtained by applying DD-T to the reversed triple C,B,A.
; Fixed operand pair for determinacy is (tagged ab-payload, tagged c).
; The family-derived tagged right-payload is reversed semantically before it
; is compared with the supplied left witness.
(local
 (defthm affine-d-d-outer-d-t-cell-local
   (implies
    (and
     (affine-distinct-x-secant-relation-p a b ab-slope ab-payload)
     (affine-distinct-x-secant-relation-p b c bc-slope bc-payload)
     (affine-doubling-relation-p
      a right-tangent-slope right-payload)
     (equal (affine-coordinates-fix bc-payload)
            (affine-coordinates-fix a))
     (equal (curve-point-fix right)
            (curve-point-affine-coordinates
             (affine-coordinates-fix right-payload)))
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates ab-payload)
      (curve-point-affine-coordinates c)
      left))
    (equal (curve-point-fix left)
           (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-distinct-x-secant-relation-p-reverse
                 (first b) (second c) (slope bc-slope)
                 (output bc-payload))
      (:instance affine-distinct-x-secant-relation-p-reverse
                 (first a) (second b) (slope ab-slope)
                 (output ab-payload))
      (:instance secant-relation-transport-fixed-operands-local
                 (first-a b) (second-a a)
                 (first-b b) (second-b bc-payload)
                 (slope ab-slope) (output ab-payload))
      (:instance doubling-relation-transport-fixed-input-local
                 (input-a a) (input-b bc-payload)
                 (slope right-tangent-slope) (output right-payload))
      (:instance affine-dd-t-translation
                 (a c) (b b) (c bc-payload) (q ab-payload)
                 (p-slope bc-slope) (r-slope ab-slope)
                 (t-slope right-tangent-slope) (d right-payload))
      (:instance secant-relation-packages-as-full-addition-local
                 (a c) (b ab-payload)
                 (slope (field-sub
                         (field-add (field-fix bc-slope)
                                    (field-fix right-tangent-slope))
                         (field-fix ab-slope)))
                 (output right-payload))
      (:instance doubling-relation-packages-as-full-addition-local
                 (a c)
                 (slope (field-sub
                         (field-add (field-fix bc-slope)
                                    (field-fix right-tangent-slope))
                         (field-fix ab-slope)))
                 (output right-payload))
      (:instance curve-point-addition-relation-p-commutative
                 (first (curve-point-affine-coordinates c))
                 (second (curve-point-affine-coordinates ab-payload))
                 (output (curve-point-affine-coordinates right-payload)))
      (:instance
       curve-point-addition-relation-output-determinate-under-fixed-operands
       (first-a (curve-point-affine-coordinates ab-payload))
       (second-a (curve-point-affine-coordinates c))
       (output-a (curve-point-affine-coordinates right-payload))
       (first-b (curve-point-affine-coordinates ab-payload))
       (second-b (curve-point-affine-coordinates c))
       (output-b left))
      (:instance
       curve-point-addition-relation-output-determinate-under-fixed-operands
       (first-a (curve-point-affine-coordinates c))
       (second-a (curve-point-affine-coordinates c))
       (output-a (curve-point-affine-coordinates right-payload))
       (first-b (curve-point-affine-coordinates ab-payload))
       (second-b (curve-point-affine-coordinates c))
       (output-b left)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(curve-point-fix-of-affine-coordinates
        affine-coordinates-fix-idempotent
        field-fix-idempotent))))))

; D/D, left outer O.  Determinacy pair: (tagged a, tagged bc-payload).
; Derived output left is packaged by opposite-y propagation; right is supplied.
(local
 (defthm affine-d-d-outer-o-any-cell-local
   (implies
    (and
     (affine-distinct-x-secant-relation-p a b ab-slope ab-payload)
     (affine-distinct-x-secant-relation-p b c bc-slope bc-payload)
     (affine-opposite-y-infinity-relation-p ab-payload c left)
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates a)
      (curve-point-affine-coordinates bc-payload) right))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-dd-opposite-y-propagates-to-other-tree
                 (p-slope ab-slope) (p ab-payload)
                 (r-slope bc-slope) (q bc-payload)
                 (infinity left))
      (:instance opposite-y-relation-packages-as-full-addition-local
                 (a a) (b bc-payload) (output left))
      (:instance
       curve-point-addition-relation-output-determinate-under-fixed-operands
       (first-a (curve-point-affine-coordinates a))
       (second-a (curve-point-affine-coordinates bc-payload))
       (output-a left)
       (first-b (curve-point-affine-coordinates a))
       (second-b (curve-point-affine-coordinates bc-payload))
       (output-b right)))
     :in-theory (theory 'minimal-theory)))))

; D/D, right outer O.  Determinacy pair: (tagged ab-payload, tagged c).
; Derived output right is packaged by mirrored propagation; left is supplied.
(local
 (defthm affine-d-d-outer-any-o-cell-local
   (implies
    (and
     (affine-distinct-x-secant-relation-p a b ab-slope ab-payload)
     (affine-distinct-x-secant-relation-p b c bc-slope bc-payload)
     (affine-opposite-y-infinity-relation-p a bc-payload right)
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates ab-payload)
      (curve-point-affine-coordinates c) left))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-dd-opposite-y-propagates-to-left-tree
                 (p-slope ab-slope) (p ab-payload)
                 (r-slope bc-slope) (q bc-payload)
                 (infinity right))
      (:instance opposite-y-relation-packages-as-full-addition-local
                 (a ab-payload) (b c) (output right))
      (:instance
       curve-point-addition-relation-output-determinate-under-fixed-operands
       (first-a (curve-point-affine-coordinates ab-payload))
       (second-a (curve-point-affine-coordinates c))
       (output-a right)
       (first-b (curve-point-affine-coordinates ab-payload))
       (second-b (curve-point-affine-coordinates c))
       (output-b left)))
     :in-theory (theory 'minimal-theory)))))

; Domain projection needed to instantiate bounded outer extraction on the two
; secant payloads.  No relation equation is used by any matrix-cell proof.
(local
 (defthm secant-relation-implies-output-affine-local
   (implies
    (affine-distinct-x-secant-relation-p first second slope output)
    (short-weierstrass-affine-point-p output))
   :hints
   (("Goal" :in-theory
     (enable affine-distinct-x-secant-relation-p)))))

; Complete inner D/D cell.  The supplied outer witnesses are first transported
; to the extracted tagged payloads.  Each transported relation is then opened
; only through affine-case-coverage; the remainder is propositional selection
; among the certified bounded subcells above.
(local
 (defthm curve-point-addition-relation-associative-affine-d-d-cell-local
   (implies
    (and
     (short-weierstrass-affine-point-p a)
     (short-weierstrass-affine-point-p b)
     (short-weierstrass-affine-point-p c)
     (affine-distinct-x-secant-relation-p
      a b ab-secant-slope ab-payload)
     (equal (curve-point-fix ab)
            (curve-point-affine-coordinates
             (affine-coordinates-fix ab-payload)))
     (affine-distinct-x-secant-relation-p
      b c bc-secant-slope bc-payload)
     (equal (curve-point-fix bc)
            (curve-point-affine-coordinates
             (affine-coordinates-fix bc-payload)))
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
     ((:instance secant-relation-implies-output-affine-local
                 (first a) (second b) (slope ab-secant-slope)
                 (output ab-payload))
      (:instance secant-relation-implies-output-affine-local
                 (first b) (second c) (slope bc-secant-slope)
                 (output bc-payload))
      (:instance addition-relation-transport-fixed-operands-local
                 (first-a ab)
                 (second-a (curve-point-affine-coordinates c))
                 (output left)
                 (first-b (curve-point-affine-coordinates ab-payload))
                 (second-b (curve-point-affine-coordinates c)))
      (:instance addition-relation-transport-fixed-operands-local
                 (first-a (curve-point-affine-coordinates a))
                 (second-a bc) (output right)
                 (first-b (curve-point-affine-coordinates a))
                 (second-b (curve-point-affine-coordinates bc-payload)))
      (:instance curve-point-addition-relation-affine-case-coverage
                 (a ab-payload) (b c) (output left))
      (:instance curve-point-addition-relation-affine-case-coverage
                 (a a) (b bc-payload) (output right))
      (:instance secant-relation-transport-fixed-operands-local
                 (first-a (affine-coordinates-fix ab-payload))
                 (second-a (affine-coordinates-fix c))
                 (first-b ab-payload) (second-b c)
                 (slope
                  (field-div
                   (field-sub
                    (affine-coordinates-y (affine-coordinates-fix c))
                    (affine-coordinates-y (affine-coordinates-fix ab-payload)))
                   (field-sub
                    (affine-coordinates-x (affine-coordinates-fix c))
                    (affine-coordinates-x (affine-coordinates-fix ab-payload)))))
                 (output (curve-point-affine-coordinates-get
                          (curve-point-fix left))))
      (:instance secant-relation-transport-fixed-operands-local
                 (first-a (affine-coordinates-fix a))
                 (second-a (affine-coordinates-fix bc-payload))
                 (first-b a) (second-b bc-payload)
                 (slope
                  (field-div
                   (field-sub
                    (affine-coordinates-y (affine-coordinates-fix bc-payload))
                    (affine-coordinates-y (affine-coordinates-fix a)))
                   (field-sub
                    (affine-coordinates-x (affine-coordinates-fix bc-payload))
                    (affine-coordinates-x (affine-coordinates-fix a)))))
                 (output (curve-point-affine-coordinates-get
                          (curve-point-fix right))))
      (:instance affine-d-d-outer-d-d-cell-local
                 (ab-slope ab-secant-slope)
                 (bc-slope bc-secant-slope)
                 (left-slope
                  (field-div
                   (field-sub
                    (affine-coordinates-y (affine-coordinates-fix c))
                    (affine-coordinates-y
                     (affine-coordinates-fix ab-payload)))
                   (field-sub
                    (affine-coordinates-x (affine-coordinates-fix c))
                    (affine-coordinates-x
                     (affine-coordinates-fix ab-payload)))))
                 (left-payload
                  (curve-point-affine-coordinates-get
                   (curve-point-fix left)))
                 (right-slope
                  (field-div
                   (field-sub
                    (affine-coordinates-y
                     (affine-coordinates-fix bc-payload))
                    (affine-coordinates-y (affine-coordinates-fix a)))
                   (field-sub
                    (affine-coordinates-x
                     (affine-coordinates-fix bc-payload))
                    (affine-coordinates-x (affine-coordinates-fix a)))))
                 (right-payload
                  (curve-point-affine-coordinates-get
                   (curve-point-fix right))))
      (:instance doubling-relation-transport-fixed-input-local
                 (input-a (affine-coordinates-fix ab-payload))
                 (input-b ab-payload)
                 (slope
                  (field-div
                   (field-add
                    (field-mul
                     (field-add (field-add (field-one) (field-one)) (field-one))
                     (field-mul
                      (affine-coordinates-x (affine-coordinates-fix ab-payload))
                      (affine-coordinates-x (affine-coordinates-fix ab-payload))))
                    (field-fix (short-weierstrass-a)))
                   (field-add
                    (affine-coordinates-y (affine-coordinates-fix ab-payload))
                    (affine-coordinates-y (affine-coordinates-fix ab-payload)))))
                 (output (curve-point-affine-coordinates-get
                          (curve-point-fix left))))
      (:instance doubling-relation-transport-fixed-input-local
                 (input-a (affine-coordinates-fix a))
                 (input-b a)
                 (slope
                  (field-div
                   (field-add
                    (field-mul
                     (field-add (field-add (field-one) (field-one)) (field-one))
                     (field-mul
                      (affine-coordinates-x (affine-coordinates-fix a))
                      (affine-coordinates-x (affine-coordinates-fix a))))
                    (field-fix (short-weierstrass-a)))
                   (field-add
                    (affine-coordinates-y (affine-coordinates-fix a))
                    (affine-coordinates-y (affine-coordinates-fix a)))))
                 (output (curve-point-affine-coordinates-get
                          (curve-point-fix right))))
      (:instance affine-d-d-outer-t-d-cell-local
                 (ab-slope ab-secant-slope)
                 (bc-slope bc-secant-slope)
                 (left-tangent-slope
                  (field-div
                   (field-add
                    (field-mul
                     (field-add (field-add (field-one) (field-one))
                                (field-one))
                     (field-mul
                      (affine-coordinates-x
                       (affine-coordinates-fix ab-payload))
                      (affine-coordinates-x
                       (affine-coordinates-fix ab-payload))))
                    (field-fix (short-weierstrass-a)))
                   (field-add
                    (affine-coordinates-y
                     (affine-coordinates-fix ab-payload))
                    (affine-coordinates-y
                     (affine-coordinates-fix ab-payload)))))
                 (left-payload
                  (curve-point-affine-coordinates-get
                   (curve-point-fix left))))
      (:instance affine-d-d-outer-d-t-cell-local
                 (ab-slope ab-secant-slope)
                 (bc-slope bc-secant-slope)
                 (right-tangent-slope
                  (field-div
                   (field-add
                    (field-mul
                     (field-add (field-add (field-one) (field-one))
                                (field-one))
                     (field-mul
                      (affine-coordinates-x (affine-coordinates-fix a))
                      (affine-coordinates-x (affine-coordinates-fix a))))
                    (field-fix (short-weierstrass-a)))
                   (field-add
                    (affine-coordinates-y (affine-coordinates-fix a))
                    (affine-coordinates-y (affine-coordinates-fix a)))))
                 (right-payload
                  (curve-point-affine-coordinates-get
                   (curve-point-fix right))))
      (:instance affine-d-d-outer-o-any-cell-local
                 (ab-slope ab-secant-slope)
                 (bc-slope bc-secant-slope))
      (:instance affine-d-d-outer-any-o-cell-local
                 (ab-slope ab-secant-slope)
                 (bc-slope bc-secant-slope)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(curve-point-fix-of-affine-coordinates
        affine-coordinates-fix-idempotent
        field-fix-idempotent
        affine-distinct-x-secant-relation-p-of-fixes
        affine-doubling-relation-p-of-fixes
        affine-opposite-y-infinity-relation-p-of-fixes))))))

; Inner D/T, left outer D.  Determinacy compares the family-derived tagged
; left-payload with supplied RIGHT on fixed pair (tagged A, tagged Q).
(local
 (defthm affine-d-t-outer-d-cell-local
   (implies
    (and
     (affine-distinct-x-secant-relation-p a b p-slope p-output)
     (affine-doubling-relation-p b t-slope q-output)
     (affine-distinct-x-secant-relation-p
      p-output b left-slope left-payload)
     (equal (curve-point-fix left)
            (curve-point-affine-coordinates
             (affine-coordinates-fix left-payload)))
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates a)
      (curve-point-affine-coordinates q-output) right))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-dt-d-translation
                 (q-slope left-slope) (r-output left-payload))
      (:instance secant-relation-packages-as-full-addition-local
                 (a a) (b q-output)
                 (slope
                  (field-sub
                   (field-add (field-fix p-slope)
                              (field-fix left-slope))
                   (field-fix t-slope)))
                 (output left-payload))
      (:instance doubling-relation-packages-as-full-addition-local
                 (a a)
                 (slope
                  (field-sub
                   (field-add (field-fix p-slope)
                              (field-fix left-slope))
                   (field-fix t-slope)))
                 (output left-payload))
      (:instance
       curve-point-addition-relation-output-determinate-under-fixed-operands
       (first-a (curve-point-affine-coordinates a))
       (second-a (curve-point-affine-coordinates q-output))
       (output-a (curve-point-affine-coordinates left-payload))
       (first-b (curve-point-affine-coordinates a))
       (second-b (curve-point-affine-coordinates q-output))
       (output-b right))
      (:instance
       curve-point-addition-relation-output-determinate-under-fixed-operands
       (first-a (curve-point-affine-coordinates a))
       (second-a (curve-point-affine-coordinates a))
       (output-a (curve-point-affine-coordinates left-payload))
       (first-b (curve-point-affine-coordinates a))
       (second-b (curve-point-affine-coordinates q-output))
       (output-b right)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(curve-point-fix-of-affine-coordinates
        affine-coordinates-fix-idempotent))))))

; Inner D/T, left outer O.  Propagation packages LEFT as the derived output on
; fixed pair (tagged A, tagged Q); supplied output on that pair is RIGHT.
(local
 (defthm affine-d-t-outer-o-cell-local
   (implies
    (and
     (affine-distinct-x-secant-relation-p a b p-slope p-output)
     (affine-doubling-relation-p b t-slope q-output)
     (affine-opposite-y-infinity-relation-p p-output b left)
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates a)
      (curve-point-affine-coordinates q-output) right))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance
       affine-dt-left-output-opposite-y-propagates-to-right-output
       (infinity left))
      (:instance opposite-y-relation-packages-as-full-addition-local
                 (a a) (b q-output) (output left))
      (:instance
       curve-point-addition-relation-output-determinate-under-fixed-operands
       (first-a (curve-point-affine-coordinates a))
       (second-a (curve-point-affine-coordinates q-output))
       (output-a left)
       (first-b (curve-point-affine-coordinates a))
       (second-b (curve-point-affine-coordinates q-output))
       (output-b right)))
     :in-theory (theory 'minimal-theory)))))

; Inner T/D, right outer D.  Determinacy compares the family-derived tagged
; right-payload with supplied LEFT on fixed pair (tagged P, tagged B).
(local
 (defthm affine-t-d-outer-d-cell-local
   (implies
    (and
     (affine-doubling-relation-p a t-slope p-output)
     (affine-distinct-x-secant-relation-p a b p-slope q-output)
     (affine-distinct-x-secant-relation-p
      a q-output right-slope right-payload)
     (equal (curve-point-fix right)
            (curve-point-affine-coordinates
             (affine-coordinates-fix right-payload)))
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates p-output)
      (curve-point-affine-coordinates b) left))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-td-d-translation
                 (q-slope right-slope) (r-output right-payload))
      (:instance secant-relation-packages-as-full-addition-local
                 (a p-output) (b b)
                 (slope
                  (field-sub
                   (field-add (field-fix p-slope)
                              (field-fix right-slope))
                   (field-fix t-slope)))
                 (output right-payload))
      (:instance doubling-relation-packages-as-full-addition-local
                 (a b)
                 (slope
                  (field-sub
                   (field-add (field-fix p-slope)
                              (field-fix right-slope))
                   (field-fix t-slope)))
                 (output right-payload))
      (:instance
       curve-point-addition-relation-output-determinate-under-fixed-operands
       (first-a (curve-point-affine-coordinates p-output))
       (second-a (curve-point-affine-coordinates b))
       (output-a (curve-point-affine-coordinates right-payload))
       (first-b (curve-point-affine-coordinates p-output))
       (second-b (curve-point-affine-coordinates b))
       (output-b left))
      (:instance
       curve-point-addition-relation-output-determinate-under-fixed-operands
       (first-a (curve-point-affine-coordinates b))
       (second-a (curve-point-affine-coordinates b))
       (output-a (curve-point-affine-coordinates right-payload))
       (first-b (curve-point-affine-coordinates p-output))
       (second-b (curve-point-affine-coordinates b))
       (output-b left)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(curve-point-fix-of-affine-coordinates
        affine-coordinates-fix-idempotent))))))

; Inner T/D, left outer O.  The checked-in propagation theorem derives RIGHT
; as an opposite-y output.  Determinacy pair is (tagged A, tagged Q).
(local
 (defthm affine-t-d-outer-o-cell-local
   (implies
    (and
     (affine-doubling-relation-p a t-slope p-output)
     (affine-distinct-x-secant-relation-p a b p-slope q-output)
     (affine-opposite-y-infinity-relation-p p-output b left)
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates a)
      (curve-point-affine-coordinates q-output) right))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance
       affine-td-left-output-opposite-y-propagates-to-right-output
       (infinity left))
      (:instance opposite-y-relation-packages-as-full-addition-local
                 (a a) (b q-output) (output left))
      (:instance
       curve-point-addition-relation-output-determinate-under-fixed-operands
       (first-a (curve-point-affine-coordinates a))
       (second-a (curve-point-affine-coordinates q-output))
       (output-a left)
       (first-b (curve-point-affine-coordinates a))
       (second-b (curve-point-affine-coordinates q-output))
       (output-b right)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm doubling-relation-implies-output-affine-local
   (implies (affine-doubling-relation-p input slope output)
            (short-weierstrass-affine-point-p output))
   :hints (("Goal" :in-theory (enable affine-doubling-relation-p)))))

(local
 (defthm affine-d-t-bounded-left-cases-local
   (implies
    (and
     (affine-distinct-x-secant-relation-p a b p-slope p-output)
     (affine-doubling-relation-p b t-slope q-output)
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates a)
      (curve-point-affine-coordinates q-output) right)
     (or
      (and (equal (curve-point-fix left)
                  (curve-point-affine-coordinates
                   (affine-coordinates-fix left-payload)))
           (affine-distinct-x-secant-relation-p
            p-output b left-slope left-payload))
      (affine-opposite-y-infinity-relation-p p-output b left)
      (and (equal (affine-coordinates-fix p-output)
                  (affine-coordinates-fix b))
           (affine-doubling-relation-p
            p-output left-tangent left-payload))))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-d-t-outer-d-cell-local)
      (:instance affine-d-t-outer-o-cell-local)
      (:instance affine-dt-left-outer-doubling-impossible))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm curve-point-addition-relation-associative-affine-d-t-cell-local
   (implies
    (and
     (short-weierstrass-affine-point-p a)
     (short-weierstrass-affine-point-p b)
     (short-weierstrass-affine-point-p c)
     (affine-distinct-x-secant-relation-p a b p-slope p-output)
     (equal (curve-point-fix ab)
            (curve-point-affine-coordinates
             (affine-coordinates-fix p-output)))
     (affine-doubling-relation-p b t-slope q-output)
     (equal (affine-coordinates-fix b) (affine-coordinates-fix c))
     (equal (curve-point-fix bc)
            (curve-point-affine-coordinates
             (affine-coordinates-fix q-output)))
     (curve-point-addition-relation-p
      ab (curve-point-affine-coordinates c) left)
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates a) bc right))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance secant-relation-implies-output-affine-local
                 (first a) (second b) (slope p-slope) (output p-output))
      (:instance doubling-relation-implies-output-affine-local
                 (input b) (slope t-slope) (output q-output))
      (:instance addition-relation-transport-fixed-operands-local
                 (first-a ab) (second-a (curve-point-affine-coordinates c))
                 (output left)
                 (first-b (curve-point-affine-coordinates p-output))
                 (second-b (curve-point-affine-coordinates b)))
      (:instance addition-relation-transport-fixed-operands-local
                 (first-a (curve-point-affine-coordinates a)) (second-a bc)
                 (output right)
                 (first-b (curve-point-affine-coordinates a))
                 (second-b (curve-point-affine-coordinates q-output)))
      (:instance curve-point-addition-relation-affine-case-coverage
                 (a p-output) (b b) (output left))
      (:instance secant-relation-transport-fixed-operands-local
                 (first-a (affine-coordinates-fix p-output))
                 (second-a (affine-coordinates-fix b))
                 (first-b p-output) (second-b b)
                 (slope (field-div
                   (field-sub
                    (affine-coordinates-y (affine-coordinates-fix b))
                    (affine-coordinates-y (affine-coordinates-fix p-output)))
                   (field-sub
                    (affine-coordinates-x (affine-coordinates-fix b))
                    (affine-coordinates-x (affine-coordinates-fix p-output)))))
                 (output (curve-point-affine-coordinates-get
                          (curve-point-fix left))))
      (:instance doubling-relation-transport-fixed-input-local
                 (input-a (affine-coordinates-fix p-output))
                 (input-b p-output)
                 (slope (field-div
                   (field-add
                    (field-mul
                     (field-add (field-add (field-one) (field-one)) (field-one))
                     (field-mul
                      (affine-coordinates-x (affine-coordinates-fix p-output))
                      (affine-coordinates-x (affine-coordinates-fix p-output))))
                    (field-fix (short-weierstrass-a)))
                   (field-add
                    (affine-coordinates-y (affine-coordinates-fix p-output))
                    (affine-coordinates-y (affine-coordinates-fix p-output)))))
                 (output (curve-point-affine-coordinates-get
                          (curve-point-fix left))))
      (:instance affine-d-t-bounded-left-cases-local
                 (left-payload
                  (curve-point-affine-coordinates-get (curve-point-fix left)))
                 (left-slope
                  (field-div
                   (field-sub
                    (affine-coordinates-y (affine-coordinates-fix b))
                    (affine-coordinates-y (affine-coordinates-fix p-output)))
                   (field-sub
                    (affine-coordinates-x (affine-coordinates-fix b))
                    (affine-coordinates-x (affine-coordinates-fix p-output)))))
                 (left-tangent
                  (field-div
                   (field-add
                    (field-mul
                     (field-add (field-add (field-one) (field-one)) (field-one))
                     (field-mul
                      (affine-coordinates-x (affine-coordinates-fix p-output))
                      (affine-coordinates-x (affine-coordinates-fix p-output))))
                    (field-fix (short-weierstrass-a)))
                   (field-add
                    (affine-coordinates-y (affine-coordinates-fix p-output))
                    (affine-coordinates-y (affine-coordinates-fix p-output)))))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(curve-point-fix-of-affine-coordinates
        affine-coordinates-fix-idempotent
        affine-distinct-x-secant-relation-p-of-fixes
        affine-doubling-relation-p-of-fixes
        affine-opposite-y-infinity-relation-p-of-fixes))))))

; Inner T/D, right outer O, mirrored through the maintained D/T left-O theorem
; on reversed point order.  Determinacy pair is (tagged P, tagged B).
(local
 (defthm affine-t-d-right-o-cell-local
   (implies
    (and
     (affine-doubling-relation-p a t-slope p-output)
     (affine-distinct-x-secant-relation-p a b p-slope q-output)
     (affine-opposite-y-infinity-relation-p a q-output right)
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates p-output)
      (curve-point-affine-coordinates b) left))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-distinct-x-secant-relation-p-reverse
                 (first a) (second b) (slope p-slope) (output q-output))
      (:instance affine-opposite-y-infinity-relation-p-symmetric
                 (first a) (second q-output) (output right))
      (:instance
       affine-dt-left-output-opposite-y-propagates-to-right-output
       (a b) (b a) (p-slope p-slope) (p-output q-output)
       (t-slope t-slope) (q-output p-output) (infinity right))
      (:instance affine-opposite-y-infinity-relation-p-symmetric
                 (first b) (second p-output) (output right))
      (:instance opposite-y-relation-packages-as-full-addition-local
                 (a p-output) (b b) (output right))
      (:instance
       curve-point-addition-relation-output-determinate-under-fixed-operands
       (first-a (curve-point-affine-coordinates p-output))
       (second-a (curve-point-affine-coordinates b)) (output-a right)
       (first-b (curve-point-affine-coordinates p-output))
       (second-b (curve-point-affine-coordinates b)) (output-b left)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm affine-t-d-bounded-right-cases-local
   (implies
    (and
     (affine-doubling-relation-p a t-slope p-output)
     (affine-distinct-x-secant-relation-p a b p-slope q-output)
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates p-output)
      (curve-point-affine-coordinates b) left)
     (or
      (and (equal (curve-point-fix right)
                  (curve-point-affine-coordinates
                   (affine-coordinates-fix right-payload)))
           (affine-distinct-x-secant-relation-p
            a q-output right-slope right-payload))
      (affine-opposite-y-infinity-relation-p a q-output right)
      (and (equal (affine-coordinates-fix a)
                  (affine-coordinates-fix q-output))
           (affine-doubling-relation-p a right-tangent right-payload))))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance affine-t-d-outer-d-cell-local)
           (:instance affine-t-d-right-o-cell-local)
           (:instance affine-td-right-outer-doubling-impossible))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm curve-point-addition-relation-associative-affine-t-d-cell-local
   (implies
    (and
     (short-weierstrass-affine-point-p a)
     (short-weierstrass-affine-point-p b)
     (short-weierstrass-affine-point-p c)
     (affine-doubling-relation-p a t-slope p-output)
     (equal (affine-coordinates-fix a) (affine-coordinates-fix b))
     (equal (curve-point-fix ab)
            (curve-point-affine-coordinates (affine-coordinates-fix p-output)))
     (affine-distinct-x-secant-relation-p b c p-slope q-output)
     (equal (curve-point-fix bc)
            (curve-point-affine-coordinates (affine-coordinates-fix q-output)))
     (curve-point-addition-relation-p
      ab (curve-point-affine-coordinates c) left)
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates a) bc right))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance doubling-relation-implies-output-affine-local
                 (input a) (slope t-slope) (output p-output))
      (:instance secant-relation-implies-output-affine-local
                 (first b) (second c) (slope p-slope) (output q-output))
      (:instance secant-relation-transport-fixed-operands-local
                 (first-a b) (second-a c) (first-b a) (second-b c)
                 (slope p-slope) (output q-output))
      (:instance addition-relation-transport-fixed-operands-local
                 (first-a ab) (second-a (curve-point-affine-coordinates c))
                 (output left)
                 (first-b (curve-point-affine-coordinates p-output))
                 (second-b (curve-point-affine-coordinates c)))
      (:instance addition-relation-transport-fixed-operands-local
                 (first-a (curve-point-affine-coordinates a)) (second-a bc)
                 (output right)
                 (first-b (curve-point-affine-coordinates a))
                 (second-b (curve-point-affine-coordinates q-output)))
      (:instance curve-point-addition-relation-affine-case-coverage
                 (a a) (b q-output) (output right))
      (:instance secant-relation-transport-fixed-operands-local
                 (first-a (affine-coordinates-fix a))
                 (second-a (affine-coordinates-fix q-output))
                 (first-b a) (second-b q-output)
                 (slope
                  (field-div
                   (field-sub
                    (affine-coordinates-y (affine-coordinates-fix q-output))
                    (affine-coordinates-y (affine-coordinates-fix a)))
                   (field-sub
                    (affine-coordinates-x (affine-coordinates-fix q-output))
                    (affine-coordinates-x (affine-coordinates-fix a)))))
                 (output (curve-point-affine-coordinates-get
                          (curve-point-fix right))))
      (:instance doubling-relation-transport-fixed-input-local
                 (input-a (affine-coordinates-fix a)) (input-b a)
                 (slope
                  (field-div
                   (field-add
                    (field-mul
                     (field-add (field-add (field-one) (field-one)) (field-one))
                     (field-mul
                      (affine-coordinates-x (affine-coordinates-fix a))
                      (affine-coordinates-x (affine-coordinates-fix a))))
                    (field-fix (short-weierstrass-a)))
                   (field-add
                    (affine-coordinates-y (affine-coordinates-fix a))
                    (affine-coordinates-y (affine-coordinates-fix a)))))
                 (output (curve-point-affine-coordinates-get
                          (curve-point-fix right))))
      (:instance affine-t-d-bounded-right-cases-local
                 (b c)
                 (right-payload
                  (curve-point-affine-coordinates-get (curve-point-fix right)))
                 (right-slope
                  (field-div
                   (field-sub
                    (affine-coordinates-y (affine-coordinates-fix q-output))
                    (affine-coordinates-y (affine-coordinates-fix a)))
                   (field-sub
                    (affine-coordinates-x (affine-coordinates-fix q-output))
                    (affine-coordinates-x (affine-coordinates-fix a)))))
                 (right-tangent
                  (field-div
                   (field-add
                    (field-mul
                     (field-add (field-add (field-one) (field-one)) (field-one))
                     (field-mul
                      (affine-coordinates-x (affine-coordinates-fix a))
                      (affine-coordinates-x (affine-coordinates-fix a))))
                    (field-fix (short-weierstrass-a)))
                   (field-add
                    (affine-coordinates-y (affine-coordinates-fix a))
                    (affine-coordinates-y (affine-coordinates-fix a)))))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(curve-point-fix-of-affine-coordinates
        affine-coordinates-fix-idempotent
        affine-distinct-x-secant-relation-p-of-fixes
        affine-doubling-relation-p-of-fixes
        affine-opposite-y-infinity-relation-p-of-fixes))))))

; Ordered infinity consequences used by the four inverse cells.  These are the
; only inverse-cell helpers that open the full relation, solely to construct
; its ordered identity witness; determinacy then aligns the supplied output.
(local
 (defthm addition-relation-left-infinity-witness-local
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
     :use (addition-relation-left-infinity-witness-local
           (:instance curve-point-addition-relation-output-determinate
                      (output-a output) (output-b second)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm addition-relation-right-infinity-witness-local
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
     :use (addition-relation-right-infinity-witness-local
           (:instance curve-point-addition-relation-output-determinate
                      (output-a output) (output-b first)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm affine-o-t-derived-right-relation-local
   (implies
    (and (affine-opposite-y-infinity-relation-p a b infinity)
         (affine-doubling-relation-p b tangent u))
    (curve-point-addition-relation-p
     (curve-point-affine-coordinates a)
     (curve-point-affine-coordinates u)
     (curve-point-affine-coordinates b)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-inverse-tangent-translation)
      (:instance secant-relation-packages-as-full-addition-local
                 (a a) (b u) (slope (field-neg tangent)) (output b))
      (:instance doubling-relation-packages-as-full-addition-local
                 (a a) (slope (field-neg tangent)) (output b))
      (:instance addition-relation-transport-fixed-operands-local
                 (first-a (curve-point-affine-coordinates a))
                 (second-a (curve-point-affine-coordinates a))
                 (output (curve-point-affine-coordinates b))
                 (first-b (curve-point-affine-coordinates a))
                 (second-b (curve-point-affine-coordinates u))))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(curve-point-fix-of-affine-coordinates))))))

; O/T principal determinacy pair: (tagged A, tagged U).  Family output is
; tagged B and the supplied output is RIGHT; LEFT is the ordered infinity
; identity output on (AB, tagged B).
(local
 (defthm curve-point-addition-relation-associative-affine-o-t-cell-local
   (implies
    (and
     (affine-opposite-y-infinity-relation-p a b ab)
     (affine-doubling-relation-p b tangent u)
     (equal (affine-coordinates-fix b) (affine-coordinates-fix c))
     (equal (curve-point-fix bc)
            (curve-point-affine-coordinates (affine-coordinates-fix u)))
     (curve-point-addition-relation-p
      ab (curve-point-affine-coordinates c) left)
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates a) bc right))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance addition-relation-transport-fixed-operands-local
                 (first-a ab) (second-a (curve-point-affine-coordinates c))
                 (output left) (first-b ab)
                 (second-b (curve-point-affine-coordinates b)))
      (:instance addition-relation-left-infinity-output-local
                 (first ab) (second (curve-point-affine-coordinates b))
                 (output left))
      (:instance affine-o-t-derived-right-relation-local
                 (infinity ab))
      (:instance addition-relation-transport-fixed-operands-local
                 (first-a (curve-point-affine-coordinates a))
                 (second-a bc) (output right)
                 (first-b (curve-point-affine-coordinates a))
                 (second-b (curve-point-affine-coordinates u)))
      (:instance
       curve-point-addition-relation-output-determinate-under-fixed-operands
       (first-a (curve-point-affine-coordinates a))
       (second-a (curve-point-affine-coordinates u))
       (output-a (curve-point-affine-coordinates b))
       (first-b (curve-point-affine-coordinates a))
       (second-b (curve-point-affine-coordinates u))
       (output-b right)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(affine-opposite-y-infinity-relation-p
        curve-point-fix-of-affine-coordinates
        affine-coordinates-fix-idempotent))))))

(local
 (defthm affine-o-d-derived-right-relation-local
   (implies
    (and (short-weierstrass-characteristic-p)
         (affine-opposite-y-infinity-relation-p a b infinity)
         (affine-distinct-x-secant-relation-p b c slope u))
    (curve-point-addition-relation-p
     (curve-point-affine-coordinates a)
     (curve-point-affine-coordinates u)
     (curve-point-affine-coordinates c)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-inverse-secant-translation (r slope))
      (:instance secant-relation-packages-as-full-addition-local
                 (a a) (b u) (slope (field-neg (field-fix slope)))
                 (output c))
      (:instance doubling-relation-packages-as-full-addition-local
                 (a a) (slope (field-neg (field-fix slope))) (output c))
      (:instance addition-relation-transport-fixed-operands-local
                 (first-a (curve-point-affine-coordinates a))
                 (second-a (curve-point-affine-coordinates a))
                 (output (curve-point-affine-coordinates c))
                 (first-b (curve-point-affine-coordinates a))
                 (second-b (curve-point-affine-coordinates u))))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(curve-point-fix-of-affine-coordinates))))))

; O/D principal determinacy pair: (tagged A, tagged U).  Family output is
; tagged C and supplied output is RIGHT; LEFT is infinity+C.
(local
 (defthm curve-point-addition-relation-associative-affine-o-d-cell-local
   (implies
    (and
     (short-weierstrass-characteristic-p)
     (affine-opposite-y-infinity-relation-p a b ab)
     (affine-distinct-x-secant-relation-p b c slope u)
     (equal (curve-point-fix bc)
            (curve-point-affine-coordinates (affine-coordinates-fix u)))
     (curve-point-addition-relation-p
      ab (curve-point-affine-coordinates c) left)
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates a) bc right))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance addition-relation-left-infinity-output-local
                 (first ab) (second (curve-point-affine-coordinates c))
                 (output left))
      (:instance affine-o-d-derived-right-relation-local (infinity ab))
      (:instance addition-relation-transport-fixed-operands-local
                 (first-a (curve-point-affine-coordinates a))
                 (second-a bc) (output right)
                 (first-b (curve-point-affine-coordinates a))
                 (second-b (curve-point-affine-coordinates u)))
      (:instance
       curve-point-addition-relation-output-determinate-under-fixed-operands
       (first-a (curve-point-affine-coordinates a))
       (second-a (curve-point-affine-coordinates u))
       (output-a (curve-point-affine-coordinates c))
       (first-b (curve-point-affine-coordinates a))
       (second-b (curve-point-affine-coordinates u))
       (output-b right)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(affine-opposite-y-infinity-relation-p
        curve-point-fix-of-affine-coordinates
        affine-coordinates-fix-idempotent))))))

; T/O is the point-order mirror of O/T.  Principal comparison in the invoked
; cell is (tagged B, tagged P), semantically reversed from supplied P+B.
(local
 (defthm curve-point-addition-relation-associative-affine-t-o-cell-local
   (implies
    (and
     (affine-doubling-relation-p a tangent p)
     (equal (affine-coordinates-fix a) (affine-coordinates-fix b))
     (equal (curve-point-fix ab)
            (curve-point-affine-coordinates (affine-coordinates-fix p)))
     (affine-opposite-y-infinity-relation-p b c bc)
     (curve-point-addition-relation-p
      ab (curve-point-affine-coordinates c) left)
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates a) bc right))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance doubling-relation-transport-fixed-input-local
                 (input-a a) (input-b b) (slope tangent) (output p))
      (:instance affine-opposite-y-infinity-relation-p-symmetric
                 (first b) (second c) (output bc))
      (:instance curve-point-addition-relation-p-commutative
                 (first ab) (second (curve-point-affine-coordinates c))
                 (output left))
      (:instance curve-point-addition-relation-p-commutative
                 (first (curve-point-affine-coordinates a)) (second bc)
                 (output right))
      (:instance curve-point-addition-relation-associative-affine-o-t-cell-local
                 (a c) (b b) (c a) (ab bc)
                 (tangent tangent) (u p) (bc ab)
                 (left right) (right left)))
     :in-theory (theory 'minimal-theory)))))
; D/O is the point-order mirror of O/D.  The invoked determinacy pair is
; (tagged C, tagged P), the semantic reversal of supplied P+C.
(local
 (defthm curve-point-addition-relation-associative-affine-d-o-cell-local
   (implies
    (and
     (short-weierstrass-characteristic-p)
     (affine-distinct-x-secant-relation-p a b slope p)
     (equal (curve-point-fix ab)
            (curve-point-affine-coordinates (affine-coordinates-fix p)))
     (affine-opposite-y-infinity-relation-p b c bc)
     (curve-point-addition-relation-p
      ab (curve-point-affine-coordinates c) left)
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates a) bc right))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-distinct-x-secant-relation-p-reverse
                 (first a) (second b) (slope slope) (output p))
      (:instance affine-opposite-y-infinity-relation-p-symmetric
                 (first b) (second c) (output bc))
      (:instance curve-point-addition-relation-p-commutative
                 (first ab) (second (curve-point-affine-coordinates c))
                 (output left))
      (:instance curve-point-addition-relation-p-commutative
                 (first (curve-point-affine-coordinates a)) (second bc)
                 (output right))
      (:instance curve-point-addition-relation-associative-affine-o-d-cell-local
                 (a c) (b b) (ab bc) (c a)
                 (slope slope) (u p) (bc ab)
                 (left right) (right left)))
     :in-theory (theory 'minimal-theory)))))

; Purely propositional nine-cell matrix combination.  All semantic work is in
; the local cells above; this lemma only names the two bounded D/O/T rows.
(local
 (defthm affine-extracted-case-normalizes-fixed-inputs-local
   (implies
    (or
     (and (equal (curve-point-fix output)
                 (curve-point-affine-coordinates
                  (affine-coordinates-fix payload)))
          (affine-distinct-x-secant-relation-p
           (affine-coordinates-fix a) (affine-coordinates-fix b)
           secant-slope payload))
     (affine-opposite-y-infinity-relation-p a b output)
     (and (equal (curve-point-fix output)
                 (curve-point-affine-coordinates
                  (affine-coordinates-fix payload)))
          (equal (affine-coordinates-fix a)
                 (affine-coordinates-fix b))
          (affine-doubling-relation-p
           (affine-coordinates-fix a) tangent-slope payload)))
    (or
     (and (equal (curve-point-fix output)
                 (curve-point-affine-coordinates
                  (affine-coordinates-fix payload)))
          (affine-distinct-x-secant-relation-p
           a b secant-slope payload))
     (affine-opposite-y-infinity-relation-p a b output)
     (and (equal (curve-point-fix output)
                 (curve-point-affine-coordinates
                  (affine-coordinates-fix payload)))
          (equal (affine-coordinates-fix a)
                 (affine-coordinates-fix b))
          (affine-doubling-relation-p a tangent-slope payload))))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance secant-relation-transport-fixed-operands-local
                 (first-a (affine-coordinates-fix a))
                 (second-a (affine-coordinates-fix b))
                 (first-b a) (second-b b)
                 (slope secant-slope) (output payload))
      (:instance doubling-relation-transport-fixed-input-local
                 (input-a (affine-coordinates-fix a)) (input-b a)
                 (slope tangent-slope) (output payload))
      (:instance affine-coordinates-fix-idempotent (coordinates a))
      (:instance affine-coordinates-fix-idempotent (coordinates b)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm affine-associativity-nine-cell-combination-local
   (implies
    (and
     (short-weierstrass-characteristic-p)
     (short-weierstrass-affine-point-p a)
     (short-weierstrass-affine-point-p b)
     (short-weierstrass-affine-point-p c)
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates a)
      (curve-point-affine-coordinates b) ab)
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates b)
      (curve-point-affine-coordinates c) bc)
     (curve-point-addition-relation-p
      ab (curve-point-affine-coordinates c) left)
     (curve-point-addition-relation-p
      (curve-point-affine-coordinates a) bc right)
     (or
      (and (equal (curve-point-fix ab)
                  (curve-point-affine-coordinates
                   (affine-coordinates-fix ab-payload)))
           (affine-distinct-x-secant-relation-p
            a b ab-secant-slope ab-payload))
      (affine-opposite-y-infinity-relation-p a b ab)
      (and (equal (curve-point-fix ab)
                  (curve-point-affine-coordinates
                   (affine-coordinates-fix ab-payload)))
           (equal (affine-coordinates-fix a)
                  (affine-coordinates-fix b))
           (affine-doubling-relation-p
            a ab-tangent-slope ab-payload)))
     (or
      (and (equal (curve-point-fix bc)
                  (curve-point-affine-coordinates
                   (affine-coordinates-fix bc-payload)))
           (affine-distinct-x-secant-relation-p
            b c bc-secant-slope bc-payload))
      (affine-opposite-y-infinity-relation-p b c bc)
      (and (equal (curve-point-fix bc)
                  (curve-point-affine-coordinates
                   (affine-coordinates-fix bc-payload)))
           (equal (affine-coordinates-fix b)
                  (affine-coordinates-fix c))
           (affine-doubling-relation-p
            b bc-tangent-slope bc-payload))))
    (equal (curve-point-fix left) (curve-point-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance curve-point-addition-relation-associative-affine-d-d-cell-local)
      (:instance curve-point-addition-relation-associative-affine-d-o-cell-local
                 (slope ab-secant-slope) (p ab-payload))
      (:instance curve-point-addition-relation-associative-affine-d-t-cell-local
                 (p-slope ab-secant-slope) (p-output ab-payload)
                 (t-slope bc-tangent-slope) (q-output bc-payload))
      (:instance curve-point-addition-relation-associative-affine-o-d-cell-local
                 (slope bc-secant-slope) (u bc-payload))
      (:instance curve-point-addition-relation-associative-affine-o-o-cell-local)
      (:instance curve-point-addition-relation-associative-affine-o-t-cell-local
                 (tangent bc-tangent-slope) (u bc-payload))
      (:instance curve-point-addition-relation-associative-affine-t-d-cell-local
                 (t-slope ab-tangent-slope) (p-output ab-payload)
                 (p-slope bc-secant-slope) (q-output bc-payload))
      (:instance curve-point-addition-relation-associative-affine-t-o-cell-local
                 (tangent ab-tangent-slope) (p ab-payload))
      (:instance curve-point-addition-relation-associative-affine-t-t-cell-local))
     :in-theory (theory 'minimal-theory)))))

(defthm curve-point-addition-relation-associative-for-affine-inputs
  (implies
   (and
    (short-weierstrass-characteristic-p)
    (short-weierstrass-affine-point-p a)
    (short-weierstrass-affine-point-p b)
    (short-weierstrass-affine-point-p c)

    (curve-point-addition-relation-p
     (curve-point-affine-coordinates a)
     (curve-point-affine-coordinates b)
     ab)

    (curve-point-addition-relation-p
     (curve-point-affine-coordinates b)
     (curve-point-affine-coordinates c)
     bc)

    (curve-point-addition-relation-p
     ab
     (curve-point-affine-coordinates c)
     left)

    (curve-point-addition-relation-p
     (curve-point-affine-coordinates a)
     bc
     right))
   (equal (curve-point-fix left)
          (curve-point-fix right)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance curve-point-addition-relation-affine-case-coverage
                (a a) (b b) (output ab))
     (:instance curve-point-addition-relation-affine-case-coverage
                (a b) (b c) (output bc))
     (:instance affine-extracted-case-normalizes-fixed-inputs-local
                (a a) (b b) (output ab)
                (payload (curve-point-affine-coordinates-get
                          (curve-point-fix ab)))
                (secant-slope
                 (field-div
                  (field-sub
                   (affine-coordinates-y (affine-coordinates-fix b))
                   (affine-coordinates-y (affine-coordinates-fix a)))
                  (field-sub
                   (affine-coordinates-x (affine-coordinates-fix b))
                   (affine-coordinates-x (affine-coordinates-fix a)))))
                (tangent-slope
                 (field-div
                  (field-add
                   (field-mul
                    (field-add (field-add (field-one) (field-one))
                               (field-one))
                    (field-mul
                     (affine-coordinates-x (affine-coordinates-fix a))
                     (affine-coordinates-x (affine-coordinates-fix a))))
                   (field-fix (short-weierstrass-a)))
                  (field-add
                   (affine-coordinates-y (affine-coordinates-fix a))
                   (affine-coordinates-y (affine-coordinates-fix a))))))
     (:instance affine-extracted-case-normalizes-fixed-inputs-local
                (a b) (b c) (output bc)
                (payload (curve-point-affine-coordinates-get
                          (curve-point-fix bc)))
                (secant-slope
                 (field-div
                  (field-sub
                   (affine-coordinates-y (affine-coordinates-fix c))
                   (affine-coordinates-y (affine-coordinates-fix b)))
                  (field-sub
                   (affine-coordinates-x (affine-coordinates-fix c))
                   (affine-coordinates-x (affine-coordinates-fix b)))))
                (tangent-slope
                 (field-div
                  (field-add
                   (field-mul
                    (field-add (field-add (field-one) (field-one))
                               (field-one))
                    (field-mul
                     (affine-coordinates-x (affine-coordinates-fix b))
                     (affine-coordinates-x (affine-coordinates-fix b))))
                   (field-fix (short-weierstrass-a)))
                  (field-add
                   (affine-coordinates-y (affine-coordinates-fix b))
                   (affine-coordinates-y (affine-coordinates-fix b))))))
     (:instance affine-associativity-nine-cell-combination-local
                (ab-payload
                 (curve-point-affine-coordinates-get (curve-point-fix ab)))
                (ab-secant-slope
                 (field-div
                  (field-sub
                   (affine-coordinates-y (affine-coordinates-fix b))
                   (affine-coordinates-y (affine-coordinates-fix a)))
                  (field-sub
                   (affine-coordinates-x (affine-coordinates-fix b))
                   (affine-coordinates-x (affine-coordinates-fix a)))))
                (ab-tangent-slope
                 (field-div
                  (field-add
                   (field-mul
                    (field-add (field-add (field-one) (field-one))
                               (field-one))
                    (field-mul
                     (affine-coordinates-x (affine-coordinates-fix a))
                     (affine-coordinates-x (affine-coordinates-fix a))))
                   (field-fix (short-weierstrass-a)))
                  (field-add
                   (affine-coordinates-y (affine-coordinates-fix a))
                   (affine-coordinates-y (affine-coordinates-fix a)))))
                (bc-payload
                 (curve-point-affine-coordinates-get (curve-point-fix bc)))
                (bc-secant-slope
                 (field-div
                  (field-sub
                   (affine-coordinates-y (affine-coordinates-fix c))
                   (affine-coordinates-y (affine-coordinates-fix b)))
                  (field-sub
                   (affine-coordinates-x (affine-coordinates-fix c))
                   (affine-coordinates-x (affine-coordinates-fix b)))))
                (bc-tangent-slope
                 (field-div
                  (field-add
                   (field-mul
                    (field-add (field-add (field-one) (field-one))
                               (field-one))
                    (field-mul
                     (affine-coordinates-x (affine-coordinates-fix b))
                     (affine-coordinates-x (affine-coordinates-fix b))))
                   (field-fix (short-weierstrass-a)))
                  (field-add
                   (affine-coordinates-y (affine-coordinates-fix b))
                   (affine-coordinates-y (affine-coordinates-fix b)))))))
    :in-theory (theory 'minimal-theory))))
