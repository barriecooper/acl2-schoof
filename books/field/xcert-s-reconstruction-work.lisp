(in-package "GFIELD")
(include-book "xcert-h-reconstruction")

; Temporary proof-development book for the exact S reconstruction.
; E4--E11 below preserve the ordered differences of the semantic secants.
(local
 (defthm field-mul-of-neg-right-local
  (equal (field-mul x (field-neg y)) (field-neg (field-mul x y)))
  :hints (("Goal" :use ((:instance field-additive-inverse-unique
                          (x (field-mul x y)) (y (field-mul x (field-neg y))))
                         (:instance field-mul-left-distributive
                          (x x) (y y) (z (field-neg y))))
           :in-theory (union-theories (theory 'minimal-theory)
                       '(field-add-inverse-right field-mul-zero-right
                         field-fix-of-mul))))))
(local
 (defthm field-mul-of-neg-left-local
  (equal (field-mul (field-neg x) y) (field-neg (field-mul x y)))
  :hints (("Goal" :use ((:instance field-mul-commutative
                          (x (field-neg x)) (y y))
                         (:instance field-mul-commutative (x y) (y x))
                         (:instance field-mul-of-neg-right-local (x y) (y x)))
           :in-theory (theory 'minimal-theory)))))
(local (defthm field-add-swap-local
 (equal (field-add x (field-add y z)) (field-add y (field-add x z)))
 :hints (("Goal" :use ((:instance field-add-associative (x x)(y y)(z z))
                        (:instance field-add-associative (x y)(y x)(z z))
                        (:instance field-add-commutative (x x)(y y)))
          :in-theory (union-theories (theory 'minimal-theory) '(field-fix-of-add))))))
(local (defthm field-add-inverse-tail-local
 (equal (field-add x (field-add (field-neg x) y)) (field-fix y))
 :hints (("Goal" :use ((:instance field-add-associative
                         (x x) (y (field-neg x)) (z y)))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(field-add-inverse-right field-add-zero-left
                         field-fix-idempotent))))))
(local (defthm field-add-inverse-shuffle-local
 (equal (field-add x (field-add y (field-add (field-neg x) z)))
        (field-add y (field-fix z)))
 :hints (("Goal" :use ((:instance field-add-swap-local
                         (x x) (y y) (z (field-add (field-neg x) z)))
                        (:instance field-add-inverse-tail-local (x x) (y z)))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(field-add-swap-local field-add-inverse-tail-local
                         field-add-fix-right))))))
(local
 (defthm field-neg-of-add-local
  (equal (field-neg (field-add x y))
         (field-add (field-neg x) (field-neg y)))
  :hints (("Goal" :use ((:instance field-additive-inverse-unique
                          (x (field-add x y))
                          (y (field-add (field-neg x) (field-neg y)))))
           :in-theory (union-theories (theory 'minimal-theory)
                       '(field-add-associative field-add-inverse-shuffle-local
                         field-add-inverse-right field-add-zero-left
                         field-fix-of-add field-fix-of-neg))))))

(local
 (defthm field-add-cancel-around-local
  (equal (field-add x (field-add y (field-add z (field-neg x))))
         (field-add y (field-fix z)))
  :hints (("Goal"
           :use ((:instance field-add-swap-local
                             (x x) (y y) (z (field-add z (field-neg x))))
                 (:instance field-add-swap-local
                             (x x) (y z) (z (field-neg x))))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(field-add-associative field-add-inverse-right
                          field-add-zero-right field-add-fix-right))))))

(local
 (defthm xcert-s-output-y-bridge-local
  (implies
   (and (equal (field-add yab ya)
               (field-mul p (field-sub xa xab)))
        (equal (field-mul tt (field-sub xbc xa))
               (field-sub ybc ya)))
   (equal (field-add (field-mul p (field-sub xa xab))
                     (field-mul tt (field-sub xbc xa)))
          (field-add yab ybc)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :in-theory
           (union-theories (theory 'minimal-theory)
            '(field-sub field-add-associative field-add-commutative
              field-add-inverse-shuffle-local field-add-swap-local
              field-add-cancel-around-local field-add-inverse-left field-add-inverse-right
              field-add-zero-left field-add-zero-right field-add-fix-right
              field-fix-of-add field-fix-of-neg))))))

(local
 (defthm xcert-s-factored-stage-local
  (equal
   (field-mul (field-sub xbc xa)
              (field-sub (field-add p q) (field-add r tt)))
   (field-sub
    (field-add (field-sub (field-mul q (field-sub xbc xa))
                          (field-mul r (field-sub xbc xa)))
               (field-mul p xbc))
    (field-add (field-mul p xa)
               (field-mul tt (field-sub xbc xa)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (union-theories (theory 'minimal-theory)
            '(field-sub field-mul-left-distributive field-mul-right-distributive
              field-mul-associative field-mul-commutative
              field-mul-of-neg-right-local field-mul-of-neg-left-local
              field-neg-of-add-local field-neg-of-neg field-add-swap-local
              field-add-associative field-add-commutative
              field-add-inverse-left field-add-inverse-right
              field-add-zero-left field-add-zero-right
              field-fix-of-add field-fix-of-mul field-fix-of-neg))))))

(local
 (defthm field-add-neg-move-right-local
  (implies (equal (field-add x (field-neg z)) y)
           (equal (field-fix x) (field-add y z)))
  :hints (("Goal"
           :use ((:instance field-add-fixed-congruence
                   (x1 (field-add x (field-neg z))) (x2 y)
                   (y1 z) (y2 z)))
           :in-theory (union-theories (theory 'minimal-theory)
            '(field-add-associative field-add-inverse-left
              field-add-zero-right field-add-fix-left field-add-fix-right
              field-fix-of-add field-fix-of-neg field-fix-idempotent))))))

(local
 (defthm xcert-s-output-y-regroup-local
  (implies
   (equal (field-add (field-mul p (field-sub xa xab))
                     (field-mul tt (field-sub xbc xa)))
          (field-add yab ybc))
   (equal (field-add (field-mul p xa)
                     (field-mul tt (field-sub xbc xa)))
          (field-add (field-mul p xab) (field-add yab ybc))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance field-add-neg-move-right-local
                   (x (field-add (field-mul p xa)
                        (field-mul tt (field-sub xbc xa))))
                   (z (field-mul p xab))
                   (y (field-add yab ybc))))
           :in-theory (union-theories (theory 'minimal-theory)
            '(field-sub field-mul-left-distributive
              field-mul-of-neg-right-local field-add-associative
              field-add-commutative field-add-swap-local field-add-fix-left
              field-add-fix-right field-fix-of-add field-fix-of-mul
              field-fix-of-neg))))))

(local
 (defthm xcert-s-eight-equation-residual-local
  (implies
   (and
    (equal (field-mul p (field-sub xb xa)) (field-sub yb ya))
    (equal (field-mul q (field-sub xc xab)) (field-sub yc yab))
    (equal (field-mul r (field-sub xc xb)) (field-sub yc yb))
    (equal (field-mul tt (field-sub xbc xa)) (field-sub ybc ya))
    (equal (field-add (field-add xab xa) xb) (field-mul p p))
    (equal (field-add yab ya) (field-mul p (field-sub xa xab)))
    (equal (field-add (field-add xbc xb) xc) (field-mul r r))
    (equal (field-add ybc yb) (field-mul r (field-sub xb xbc))))
   (equal
    (field-mul (field-sub xbc xa)
               (field-sub (field-add p q) (field-add r tt)))
    (field-sub
     (field-add
      (field-sub (field-mul q (field-sub xbc xa))
                 (field-mul r (field-sub xbc xa)))
      (field-mul p xbc))
     (field-add (field-mul p xab) (field-add yab ybc)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance xcert-s-output-y-bridge-local)
                 (:instance xcert-s-output-y-regroup-local)
                 (:instance xcert-s-factored-stage-local))
           :in-theory (theory 'minimal-theory)))))

; The retained residual is now certified in its staged, equation-shaped form.
; The next event records the exact four ordered input-secant candidates.  It is
; intentionally retained as the current proof-development checkpoint.
(local
 (defthm field-neg-fixed-congruence-local
  (implies (equal (field-fix x) (field-fix y))
           (equal (field-neg x) (field-neg y)))
  :hints (("Goal" :use ((:instance field-neg-of-fix (x x))
                           (:instance field-neg-of-fix (x y)))
           :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-slope-equation-reverse-local
  (implies (equal (field-mul slope (field-sub x2 x1))
                  (field-sub y2 y1))
           (equal (field-mul slope (field-sub x1 x2))
                  (field-sub y1 y2)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance field-neg-fixed-congruence-local
                   (x (field-mul slope (field-sub x2 x1)))
                   (y (field-sub y2 y1))))
           :in-theory (union-theories (theory 'minimal-theory)
            '(field-sub field-add-associative field-add-commutative
              field-add-inverse-left field-add-inverse-right
              field-mul-left-distributive field-mul-right-distributive
              field-neg-of-add-local field-neg-of-neg
              field-mul-of-neg-right-local field-add-fix-left field-fix-of-add
              field-fix-of-mul field-fix-of-neg))))))

; Concrete q-route residual segment.  The displayed input keeps exactly the
; q*xbc, -q*xa, and -yab terms occurring in the retained residual.
(local
 (defthm xcert-s-q-slope-residual-segment-local
  (implies
   (equal (field-mul q (field-sub xc xab)) (field-sub yc yab))
   (equal
    (field-add (field-sub (field-mul q xbc) (field-mul q xa))
               (field-neg yab))
    (field-add (field-sub (field-mul q xbc) (field-mul q xa))
               (field-sub (field-mul q (field-sub xc xab)) yc))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance field-add-cancel-around-local
                   (x yc) (y (field-neg yab))
                   (z (field-sub (field-mul q xbc) (field-mul q xa)))))
           :in-theory (union-theories (theory 'minimal-theory)
            '(field-sub field-add-associative field-add-commutative
              field-add-swap-local field-add-cancel-around-local field-add-inverse-left
              field-add-inverse-right field-add-zero-left
              field-add-zero-right field-add-fix-left field-add-fix-right
              field-fix-of-add field-fix-of-neg))))))

; Exact expanded q input-secant segment.  This exposes the named secant
; equation in additive residual syntax before combining it with the q-route
; segment above.
(local
 (defthm xcert-s-q-input-secant-segment-local
  (implies
   (equal (field-mul q (field-add yc yab))
          (field-add (field-mul xc xc)
           (field-add (field-mul xc xab)
            (field-add (field-mul xab xab) curve-a))))
   (equal
    (field-sub
     (field-add (field-mul q yc) (field-mul q yab))
     (field-add (field-mul xc xc)
      (field-add (field-mul xc xab)
       (field-add (field-mul xab xab) curve-a))))
    (field-zero)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (union-theories (theory 'minimal-theory)
            '(field-sub field-mul-left-distributive field-fix-of-add
              field-fix-of-mul field-fix-of-neg field-add-inverse-right field-sub-self))))))

(local
 (defthm xcert-s-residual-combination-local
  (equal
   (field-sub
    (field-add
     (field-sub (field-mul q (field-sub xbc xa))
                (field-mul r (field-sub xbc xa)))
     (field-mul p xbc))
    (field-add (field-mul p xab) (field-add yab ybc)))
   (field-add
    (field-neg (field-sub (field-mul q (field-sub xc xab))
                          (field-sub yc yab)))
    (field-add
     (field-sub (field-mul r (field-sub xc xb)) (field-sub yc yb))
     (field-add
      (field-neg
       (field-mul (field-add p q)
        (field-sub (field-add (field-add xab xa) xb) (field-mul p p))))
      (field-add
       (field-mul (field-add p q)
        (field-sub (field-add (field-add xbc xb) xc) (field-mul r r)))
       (field-add
        (field-neg
         (field-sub (field-add ybc yb)
                    (field-mul r (field-sub xb xbc))))
        (field-neg
         (field-mul (field-add p r)
          (field-sub
           (field-mul (field-sub p r) (field-add p q))
           (field-sub xa xc))))))))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (union-theories (theory 'minimal-theory)
            '(field-sub field-mul-left-distributive field-mul-right-distributive
              field-mul-associative field-mul-commutative
              field-mul-of-neg-right-local field-mul-of-neg-left-local
              field-neg-of-add-local field-neg-of-neg field-add-swap-local
              field-add-associative field-add-commutative
              field-add-inverse-left field-add-inverse-right
              field-add-zero-left field-add-zero-right field-add-fix-left
              field-add-fix-right field-fix-of-add field-fix-of-mul
              field-fix-of-neg field-fix-of-zero))))))

(local
 (defthm xcert-s-residual-zero-from-h-local
  (implies
   (and
    (equal (field-mul (field-sub p r) (field-add p q))
           (field-sub xa xc))
    (equal (field-mul q (field-sub xc xab)) (field-sub yc yab))
    (equal (field-mul r (field-sub xc xb)) (field-sub yc yb))
    (equal (field-add (field-add xab xa) xb) (field-mul p p))
    (equal (field-add (field-add xbc xb) xc) (field-mul r r))
    (equal (field-add ybc yb) (field-mul r (field-sub xb xbc))))
   (equal
    (field-sub
     (field-add
      (field-sub (field-mul q (field-sub xbc xa))
                 (field-mul r (field-sub xbc xa)))
      (field-mul p xbc))
     (field-add (field-mul p xab) (field-add yab ybc)))
    (field-zero)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance xcert-s-residual-combination-local))
           :in-theory (union-theories (theory 'minimal-theory)
            '(field-sub field-mul-left-distributive field-mul-right-distributive
              field-mul-associative field-mul-commutative
              field-mul-of-neg-right-local field-mul-of-neg-left-local
              field-neg-of-add-local field-neg-of-neg field-add-swap-local
              field-add-associative field-add-commutative
              field-add-cancel-around-local field-add-inverse-tail-local
              field-add-inverse-left field-add-inverse-right
              field-add-zero-left field-add-zero-right field-add-fix-left
              field-add-fix-right field-fix-of-add field-fix-of-mul
              field-fix-of-neg field-fix-of-zero))))))

(local
 (defthm xcert-s-residual-zero-local
  (implies
   (and
    (equal (field-mul p (field-add yb ya))
           (field-add (field-mul xb xb)
            (field-add (field-mul xb xa)
             (field-add (field-mul xa xa) curve-a))))
    (equal (field-mul q (field-add yc yab))
           (field-add (field-mul xc xc)
            (field-add (field-mul xc xab)
             (field-add (field-mul xab xab) curve-a))))
    (equal (field-mul r (field-add yc yb))
           (field-add (field-mul xc xc)
            (field-add (field-mul xc xb)
             (field-add (field-mul xb xb) curve-a))))
    (equal (field-mul tt (field-add ybc ya))
           (field-add (field-mul xbc xbc)
            (field-add (field-mul xbc xa)
             (field-add (field-mul xa xa) curve-a))))
    (equal (field-mul p (field-sub xb xa)) (field-sub yb ya))
    (equal (field-mul q (field-sub xc xab)) (field-sub yc yab))
    (equal (field-mul r (field-sub xc xb)) (field-sub yc yb))
    (equal (field-mul tt (field-sub xbc xa)) (field-sub ybc ya))
    (equal (field-add (field-add xab xa) xb) (field-mul p p))
    (equal (field-add yab ya) (field-mul p (field-sub xa xab)))
    (equal (field-add (field-add xbc xb) xc) (field-mul r r))
    (equal (field-add ybc yb) (field-mul r (field-sub xb xbc)))
    (not (equal (field-sub xc xb) (field-zero))))
   (equal
    (field-sub
     (field-add
      (field-sub (field-mul q (field-sub xbc xa))
                 (field-mul r (field-sub xbc xa)))
      (field-mul p xbc))
     (field-add (field-mul p xab) (field-add yab ybc)))
    (field-zero)))
  :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
           :use ((:instance xcert-h-scalar-reconstruction
                   (a curve-a))
                 (:instance xcert-s-residual-zero-from-h-local))
           :in-theory (union-theories (theory 'minimal-theory)
            '(field-sub field-mul-left-distributive field-mul-right-distributive
              field-mul-associative field-mul-commutative
              field-mul-of-neg-right-local field-mul-of-neg-left-local
              field-neg-of-add-local field-neg-of-neg field-add-swap-local
              field-add-associative field-add-commutative
              field-add-inverse-left field-add-inverse-right
              field-add-zero-left field-add-zero-right
              field-fix-of-add field-fix-of-mul field-fix-of-neg))))))

; CONTINUATION CHECKPOINT: the complete log leaves exactly
;   -yab-ybc+p*xbc+q*xbc+r*xa-p*xab-q*xa-r*xbc = 0.
; The four secant equations are present above in the maintained order.  Continue
; by proving equation-shaped segment expansions before any term permutation;
; do not re-expand XCERT-S-EIGHT-EQUATION-RESIDUAL-LOCAL, which certifies.
; FIELD-SLOPE-EQUATION-REVERSE-LOCAL now certifies an explicit reversal of an
; ordered slope equation by negating both sides.  It is available for segment
; decompositions that require the opposite displayed difference; the retained
; secant and slope hypotheses themselves remain in their authoritative order.
; The q-route segment and expanded q input-secant segment above both certify.
; Next combine them after multiplying/moving only the required q-route terms;
; then construct the analogous r-route segment before normalizing the remainder.
; Retained combination checkpoint: XCERT-S-RESIDUAL-COMBINATION-LOCAL encodes
;   -E_q-slope + E_r-slope -(p+q)E_AB-x +(p+q)E_BC-x
;   -E_BC-y -(p+r)E_H.
; Its expanded ACL2 goal is now solely a finite additive permutation.  Continue
; with a local FIELD-SUM-LIST expansion/permutation for this exact combination;
; then XCERT-S-RESIDUAL-ZERO-FROM-H-LOCAL consumes the certified public H
; reconstruction rather than separately re-normalizing the four secant cubics.
