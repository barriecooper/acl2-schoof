(in-package "GFIELD")
(include-book "xcert-algebra")

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
    (field-add
     (field-add
      (field-sub (field-mul q (field-sub xbc xa))
                 (field-mul r (field-sub xbc xa)))
      (field-mul p (field-sub xbc xab)))
     (field-add (field-neg yab) (field-neg ybc)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance xcert-s-output-y-bridge-local))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(field-sub field-mul-left-distributive field-mul-right-distributive
              field-mul-associative field-mul-commutative
              field-mul-of-neg-right-local field-mul-of-neg-left-local
              field-neg-of-add-local field-neg-of-neg
              field-add-associative field-add-commutative
              field-add-inverse-left field-add-inverse-right
              field-add-zero-left field-add-zero-right
              field-fix-of-add field-fix-of-mul field-fix-of-neg))))))

; CONTINUATION CHECKPOINT (uncertified):
; XCERT-S-OUTPUT-Y-BRIDGE-LOCAL certifies before the following event is reached.
; The remaining goal for XCERT-S-EIGHT-EQUATION-RESIDUAL-LOCAL is a finite
; additive permutation.  Its useful bridge is exactly
;   p*(xa-xab) + tt*(xbc-xa) = yab+ybc.
; Continue by introducing a local FIELD-SUM-LIST/PERM lemma (as in
; xcert-h-reconstruction.lisp), or stage the target as
;   q*D-r*D+p*xbc - (p*xab+yab+ybc), D=xbc-xa,
; so that the bridge rewrites one grouped subterm.  The candidate residual has
; been checked through ACL2 expansion; no secant equations are needed for this
; first checkpoint, despite the deliberately retained eight-equation statement.
