(in-package "GFIELD")
(include-book "xcert-h-reconstruction")
(include-book "sorting/perm" :dir :system)

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

(local (defun field-sum-list (xs)
 (if (consp xs) (field-add (car xs) (field-sum-list (cdr xs))) (field-zero))))
(local (defthm field-sum-list-of-rm-local
 (implies (acl2::memb a xs)
  (equal (field-sum-list xs)
         (field-add a (field-sum-list (acl2::rm a xs)))))
 :hints (("Goal" :induct (acl2::rm a xs)
          :in-theory (enable field-sum-list field-add-swap-local)))))
(local (defthm field-sum-list-perm-local
 (implies (acl2::perm xs ys)
          (equal (field-sum-list xs) (field-sum-list ys)))
 :rule-classes nil
 :hints (("Goal" :induct (acl2::perm xs ys))
         ("Subgoal *1/1" :use ((:instance field-sum-list-of-rm-local
                                 (a (car xs)) (xs ys)))
          :in-theory (disable field-sum-list-of-rm-local)))))
(local (defthm field-sum-list-nil-local
 (equal (field-sum-list nil) (field-zero))
 :hints (("Goal" :expand ((field-sum-list nil))))))

(local
 (defthm xcert-s-residual-left-normal-local
  (equal
   (field-sub
    (field-add
     (field-sub (field-mul q (field-sub xbc xa))
                (field-mul r (field-sub xbc xa)))
     (field-mul p xbc))
    (field-add (field-mul p xab) (field-add yab ybc)))
   (field-sum-list
    (list (field-mul q xbc) (field-neg (field-mul q xa))
          (field-neg (field-mul r xbc)) (field-mul r xa)
          (field-mul p xbc) (field-neg (field-mul p xab))
          (field-neg yab) (field-neg ybc))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable field-sum-list field-sum-list-nil-local field-sub
            field-mul-left-distributive field-mul-right-distributive
            field-mul-of-neg-right-local field-mul-of-neg-left-local
            field-neg-of-add-local field-neg-of-neg field-add-associative
            field-add-commutative field-add-zero-left field-add-zero-right
            field-fix-of-add field-fix-of-mul field-fix-of-neg
            field-fix-of-zero)))))

(local
 (defthm xcert-s-combination-right-normal-local
  (equal
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
           (field-sub xa xc)))))))))
   (field-sum-list
    (list
     (field-mul p xa) (field-neg (field-mul p xa))
     (field-mul p xb) (field-neg (field-mul p xb))
     (field-mul p xc) (field-neg (field-mul p xc))
     (field-mul q xb) (field-neg (field-mul q xb))
     (field-mul q xc) (field-neg (field-mul q xc))
     (field-mul r xb) (field-neg (field-mul r xb))
     (field-mul p xbc) (field-mul q xbc) (field-mul r xa)
     (field-neg (field-mul p xab)) (field-neg (field-mul q xa))
     (field-neg (field-mul r xbc)) (field-neg yab) (field-neg ybc))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance field-sum-list-perm-local
                   (xs (list
     (field-mul p xa) (field-mul p xb) (field-mul p xbc) (field-mul p xc)
     (field-mul q xb) (field-mul q xbc) (field-mul q xc)
     (field-mul r xa) (field-mul r xb)
     (field-neg (field-mul p xa)) (field-neg (field-mul p xab))
     (field-neg (field-mul p xb)) (field-neg (field-mul p xc))
     (field-neg (field-mul q xa)) (field-neg (field-mul q xb))
     (field-neg (field-mul q xc)) (field-neg (field-mul r xb))
     (field-neg (field-mul r xbc)) (field-neg yab) (field-neg ybc))) (ys (list
     (field-mul p xa) (field-neg (field-mul p xa))
     (field-mul p xb) (field-neg (field-mul p xb))
     (field-mul p xc) (field-neg (field-mul p xc))
     (field-mul q xb) (field-neg (field-mul q xb))
     (field-mul q xc) (field-neg (field-mul q xc))
     (field-mul r xb) (field-neg (field-mul r xb))
     (field-mul p xbc) (field-mul q xbc) (field-mul r xa)
     (field-neg (field-mul p xab)) (field-neg (field-mul q xa))
     (field-neg (field-mul r xbc)) (field-neg yab) (field-neg ybc)))))
           :in-theory (enable acl2::perm acl2::rm acl2::memb field-sum-list field-sum-list-nil-local field-sub
            field-mul-left-distributive field-mul-right-distributive
            field-mul-associative field-mul-commutative
            field-mul-of-neg-right-local field-mul-of-neg-left-local
            field-neg-of-add-local field-neg-of-neg field-add-associative
            field-add-commutative field-add-zero-left field-add-zero-right
            field-add-inverse-left field-add-inverse-right
            field-add-inverse-tail-local field-add-cancel-around-local
            field-add-fix-left field-add-fix-right field-fix-of-add
            field-fix-of-mul field-fix-of-neg field-fix-of-zero)))))

(local
 (defthm xcert-s-paired-sum-reduces-local
  (equal
   (field-sum-list
   (list
    (field-mul p xa) (field-neg (field-mul p xa))
    (field-mul p xb) (field-neg (field-mul p xb))
    (field-mul p xc) (field-neg (field-mul p xc))
    (field-mul q xb) (field-neg (field-mul q xb))
    (field-mul q xc) (field-neg (field-mul q xc))
    (field-mul r xb) (field-neg (field-mul r xb))
    (field-mul p xbc) (field-mul q xbc) (field-mul r xa)
    (field-neg (field-mul p xab)) (field-neg (field-mul q xa))
    (field-neg (field-mul r xbc)) (field-neg yab) (field-neg ybc)))
   (field-sum-list
   (list (field-mul q xbc) (field-neg (field-mul q xa))
         (field-neg (field-mul r xbc)) (field-mul r xa)
         (field-mul p xbc) (field-neg (field-mul p xab))
         (field-neg yab) (field-neg ybc))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance field-sum-list-perm-local
                   (xs (list (field-mul p xbc) (field-mul q xbc)
                             (field-mul r xa) (field-neg (field-mul p xab))
                             (field-neg (field-mul q xa))
                             (field-neg (field-mul r xbc))
                             (field-neg yab) (field-neg ybc)))
                   (ys (list (field-mul q xbc) (field-neg (field-mul q xa))
                             (field-neg (field-mul r xbc)) (field-mul r xa)
                             (field-mul p xbc) (field-neg (field-mul p xab))
                             (field-neg yab) (field-neg ybc)))))
           :in-theory
           (e/d (acl2::perm acl2::rm acl2::memb field-sum-list field-sum-list-nil-local
                 field-add-inverse-tail-local field-add-inverse-right
                 field-add-zero-left field-add-zero-right field-add-fix-left
                 field-add-fix-right field-fix-of-add field-fix-of-neg)
                (field-add-swap-local field-add-commutative
                 field-add-associative))))))

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
  :hints (("Goal"
           :use ((:instance xcert-s-residual-left-normal-local)
                 (:instance xcert-s-combination-right-normal-local)
                 (:instance xcert-s-paired-sum-reduces-local))
           :in-theory (theory 'minimal-theory)))))

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
  :hints (("Goal"
           :use ((:instance xcert-s-residual-combination-local))
           :in-theory (union-theories (theory 'minimal-theory)
            '(field-sub-self field-neg-of-zero field-mul-zero-left
              field-mul-zero-right field-add-zero-left field-add-zero-right
              field-fix-of-zero))))))

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

(local
 (defthm xcert-s-zero-product-local
  (implies
   (and
    (equal (field-mul (field-sub p r) (field-add p q))
           (field-sub xa xc))
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
    (field-zero)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance xcert-s-eight-equation-residual-local)
                 (:instance xcert-s-residual-zero-from-h-local))
           :in-theory (theory 'minimal-theory)))))

(defthm xcert-s-scalar-reconstruction
 (implies
  (and
   (equal (field-mul p (field-add yb ya))
    (field-add (field-mul xb xb)
     (field-add (field-mul xb xa) (field-add (field-mul xa xa) curve-a))))
   (equal (field-mul q (field-add yc yab))
    (field-add (field-mul xc xc)
     (field-add (field-mul xc xab) (field-add (field-mul xab xab) curve-a))))
   (equal (field-mul p (field-sub xb xa)) (field-sub yb ya))
   (equal (field-mul q (field-sub xc xab)) (field-sub yc yab))
   (equal (field-mul r (field-sub xc xb)) (field-sub yc yb))
   (equal (field-mul tt (field-sub xbc xa)) (field-sub ybc ya))
   (equal (field-add (field-add xab xa) xb) (field-mul p p))
   (equal (field-add yab ya) (field-mul p (field-sub xa xab)))
   (equal (field-add (field-add xbc xb) xc) (field-mul r r))
   (equal (field-add ybc yb) (field-mul r (field-sub xb xbc)))
   (not (equal (field-sub xc xb) (field-zero)))
   (not (equal (field-sub xbc xa) (field-zero))))
  (equal (field-sub (field-add p q) (field-add r tt))
         (field-zero)))
 :rule-classes nil
 :hints
 (("Goal"
   :use
   ((:instance xcert-h-scalar-reconstruction (a curve-a))
    (:instance xcert-s-zero-product-local)
    (:instance field-mul-left-cancel-forward
     (x (field-sub xbc xa))
     (y (field-sub (field-add p q) (field-add r tt)))
     (z (field-zero))))
   :in-theory
   (union-theories (theory 'minimal-theory)
    '(field-sub field-fix-of-add field-fix-of-neg field-fix-of-zero
      field-mul-zero-right))))
)
