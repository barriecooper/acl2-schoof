(in-package "GFIELD")
(include-book "xcert-h-reconstruction")

; Bounded algebra used only by the staged confluent-H reconstruction.
(local (defthm add-swap-local
 (equal (field-add x (field-add y z)) (field-add y (field-add x z)))
 :hints (("Goal" :use ((:instance field-add-associative (x x)(y y)(z z))
                        (:instance field-add-associative (x y)(y x)(z z))
                        (:instance field-add-commutative (x x)(y y)))
          :in-theory (union-theories (theory 'minimal-theory) '(field-fix-of-add))))))
(local (defthm add-inverse-tail-local
 (equal (field-add x (field-add (field-neg x) y)) (field-fix y))
 :hints (("Goal" :use ((:instance field-add-associative (x x)(y (field-neg x))(z y)))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(field-add-inverse-right field-add-zero-left field-fix-idempotent))))))
(local (defthm add-inverse-shuffle-local
 (equal (field-add x (field-add y (field-add (field-neg x) z)))
        (field-add y (field-fix z)))
 :hints (("Goal" :use ((:instance add-swap-local (x x)(y y)(z (field-add (field-neg x) z)))
                        (:instance add-inverse-tail-local (x x)(y z)))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(add-swap-local add-inverse-tail-local field-add-fix-right))))))
(local (defthm neg-add-local
 (equal (field-neg (field-add x y)) (field-add (field-neg x)(field-neg y)))
 :hints (("Goal" :use ((:instance field-additive-inverse-unique
                         (x (field-add x y))(y (field-add (field-neg x)(field-neg y)))))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(field-add-associative add-inverse-shuffle-local
                         field-add-inverse-right field-add-zero-left field-fix-of-add field-fix-of-neg))))))
(local (defthm mul-neg-right-local
 (equal (field-mul x (field-neg y)) (field-neg (field-mul x y)))
 :hints (("Goal" :use ((:instance field-additive-inverse-unique
                         (x (field-mul x y))(y (field-mul x (field-neg y))))
                        (:instance field-mul-left-distributive (x x)(y y)(z (field-neg y))))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(field-add-inverse-right field-mul-zero-right field-fix-of-mul))))))
(local (defthm mul-neg-left-local
 (equal (field-mul (field-neg x) y) (field-neg (field-mul x y)))
 :hints (("Goal" :use ((:instance field-mul-commutative (x (field-neg x))(y y))
                        (:instance field-mul-commutative (x y)(y x))
                        (:instance mul-neg-right-local (x y)(y x)))
          :in-theory (theory 'minimal-theory)))))
(local (defthm cancel-after-two-local
 (equal (field-add x (field-add y (field-add z (field-add (field-neg x) w))))
        (field-add y (field-add z (field-fix w))))
 :hints (("Goal" :use ((:instance add-swap-local (x x)(y y)(z (field-add z (field-add (field-neg x) w))))
                        (:instance add-swap-local (x x)(y z)(z (field-add (field-neg x) w)))
                        (:instance add-inverse-tail-local (x x)(y w)))
          :in-theory (union-theories (theory 'minimal-theory) '(field-add-associative field-add-fix-right))))))
(local (defthm cancel-at-end-local
 (equal (field-add x (field-add y (field-add z (field-neg x))))
        (field-add y (field-fix z)))
 :hints (("Goal" :use ((:instance field-add-commutative (x z)(y (field-neg x)))
                        (:instance add-inverse-shuffle-local (x x)(y y)(z z)))
          :in-theory (union-theories (theory 'minimal-theory) '(field-fix-of-add field-add-fix-right))))))
(local (defthm cancel-after-three-local
 (equal (field-add x (field-add y (field-add z (field-add v (field-add (field-neg x) w)))))
        (field-add y (field-add z (field-add v (field-fix w)))))
 :hints (("Goal" :use ((:instance add-swap-local
                         (x x)(y y)(z (field-add z (field-add v (field-add (field-neg x) w)))))
                        (:instance cancel-after-two-local (x x)(y z)(z v)(w w)))
          :in-theory (union-theories (theory 'minimal-theory) '(field-add-fix-right))))))

(local (defthm add-three-equalities-local
 (implies (and (equal a aa)(equal b bb)(equal c cc))
  (equal (field-add a (field-add b c)) (field-add aa (field-add bb cc))))
 :hints (("Goal" :in-theory (enable field-add-fixed-congruence)))))

(local (defconst *confluent-algebra-theory*
 '(field-sub field-mul-left-distributive field-mul-right-distributive
   field-mul-associative field-mul-commutative mul-neg-left-local mul-neg-right-local
   neg-add-local field-neg-of-neg field-add-associative field-add-commutative
   add-swap-local add-inverse-tail-local add-inverse-shuffle-local cancel-after-two-local
   cancel-at-end-local cancel-after-three-local field-add-inverse-left field-add-inverse-right field-add-zero-left
   field-add-zero-right field-mul-zero-left field-mul-zero-right field-add-fix-left
   field-add-fix-right field-mul-fix-left field-mul-fix-right field-fix-idempotent
   field-fix-of-add field-fix-of-mul field-fix-of-neg field-fix-of-zero field-fix-of-one)))

; The two ordered line equations and the first output-y equation telescope at B.
(local (defthm confluent-line-left-normal-local
 (equal (field-add (field-mul p (field-sub xb xa))
          (field-add (field-mul q (field-sub xb xp))
                     (field-mul p (field-sub xa xp))))
        (field-mul (field-sub xb xp) (field-add p q)))
 :rule-classes nil :hints (("Goal" :do-not '(preprocess)
  :in-theory (union-theories (theory 'minimal-theory) *confluent-algebra-theory*)))))
(local (defthm confluent-line-right-normal-local
 (equal (field-add (field-sub yb ya)
          (field-add (field-sub yb yp) (field-add yp ya)))
        (field-add yb yb))
 :rule-classes nil :hints (("Goal" :do-not '(preprocess)
  :in-theory (union-theories (theory 'minimal-theory) *confluent-algebra-theory*)))))
(local (defthm confluent-line-telescope-local
 (implies (and (equal (field-mul p (field-sub xb xa)) (field-sub yb ya))
               (equal (field-mul q (field-sub xb xp)) (field-sub yb yp))
               (equal (field-add yp ya) (field-mul p (field-sub xa xp))))
  (equal (field-mul (field-sub xb xp) (field-add p q)) (field-add yb yb)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance add-three-equalities-local
   (a (field-mul p (field-sub xb xa)))(aa (field-sub yb ya))
   (b (field-mul q (field-sub xb xp)))(bb (field-sub yb yp))
   (c (field-mul p (field-sub xa xp)))(cc (field-add yp ya)))
   (:instance confluent-line-left-normal-local)
   (:instance confluent-line-right-normal-local)) :in-theory (theory 'minimal-theory)))))

; Stage 1.
(local (defthm confluent-telescope-transport-shape-local
 (equal (field-mul e (field-mul (field-sub p tangent) l))
        (field-sub (field-mul p (field-mul e l))
                   (field-mul tangent (field-mul e l))))
 :rule-classes nil :hints (("Goal" :do-not '(preprocess)
  :use ((:instance field-mul-associative (x e)(y tangent)(z l))
        (:instance field-mul-associative (x tangent)(y e)(z l))
        (:instance field-mul-associative (x e)(y p)(z l))
        (:instance field-mul-associative (x p)(y e)(z l))
        (:instance field-mul-commutative (x e)(y tangent))
        (:instance field-mul-commutative (x e)(y p)))
  :in-theory (union-theories (theory 'minimal-theory) *confluent-algebra-theory*)))))
(local (defthm confluent-telescope-transport-local
 (implies (equal (field-mul e l) doubled)
  (equal (field-mul e (field-mul (field-sub p tangent) l))
         (field-sub (field-mul p doubled) (field-mul tangent doubled))))
 :rule-classes nil :hints (("Goal" :use ((:instance confluent-telescope-transport-shape-local))
  :in-theory (union-theories (theory 'minimal-theory) '(field-mul-fixed-congruence field-fix-of-mul field-sub))))))

; Stage 2.  The line equation is scaled by p, so the subtracted term
; is p*(p*d); this is the dimensionally correct form yielding the p^2*d term.
(local (defthm confluent-first-line-doubled-ordinate-shape-local
 (equal (field-sub (field-mul p (field-add yb yb))
                   (field-mul p (field-sub yb ya)))
        (field-mul p (field-add yb ya)))
 :rule-classes nil :hints (("Goal" :do-not '(preprocess)
  :in-theory (union-theories (theory 'minimal-theory) *confluent-algebra-theory*)))))
(local (defthm confluent-first-line-doubled-ordinate-local
 (implies (equal (field-mul p (field-sub yb ya))
                 (field-mul p (field-mul p d)))
  (equal (field-sub (field-mul p (field-add yb yb)) (field-mul p (field-mul p d)))
         (field-mul p (field-add yb ya))))
 :rule-classes nil :hints (("Goal" :do-not '(preprocess)
  :use ((:instance confluent-first-line-doubled-ordinate-shape-local
                   (p p) (yb yb) (ya ya)))
  :in-theory (union-theories (theory 'minimal-theory) '(field-sub))))))
(local (defthm confluent-first-line-scaled-local
 (implies (equal (field-mul p d) (field-sub yb ya))
  (equal (field-mul p (field-sub yb ya))
         (field-mul p (field-mul p d))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable field-mul-fixed-congruence)))))

; Stage 3.
(local (defthm confluent-telescope-line-combination-local
 (implies (and (equal (field-mul e l) (field-add yb yb))
               (equal (field-mul p d) (field-sub yb ya)))
  (equal (field-mul e (field-mul (field-sub p tangent) l))
   (field-add (field-sub (field-mul p (field-add yb ya))
                         (field-mul tangent (field-add yb yb)))
              (field-mul p (field-mul p d)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance confluent-telescope-transport-local
                         (doubled (field-add yb yb)))
                        (:instance confluent-first-line-scaled-local)
                        (:instance confluent-first-line-doubled-ordinate-local))
  :in-theory (union-theories (theory 'minimal-theory) *confluent-algebra-theory*)))))

(local (defthm three-square-shape-local
 (equal (field-mul (field-add (field-add (field-one)(field-one))(field-one))
                   (field-mul x x))
        (field-add (field-mul x x)(field-add (field-mul x x)(field-mul x x))))
 :hints (("Goal" :in-theory (enable field-mul-left-distributive field-fix-of-add field-fix-of-mul)))))
; Stage 4.
(local (defthm confluent-secant-minus-tangent-shape-local
 (equal
  (field-sub
   (field-add (field-mul xb xb)
    (field-add (field-mul xb xa) (field-add (field-mul xa xa) a)))
   (field-add
    (field-add (field-mul xb xb)
               (field-add (field-mul xb xb) (field-mul xb xb))) a))
  (field-sub (field-add (field-mul xa xa) (field-mul xa xb))
             (field-add (field-mul xb xb) (field-mul xb xb))))
 :rule-classes nil :hints (("Goal" :do-not '(preprocess)
  :in-theory (union-theories (theory 'minimal-theory) *confluent-algebra-theory*)))))
(local (defthm confluent-secant-minus-tangent-local
 (implies
  (and (equal (field-mul p (field-add yb ya))
        (field-add (field-mul xb xb)(field-add (field-mul xb xa)(field-add (field-mul xa xa) a))))
       (equal (field-mul tangent (field-add yb yb))
        (field-add (field-mul (field-add (field-add (field-one)(field-one))(field-one))
                              (field-mul xb xb)) a)))
  (equal (field-sub (field-mul p (field-add yb ya))(field-mul tangent (field-add yb yb)))
   (field-sub (field-add (field-mul xa xa)(field-mul xa xb))
              (field-add (field-mul xb xb)(field-mul xb xb)))))
 :rule-classes nil :hints (("Goal"
  :use ((:instance three-square-shape-local (x xb))
        (:instance confluent-secant-minus-tangent-shape-local))
  :in-theory (union-theories (theory 'minimal-theory) '(field-sub))))))

; Stage 5, split into substitution and the bounded four-variable polynomial.
(local (defthm confluent-output-x-quadratic-shape-local
 (equal
  (field-add (field-mul (field-add (field-add xp xa) xb) (field-sub xb xa))
   (field-sub (field-add (field-mul xa xa)(field-mul xa xb))
              (field-add (field-mul xb xb)(field-mul xb xb))))
 (field-neg (field-mul (field-sub xb xa)(field-sub xb xp))))
 :rule-classes nil :hints (("Goal" :do-not '(preprocess)
  :use ((:instance cancel-after-three-local
         (x (field-mul xa xa)) (y (field-mul xa xb))
         (z (field-mul xb xb))
         (v (field-mul xb xp))
         (w (field-add (field-neg (field-mul xa xp))
              (field-add (field-neg (field-mul xb xb))
                         (field-neg (field-mul xb xb))))))
        (:instance add-inverse-shuffle-local
         (x (field-mul xb xb)) (y (field-neg (field-mul xa xp)))
         (z (field-neg (field-mul xb xb)))))
  :in-theory (union-theories (theory 'minimal-theory) *confluent-algebra-theory*)))))
(local (defthm confluent-output-x-quadratic-local
 (implies (equal (field-add (field-add xp xa) xb) (field-mul p p))
  (equal
   (field-add (field-mul p (field-mul p (field-sub xb xa)))
    (field-sub (field-add (field-mul xa xa)(field-mul xa xb))
               (field-add (field-mul xb xb)(field-mul xb xb))))
   (field-neg (field-mul (field-sub xb xa)(field-sub xb xp)))))
 :rule-classes nil :hints (("Goal" :use ((:instance confluent-output-x-quadratic-shape-local))
  :in-theory (union-theories (theory 'minimal-theory)
   '(field-mul-associative field-mul-fixed-congruence field-fix-of-mul))))))

; Stage 6.
(local (defthm confluent-one-factor-plus-residual-local
 (implies
  (and (equal (field-mul (field-sub xb xp)
                         (field-mul (field-sub p tangent)(field-add p q)))
              (field-add secant-minus-tangent
                         (field-mul p (field-mul p (field-sub xb xa)))))
       (equal secant-minus-tangent
              (field-sub (field-add (field-mul xa xa)(field-mul xa xb))
                         (field-add (field-mul xb xb)(field-mul xb xb))))
       (equal (field-add (field-mul p (field-mul p (field-sub xb xa)))
                         secant-minus-tangent)
              (field-neg (field-mul (field-sub xb xa)(field-sub xb xp)))))
  (equal (field-mul (field-sub xb xp)
                    (field-add (field-mul (field-sub p tangent)(field-add p q))
                               (field-sub xb xa)))
         (field-zero)))
 :rule-classes nil :hints (("Goal" :do-not '(preprocess)
  :in-theory (union-theories (theory 'minimal-theory) *confluent-algebra-theory*)))))
(local (defthm confluent-inner-factor-orientation-local
 (equal (field-add product (field-sub xb xa))
        (field-sub product (field-sub xa xb)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) *confluent-algebra-theory*)))))

(local (defthm confluent-one-factor-residual-local
 (implies
  (and
   (equal (field-mul p (field-add yb ya))
    (field-add (field-mul xb xb)(field-add (field-mul xb xa)(field-add (field-mul xa xa) a))))
   (equal (field-mul tangent (field-add yb yb))
    (field-add (field-mul (field-add (field-add (field-one)(field-one))(field-one))
                          (field-mul xb xb)) a))
   (equal (field-mul p (field-sub xb xa)) (field-sub yb ya))
   (equal (field-mul q (field-sub xb xp)) (field-sub yb yp))
   (equal (field-add (field-add xp xa) xb) (field-mul p p))
   (equal (field-add yp ya) (field-mul p (field-sub xa xp))))
  (equal (field-mul (field-sub xb xp)
   (field-sub (field-mul (field-sub p tangent)(field-add p q))(field-sub xa xb)))
   (field-zero)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance confluent-line-telescope-local)
   (:instance confluent-telescope-line-combination-local
    (e (field-sub xb xp))(l (field-add p q))(d (field-sub xb xa)))
   (:instance confluent-secant-minus-tangent-local)
   (:instance confluent-output-x-quadratic-local)
   (:instance confluent-one-factor-plus-residual-local
    (secant-minus-tangent
     (field-sub (field-add (field-mul xa xa)(field-mul xa xb))
                (field-add (field-mul xb xb)(field-mul xb xb)))))
   (:instance confluent-inner-factor-orientation-local
    (product (field-mul (field-sub p tangent)(field-add p q)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(field-mul-associative field-fix-of-mul))))))

(defthm xcert-confluent-h-factored-reconstruction
 (implies
  (and
   (equal (field-mul p (field-add yb ya))
    (field-add (field-mul xb xb)(field-add (field-mul xb xa)(field-add (field-mul xa xa) a))))
   (equal (field-mul q (field-add yb yp))
    (field-add (field-mul xb xb)(field-add (field-mul xb xp)(field-add (field-mul xp xp) a))))
   (equal (field-mul tangent (field-add yb yb))
    (field-add (field-mul (field-add (field-add (field-one)(field-one))(field-one))
                          (field-mul xb xb)) a))
   (equal (field-mul p (field-sub xb xa)) (field-sub yb ya))
   (equal (field-mul q (field-sub xb xp)) (field-sub yb yp))
   (equal (field-add (field-add xp xa) xb) (field-mul p p))
   (equal (field-add yp ya) (field-mul p (field-sub xa xp))))
  (equal (field-mul (field-sub xb xa)
   (field-mul (field-sub xb xp)
    (field-sub (field-mul (field-sub p tangent)(field-add p q))(field-sub xa xb))))
   (field-zero)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance confluent-one-factor-residual-local))
  :in-theory (union-theories (theory 'minimal-theory) '(field-mul-zero-right)))))

(local (defthm confluent-cancel-first-local
 (implies (and (not (equal (field-sub xb xa)(field-zero)))
               (equal (field-mul (field-sub xb xa) residual)(field-zero)))
  (equal (field-fix residual)(field-zero)))
 :rule-classes nil :hints (("Goal" :use ((:instance field-mul-left-cancel-forward
  (x (field-sub xb xa))(y residual)(z (field-zero))))
  :in-theory (union-theories (theory 'minimal-theory) '(field-sub field-fix-of-add field-fix-of-neg field-mul-zero-right field-fix-of-zero))))))
(local (defthm confluent-cancel-second-local
 (implies (and (not (equal (field-sub xb xp)(field-zero)))
               (equal (field-fix (field-mul (field-sub xb xp) residual))(field-zero)))
  (equal (field-fix residual)(field-zero)))
 :rule-classes nil :hints (("Goal" :use ((:instance field-mul-left-cancel-forward
  (x (field-sub xb xp))(y residual)(z (field-zero))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(field-sub field-fix-of-add field-fix-of-neg field-fix-of-mul field-mul-zero-right field-fix-of-zero))))))

(defthm xcert-confluent-h-scalar-reconstruction
 (implies
  (and
   (equal (field-mul p (field-add yb ya))
    (field-add (field-mul xb xb)(field-add (field-mul xb xa)(field-add (field-mul xa xa) a))))
   (equal (field-mul q (field-add yb yp))
    (field-add (field-mul xb xb)(field-add (field-mul xb xp)(field-add (field-mul xp xp) a))))
   (equal (field-mul tangent (field-add yb yb))
    (field-add (field-mul (field-add (field-add (field-one)(field-one))(field-one))
                          (field-mul xb xb)) a))
   (equal (field-mul p (field-sub xb xa)) (field-sub yb ya))
   (equal (field-mul q (field-sub xb xp)) (field-sub yb yp))
   (equal (field-add (field-add xp xa) xb) (field-mul p p))
   (equal (field-add yp ya) (field-mul p (field-sub xa xp)))
   (not (equal (field-sub xb xa)(field-zero)))
   (not (equal (field-sub xb xp)(field-zero))))
  (equal (field-mul (field-sub p tangent)(field-add p q))(field-sub xa xb)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance xcert-confluent-h-factored-reconstruction)
  (:instance confluent-cancel-first-local
   (residual (field-mul (field-sub xb xp)
    (field-sub (field-mul (field-sub p tangent)(field-add p q))(field-sub xa xb)))))
  (:instance confluent-cancel-second-local
   (residual (field-sub (field-mul (field-sub p tangent)(field-add p q))(field-sub xa xb))))
  (:instance field-sub-equal-zero-implies-fixed-equal
   (first (field-mul (field-sub p tangent)(field-add p q)))(second (field-sub xa xb))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(field-sub field-fix-of-add field-fix-of-mul field-fix-of-neg)))))
