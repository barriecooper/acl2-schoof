(in-package "GFIELD")

(include-book "affine-same-point-non-opposite-output")

; The elementary additive and multiplicative normalizations in this book are
; proof-local.  They expose no new generic field interface.
(local
 (defthm field-mul-of-neg-right
   (equal (field-mul x (field-neg y))
          (field-neg (field-mul x y)))
   :hints
   (("Goal"
     :use ((:instance field-additive-inverse-unique
                      (x (field-mul x y))
                      (y (field-mul x (field-neg y))))
           (:instance field-mul-left-distributive
                      (x x) (y y) (z (field-neg y))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-add-inverse-right field-mul-zero-right field-fix-of-mul))))))

(local
 (defthm field-add-inverse-middle
   (equal (field-add x (field-add (field-neg x) y))
          (field-fix y))
   :hints
   (("Goal"
     :use ((:instance field-add-associative
                      (x x) (y (field-neg x)) (z y)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-add-inverse-right field-add-zero-left
        field-fix-idempotent))))))

(local
 (defthm field-mul-of-neg-left
   (equal (field-mul (field-neg x) y)
          (field-neg (field-mul x y)))
   :hints
   (("Goal"
     :use ((:instance field-mul-commutative
                      (x (field-neg x)) (y y))
           (:instance field-mul-commutative (x y) (y x)))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-mul-of-neg-right))))))

(local
 (defthm field-add-swap-first-two
   (equal (field-add x (field-add y z))
          (field-add y (field-add x z)))
   :hints
   (("Goal"
     :use ((:instance field-add-associative (x x) (y y) (z z))
           (:instance field-add-associative (x y) (y x) (z z))
           (:instance field-add-commutative (x x) (y y)))
     :in-theory
     (union-theories (theory 'minimal-theory) '(field-fix-of-add))))))

(local
 (defthm field-add-inverse-shuffle
   (equal (field-add x (field-add y (field-add (field-neg x) z)))
          (field-add y (field-fix z)))
   :hints
   (("Goal"
     :use ((:instance field-add-swap-first-two
                      (x x) (y y) (z (field-add (field-neg x) z)))
           (:instance field-add-inverse-middle (x x) (y z)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-add-swap-first-two field-add-inverse-middle
        field-add-fix-right))))))

(local
 (defthm field-neg-of-add
   (equal (field-neg (field-add x y))
          (field-add (field-neg x) (field-neg y)))
   :hints
   (("Goal"
     :use ((:instance field-additive-inverse-unique
                      (x (field-add x y))
                      (y (field-add (field-neg x) (field-neg y)))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-add-associative field-add-inverse-shuffle
        field-add-inverse-right field-add-zero-left field-fix-of-add
        field-fix-of-neg))))))

(local
 (defthm field-add-cancel-separated
   (equal
    (field-add b (field-add c (field-add d (field-add (field-neg b) e))))
    (field-add c (field-add d (field-fix e))))
   :hints
   (("Goal"
     :use ((:instance field-add-swap-first-two
                      (x b) (y c)
                      (z (field-add d (field-add (field-neg b) e))))
           (:instance field-add-inverse-shuffle (x b) (y d) (z e)))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-add-fix-right))))))

(local
 (defthm field-difference-from-sum
   (implies (equal (field-add a b) c)
            (equal (field-sub a b)
                   (field-sub (field-add a a) c)))
   :rule-classes nil
   :hints
   (("Goal" :do-not '(preprocess)
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-neg-of-add field-add-associative
        field-add-commutative field-add-swap-first-two
        field-add-inverse-middle field-add-inverse-shuffle
        field-neg-of-neg field-add-fix-left field-add-fix-right
        field-add-inverse-right field-add-zero-right
        field-fix-of-add field-fix-of-neg))))))

(local
 (defthm field-square-product-move
   (equal (field-mul x (field-mul y y))
          (field-mul y (field-mul y x)))
   :hints
   (("Goal"
     :use ((:instance field-mul-associative (x y) (y y) (z x))
           (:instance field-mul-commutative
                      (x (field-mul y y)) (y x)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-output-y-tangent-consequence
   (implies
    (equal (field-add y3 y)
           (field-mul slope (field-sub x x3)))
    (equal
     (field-mul slope (field-sub y y3))
     (field-sub
      (field-mul slope (field-add y y))
      (field-mul (field-mul slope slope) (field-sub x x3)))))
   :rule-classes nil
   :hints
   (("Goal" :do-not '(preprocess)
     :use
     ((:instance field-mul-fixed-congruence
                 (x1 slope) (x2 slope)
                 (y1 (field-add y3 y))
                 (y2 (field-mul slope (field-sub x x3))))
      (:instance field-difference-from-sum
                 (a (field-mul slope y))
                 (b (field-mul slope y3))
                 (c (field-mul slope
                               (field-mul slope (field-sub x x3))))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-mul-left-distributive field-mul-right-distributive
        field-mul-associative field-mul-commutative field-mul-of-neg-right
        field-square-product-move field-mul-of-neg-left field-neg-of-add
        field-add-associative field-add-commutative field-add-swap-first-two
        field-add-inverse-middle field-add-inverse-shuffle field-fix-of-add
        field-neg-of-neg field-fix-of-mul field-fix-of-neg))))))

(local
 (defthm field-tangent-polynomial-identity
   (equal
    (field-sub
     (field-add
      (field-mul
       (field-add (field-add (field-one) (field-one)) (field-one))
       (field-mul x x))
      a)
     (field-mul
      (field-add x3
                 (field-mul (field-add (field-one) (field-one)) x))
      (field-sub x x3)))
    (field-add
     (field-add (field-mul x3 x3) (field-mul x3 x))
     (field-add (field-mul x x) a)))
   :hints
   (("Goal" :do-not '(preprocess)
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-mul-left-distributive field-mul-right-distributive
        field-mul-associative field-mul-commutative field-mul-of-neg-right
        field-mul-of-neg-left field-neg-of-add field-add-associative
        field-add-commutative field-add-swap-first-two
        field-add-inverse-middle field-add-inverse-shuffle
        field-add-cancel-separated
        field-add-inverse-left field-add-inverse-right
        field-add-zero-left field-add-zero-right field-neg-of-neg
        field-mul-one-left field-mul-fix-left field-mul-fix-right
        field-fix-of-add field-fix-of-mul
        field-fix-of-neg))))))

(local
 (defthm field-tangent-substitution
   (implies
    (and
     (equal numerator
            (field-add
             (field-mul
              (field-add (field-add (field-one) (field-one)) (field-one))
              (field-mul x x))
             a))
     (equal square
            (field-add x3
                       (field-mul (field-add (field-one) (field-one)) x))))
    (equal
     (field-sub numerator (field-mul square (field-sub x x3)))
     (field-add
      (field-add (field-mul x3 x3) (field-mul x3 x))
      (field-add (field-mul x x) a))))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance field-tangent-polynomial-identity)
      (:instance field-mul-fixed-congruence
                 (x1 square)
                 (x2 (field-add x3
                                (field-mul
                                 (field-add (field-one) (field-one)) x)))
                 (y1 (field-sub x x3)) (y2 (field-sub x x3))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-add-fixed-congruence field-fix-of-add
        field-fix-of-mul field-fix-of-neg))))))

(local
 (defthm field-tangent-final-algebra
   (implies
    (and
     (equal (field-mul slope (field-add y y))
            (field-add
             (field-mul
              (field-add (field-add (field-one) (field-one)) (field-one))
              (field-mul x x))
             a))
     (equal (field-add x3
                       (field-mul (field-add (field-one) (field-one)) x))
            (field-mul slope slope))
     (equal (field-add y3 y)
            (field-mul slope (field-sub x x3))))
    (equal
     (field-mul slope (field-sub y y3))
     (field-add
      (field-add (field-mul x3 x3) (field-mul x3 x))
      (field-add (field-mul x x) a))))
   :rule-classes nil
   :hints
   (("Goal"
     :do-not '(preprocess)
     :use
     ((:instance field-output-y-tangent-consequence)
      (:instance field-tangent-substitution
                 (numerator (field-mul slope (field-add y y)))
                 (square (field-mul slope slope))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-mul-left-distributive field-mul-right-distributive
        field-mul-associative field-mul-commutative field-mul-of-neg-right
        field-mul-of-neg-left field-neg-of-add field-add-associative
        field-add-commutative field-add-swap-first-two
        field-add-inverse-middle field-add-inverse-shuffle
        field-add-inverse-left field-add-inverse-right
        field-add-zero-left field-add-zero-right field-neg-of-neg
        field-fix-of-add field-fix-of-mul field-fix-of-neg))))))

(defthm affine-same-point-non-opposite-tangent-identity
  (implies
   (equal (affine-pair-classify first second)
          :same-point-non-opposite)
   (equal
    (field-mul
     (affine-same-point-non-opposite-slope first)
     (field-sub
      (affine-coordinates-y first)
      (affine-same-point-non-opposite-output-y first)))
    (field-add
     (field-add
      (field-mul
       (affine-same-point-non-opposite-output-x first)
       (affine-same-point-non-opposite-output-x first))
      (field-mul
       (affine-same-point-non-opposite-output-x first)
       (affine-coordinates-x first)))
     (field-add
      (field-mul (affine-coordinates-x first)
                 (affine-coordinates-x first))
      (field-fix (short-weierstrass-a))))))
  :rule-classes nil
  :hints
  (("Goal"
    :do-not '(preprocess)
    :use
    (affine-same-point-non-opposite-slope-reconstructs-tangent-numerator
     affine-same-point-non-opposite-output-x-rearrangement
     affine-same-point-non-opposite-output-y-rearrangement
     (:instance
      field-tangent-final-algebra
      (slope (affine-same-point-non-opposite-slope first))
      (x (affine-coordinates-x first))
      (y (affine-coordinates-y first))
      (x3 (affine-same-point-non-opposite-output-x first))
      (y3 (affine-same-point-non-opposite-output-y first))
      (a (field-fix (short-weierstrass-a)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(field-fix-of-add field-fix-of-mul)))))
