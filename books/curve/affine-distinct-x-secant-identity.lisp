(in-package "GFIELD")

(include-book "affine-distinct-x-output")

; These elementary factorizations are kept proof-local: their only current
; consumer is the secant calculation below.
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
      '(field-mul-left-distributive
        field-add-inverse-right
        field-mul-zero-right
        field-fix-of-mul))))))

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
      '(field-add-inverse-right
        field-add-zero-left
        field-fix-idempotent))))))

(local
 (defthm field-mul-of-neg-left
   (equal (field-mul (field-neg x) y)
          (field-neg (field-mul x y)))
   :hints
   (("Goal"
     :use ((:instance field-mul-commutative
                      (x (field-neg x)) (y y))
           (:instance field-mul-commutative
                      (x y) (y x)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
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
     (union-theories
      (theory 'minimal-theory)
      '(field-fix-of-add))))))

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
      '(field-add-swap-first-two
        field-add-inverse-middle
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
      '(field-add-associative
        field-add-inverse-shuffle
        field-add-inverse-right
        field-add-zero-left
        field-fix-of-add
        field-fix-of-neg))))))

(local
 (defthm field-difference-of-squares
   (equal (field-sub (field-mul x x) (field-mul y y))
          (field-mul (field-sub x y) (field-add x y)))
   :hints
   (("Goal"
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub
        field-mul-left-distributive
        field-mul-right-distributive
        field-mul-associative
        field-mul-commutative
        field-mul-of-neg-right
        field-mul-of-neg-left
        field-neg-of-add
        field-add-associative
        field-add-commutative
        field-add-swap-first-two
        field-add-inverse-middle
        field-add-inverse-shuffle
        field-add-inverse-left
        field-add-inverse-right
        field-add-zero-left
        field-add-zero-right
        field-fix-of-add
        field-fix-of-mul
        field-fix-of-neg))))))

(local
 (defthm field-cubic-cross-term-one
   (equal (field-mul y (field-mul x x))
          (field-mul x (field-mul x y)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-mul-associative (x y) (y x) (z x))
           (:instance field-mul-associative (x x) (y y) (z x))
           (:instance field-mul-commutative (x y) (y x)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-cubic-cross-term-two
   (equal (field-mul y (field-mul x y))
          (field-mul x (field-mul y y)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-mul-associative (x y) (y x) (z y))
           (:instance field-mul-associative (x x) (y y) (z y))
           (:instance field-mul-commutative (x y) (y x)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-difference-of-cubes
   (equal
    (field-sub (field-mul (field-mul x x) x)
               (field-mul (field-mul y y) y))
    (field-mul
     (field-sub x y)
     (field-add (field-mul x x)
                (field-add (field-mul x y)
                           (field-mul y y)))))
   :hints
   (("Goal"
     :do-not '(preprocess)
     :use ((:instance field-cubic-cross-term-one (x x) (y y))
           (:instance field-cubic-cross-term-two (x x) (y y)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub
        field-mul-left-distributive
        field-mul-right-distributive
        field-mul-associative
        field-mul-commutative
        field-mul-of-neg-right
        field-mul-of-neg-left
        field-neg-of-add
        field-add-associative
        field-add-commutative
        field-add-inverse-middle
        field-add-inverse-shuffle
        field-add-inverse-left
        field-add-inverse-right
        field-add-zero-left
        field-add-zero-right
        field-fix-of-add
        field-fix-of-mul
        field-fix-of-neg))))))

; Cancelling the nonzero secant denominator from the difference of the two
; input curve equations gives the quadratic quotient of the cubic difference.
(local
 (defthm field-add-cancel-separated
   (equal
    (field-add b (field-add c (field-add d (field-add (field-neg b) e))))
    (field-add c (field-add d (field-fix e))))
   :hints
   (("Goal"
     :use
     ((:instance field-add-swap-first-two
                 (x b) (y c)
                 (z (field-add d (field-add (field-neg b) e))))
      (:instance field-add-inverse-shuffle
                 (x b) (y d) (z e)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-add-fix-right))))))

(local
 (defthm field-subtract-common-leading
   (equal
    (field-sub (field-add b (field-add a2 c2))
               (field-add b (field-add a1 c1)))
    (field-add c2
               (field-add a2
                          (field-add (field-neg a1) (field-neg c1)))))
   :hints
   (("Goal"
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub
        field-neg-of-add
        field-add-associative
        field-add-swap-first-two
        field-add-inverse-shuffle
        field-add-cancel-separated
        field-fix-of-add
        field-fix-of-neg))))))

(local
 (defthm affine-curve-equations-difference
   (implies
    (and (short-weierstrass-affine-point-p first)
         (short-weierstrass-affine-point-p second))
    (equal
     (field-sub
      (field-mul (affine-coordinates-y second)
                 (affine-coordinates-y second))
      (field-mul (affine-coordinates-y first)
                 (affine-coordinates-y first)))
     (field-add
      (field-sub
       (field-mul
        (field-mul (affine-coordinates-x second)
                   (affine-coordinates-x second))
        (affine-coordinates-x second))
       (field-mul
        (field-mul (affine-coordinates-x first)
                   (affine-coordinates-x first))
        (affine-coordinates-x first)))
      (field-mul
       (field-fix (short-weierstrass-a))
       (field-sub (affine-coordinates-x second)
                  (affine-coordinates-x first))))))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance field-subtract-common-leading
                 (b (field-fix (short-weierstrass-b)))
                 (a2 (field-mul (field-fix (short-weierstrass-a))
                                (affine-coordinates-x second)))
                 (c2 (field-mul
                      (field-mul (affine-coordinates-x second)
                                 (affine-coordinates-x second))
                      (affine-coordinates-x second)))
                 (a1 (field-mul (field-fix (short-weierstrass-a))
                                (affine-coordinates-x first)))
                 (c1 (field-mul
                      (field-mul (affine-coordinates-x first)
                                 (affine-coordinates-x first))
                      (affine-coordinates-x first)))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(short-weierstrass-affine-point-p
        short-weierstrass-equation-p
        short-weierstrass-rhs
        field-sub
        field-add-associative
        field-add-commutative
        field-add-inverse-middle
        field-add-inverse-shuffle
        field-mul-left-distributive
        field-mul-right-distributive
        field-mul-of-neg-right
        field-mul-of-neg-left
        field-neg-of-add
        field-element-p-of-affine-coordinates-x
        field-element-p-of-affine-coordinates-y
        field-fix-when-field-element-p
        field-fix-of-add
        field-fix-of-mul
        field-fix-of-neg))))))

(local
 (defthm field-factor-cubic-and-linear
   (equal
    (field-add
     (field-sub (field-mul (field-mul x2 x2) x2)
                (field-mul (field-mul x1 x1) x1))
     (field-mul a (field-sub x2 x1)))
    (field-mul
     (field-sub x2 x1)
     (field-add (field-mul x2 x2)
                (field-add (field-mul x2 x1)
                           (field-add (field-mul x1 x1) a)))))
   :hints
   (("Goal"
     :use ((:instance field-difference-of-cubes (x x2) (y x1)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-mul-left-distributive
        field-mul-right-distributive
        field-mul-associative
        field-mul-commutative
        field-add-associative
        field-add-commutative
        field-add-swap-first-two
        field-fix-of-add
        field-fix-of-mul))))))

(local
 (defthm field-reconstructed-slope-times-y-sum
   (implies
    (equal (field-mul slope (field-sub x2 x1))
           (field-sub y2 y1))
    (equal
     (field-mul (field-sub x2 x1)
                (field-mul slope (field-add y2 y1)))
     (field-sub (field-mul y2 y2) (field-mul y1 y1))))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-difference-of-squares (x y2) (y y1))
           (:instance field-mul-associative
                      (x (field-sub x2 x1))
                      (y slope)
                      (z (field-add y2 y1)))
           (:instance field-mul-commutative
                      (x (field-sub x2 x1)) (y slope)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-mul-fix-left
        field-mul-fix-right
        field-fix-of-mul))))))

(local
 (defthm affine-distinct-x-input-secant-identity-before-cancel
   (implies
    (and (short-weierstrass-affine-point-p first)
         (short-weierstrass-affine-point-p second)
         (equal (affine-pair-classify first second) :distinct-x))
    (equal
     (field-mul
      (field-sub (affine-coordinates-x second)
                 (affine-coordinates-x first))
      (field-mul
       (affine-distinct-x-slope first second)
       (field-add (affine-coordinates-y second)
                  (affine-coordinates-y first))))
     (field-mul
      (field-sub (affine-coordinates-x second)
                 (affine-coordinates-x first))
      (field-add
       (field-mul (affine-coordinates-x second)
                  (affine-coordinates-x second))
       (field-add
        (field-mul (affine-coordinates-x second)
                   (affine-coordinates-x first))
        (field-add
         (field-mul (affine-coordinates-x first)
                    (affine-coordinates-x first))
         (field-fix (short-weierstrass-a))))))))
   :rule-classes nil
   :hints
   (("Goal"
     :do-not '(preprocess)
     :use
     (affine-curve-equations-difference
      affine-distinct-x-slope-reconstructs-y-difference
      (:instance field-reconstructed-slope-times-y-sum
                 (slope (affine-distinct-x-slope first second))
                 (x2 (affine-coordinates-x second))
                 (x1 (affine-coordinates-x first))
                 (y2 (affine-coordinates-y second))
                 (y1 (affine-coordinates-y first)))
      (:instance field-difference-of-squares
                 (x (affine-coordinates-y second))
                 (y (affine-coordinates-y first)))
      (:instance field-difference-of-cubes
                 (x (affine-coordinates-x second))
                 (y (affine-coordinates-x first)))
      (:instance field-factor-cubic-and-linear
                 (x2 (affine-coordinates-x second))
                 (x1 (affine-coordinates-x first))
                 (a (field-fix (short-weierstrass-a))))
      (:instance field-mul-left-distributive
                 (x (field-sub (affine-coordinates-x second)
                               (affine-coordinates-x first)))
                 (y (field-mul (affine-coordinates-x second)
                               (affine-coordinates-x second)))
                 (z (field-add
                     (field-mul (affine-coordinates-x second)
                                (affine-coordinates-x first))
                     (field-add
                      (field-mul (affine-coordinates-x first)
                                 (affine-coordinates-x first))
                      (field-fix (short-weierstrass-a)))))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub
        field-mul-left-distributive
        field-mul-right-distributive
        field-mul-associative
        field-mul-commutative
        field-mul-of-neg-right
        field-mul-of-neg-left
        field-neg-of-add
        field-add-associative
        field-add-commutative
        field-add-inverse-middle
        field-add-inverse-shuffle
        field-add-cancel-separated
        field-element-p-of-affine-coordinates-x
        field-element-p-of-affine-coordinates-y
        field-element-p-of-affine-distinct-x-slope
        field-fix-when-field-element-p
        field-fix-of-add
        field-fix-of-mul
        field-fix-of-neg))))))

(defthm affine-distinct-x-input-secant-identity
   (implies
    (and (short-weierstrass-affine-point-p first)
         (short-weierstrass-affine-point-p second)
         (equal (affine-pair-classify first second) :distinct-x))
    (equal
     (field-mul
      (affine-distinct-x-slope first second)
      (field-add (affine-coordinates-y second)
                 (affine-coordinates-y first)))
     (field-add
      (field-mul (affine-coordinates-x second)
                 (affine-coordinates-x second))
      (field-add
       (field-mul (affine-coordinates-x second)
                  (affine-coordinates-x first))
       (field-add
        (field-mul (affine-coordinates-x first)
                   (affine-coordinates-x first))
        (field-fix (short-weierstrass-a)))))))
   :rule-classes nil
   :hints
   (("Goal"
     :do-not '(preprocess)
     :use
     (affine-distinct-x-input-secant-identity-before-cancel
      affine-pair-classify-distinct-x-implies-x-difference-nonzero
      (:instance
       field-mul-left-cancel-forward
       (x (field-sub (affine-coordinates-x second)
                     (affine-coordinates-x first)))
       (y (field-mul
           (affine-distinct-x-slope first second)
           (field-add (affine-coordinates-y second)
                      (affine-coordinates-y first))))
       (z (field-add
           (field-mul (affine-coordinates-x second)
                      (affine-coordinates-x second))
           (field-add
            (field-mul (affine-coordinates-x second)
                       (affine-coordinates-x first))
            (field-add
             (field-mul (affine-coordinates-x first)
                        (affine-coordinates-x first))
             (field-fix (short-weierstrass-a))))))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub
        field-element-p-of-affine-coordinates-x
        field-element-p-of-affine-coordinates-y
        field-element-p-of-affine-distinct-x-slope
        field-fix-when-field-element-p
        field-fix-of-add
        field-fix-of-mul)))))

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
        field-add-cancel-separated field-neg-of-neg
        field-add-fix-left field-add-fix-right
        field-add-inverse-right field-add-zero-right
        field-fix-of-add field-fix-of-neg))))))

(local
 (defthm field-double-from-difference
   (implies (equal (field-sub b a) c)
            (equal (field-add a a)
                   (field-sub (field-add b a) c)))
   :rule-classes nil
   :hints
   (("Goal" :do-not '(preprocess)
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-neg-of-add field-add-associative
        field-add-commutative field-add-swap-first-two
        field-add-inverse-middle field-add-inverse-shuffle
        field-add-cancel-separated field-neg-of-neg
        field-add-fix-left field-add-fix-right
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
 (defthm field-output-y-secant-consequence
   (implies
    (equal (field-add y3 y1)
           (field-mul slope (field-sub x1 x3)))
    (equal
     (field-mul slope (field-sub y1 y3))
     (field-sub
      (field-mul slope (field-add y1 y1))
      (field-mul (field-mul slope slope) (field-sub x1 x3)))))
   :hints
   (("Goal" :do-not '(preprocess)
     :use
     ((:instance field-mul-fixed-congruence
                 (x1 slope) (x2 slope)
                 (y1 (field-add y3 y1))
                 (y2 (field-mul slope (field-sub x1 x3))))
      (:instance field-difference-from-sum
                 (a (field-mul slope y1))
                 (b (field-mul slope y3))
                 (c (field-mul slope
                               (field-mul slope (field-sub x1 x3))))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-mul-left-distributive field-mul-right-distributive
        field-mul-associative field-mul-commutative field-mul-of-neg-right
        field-square-product-move
        field-mul-of-neg-left field-neg-of-add field-add-associative
        field-add-commutative field-add-swap-first-two field-add-inverse-middle
        field-add-inverse-shuffle field-add-cancel-separated field-fix-of-add
        field-neg-of-neg field-fix-of-mul field-fix-of-neg))))))

(local
 (defthm field-slope-reconstruction-consequence
   (implies
    (equal (field-mul slope (field-sub x2 x1))
           (field-sub y2 y1))
    (equal
     (field-mul slope (field-add y1 y1))
     (field-sub
      (field-mul slope (field-add y2 y1))
      (field-mul (field-mul slope slope) (field-sub x2 x1)))))
   :hints
   (("Goal" :do-not '(preprocess)
     :use
     ((:instance field-mul-fixed-congruence
                 (x1 slope) (x2 slope)
                 (y1 (field-mul slope (field-sub x2 x1)))
                 (y2 (field-sub y2 y1)))
      (:instance field-double-from-difference
                 (a (field-mul slope y1))
                 (b (field-mul slope y2))
                 (c (field-mul (field-mul slope slope)
                               (field-sub x2 x1)))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-mul-left-distributive field-mul-right-distributive
        field-mul-associative field-mul-commutative field-mul-of-neg-right
        field-square-product-move
        field-mul-of-neg-left field-neg-of-add field-add-associative
        field-add-commutative field-add-swap-first-two field-add-inverse-middle
        field-add-inverse-shuffle field-add-cancel-separated field-fix-of-add
        field-neg-of-neg field-fix-of-mul field-fix-of-neg))))))

(local
 (defthm field-output-x-product-left
   (implies (equal (field-add x1 (field-add x2 x3)) square)
            (equal (field-mul x3 square)
                   (field-mul x3 (field-add x1 (field-add x2 x3)))))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-mul-fixed-congruence
                      (x1 x3) (x2 x3)
                      (y1 square)
                      (y2 (field-add x1 (field-add x2 x3)))))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-fix-of-add field-fix-of-mul))))))

(local
 (defthm field-output-x-product-right
   (implies (equal (field-add x1 (field-add x2 x3)) square)
            (equal (field-mul x2 square)
                   (field-mul x2 (field-add x1 (field-add x2 x3)))))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-mul-fixed-congruence
                      (x1 x2) (x2 x2)
                      (y1 square)
                      (y2 (field-add x1 (field-add x2 x3)))))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-fix-of-add field-fix-of-mul))))))

(local
 (defthm field-add-inverse-shuffle-end
   (equal (field-add x (field-add y (field-neg x)))
          (field-fix y))
   :hints
   (("Goal"
     :use ((:instance field-add-inverse-shuffle
                      (x x) (y y) (z (field-zero))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-add-zero-right field-add-fix-right
        field-fix-idempotent))))))

(local
 (defthm field-output-x-core-consequence
   (implies
    (equal (field-add x1 (field-add x2 x3)) square)
    (equal
     (field-add
      (field-mul x1 x2)
      (field-add
       (field-mul x2 x2)
       (field-sub (field-mul x3 square) (field-mul x2 square))))
     (field-add (field-mul x1 x3) (field-mul x3 x3))))
   :rule-classes nil
   :hints
   (("Goal" :do-not '(preprocess)
     :use ((:instance field-output-x-product-left)
           (:instance field-output-x-product-right))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-mul-left-distributive field-mul-right-distributive
        field-mul-associative field-mul-commutative field-mul-of-neg-right
        field-mul-of-neg-left field-neg-of-add field-add-associative
        field-add-commutative field-add-swap-first-two field-add-inverse-middle
        field-add-inverse-shuffle field-add-inverse-shuffle-end
        field-add-cancel-separated
        field-add-inverse-right field-add-zero-right field-neg-of-neg
        field-fix-of-add field-fix-of-mul field-fix-of-neg))))))

(local
 (defthm field-output-x-final-consequence
   (implies
    (equal (field-add (field-add x3 x1) x2)
           (field-mul slope slope))
    (equal
     (field-sub
      (field-sub
       (field-add (field-mul x2 x2)
                  (field-add (field-mul x2 x1)
                             (field-add (field-mul x1 x1) a)))
       (field-mul (field-mul slope slope) (field-sub x2 x1)))
      (field-mul (field-mul slope slope) (field-sub x1 x3)))
     (field-add
      (field-add (field-mul x3 x3) (field-mul x3 x1))
      (field-add (field-mul x1 x1) a))))
   :hints
   (("Goal" :do-not '(preprocess)
     :use
     ((:instance field-mul-fixed-congruence
                 (x1 x3) (x2 x3)
                 (y1 (field-mul slope slope))
                 (y2 (field-add (field-add x3 x1) x2)))
      (:instance field-mul-fixed-congruence
                 (x1 x2) (x2 x2)
                 (y1 (field-mul slope slope))
                 (y2 (field-add (field-add x3 x1) x2)))
      (:instance field-output-x-product-left
                 (square (field-mul slope slope)))
      (:instance field-output-x-product-right
                 (square (field-mul slope slope)))
      (:instance field-output-x-core-consequence
                 (square (field-mul slope slope))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-mul-left-distributive field-mul-right-distributive
        field-mul-associative field-mul-commutative field-mul-of-neg-right
        field-mul-of-neg-left field-neg-of-add field-add-associative
        field-add-commutative field-add-swap-first-two field-add-inverse-middle
        field-add-inverse-shuffle field-add-cancel-separated field-fix-of-add
        field-neg-of-neg field-fix-of-mul field-fix-of-neg))))))

(local
 (defthm field-secant-final-algebra
   (implies
    (and
     (equal (field-mul slope (field-add y2 y1))
            (field-add (field-mul x2 x2)
                       (field-add (field-mul x2 x1)
                                  (field-add (field-mul x1 x1) a))))
     (equal (field-add (field-add x3 x1) x2)
            (field-mul slope slope))
     (equal (field-add y3 y1)
            (field-mul slope (field-sub x1 x3)))
     (equal (field-mul slope (field-sub x2 x1))
            (field-sub y2 y1)))
    (equal
     (field-mul slope (field-sub y1 y3))
     (field-add
      (field-add (field-mul x3 x3) (field-mul x3 x1))
      (field-add (field-mul x1 x1) a))))
   :rule-classes nil
   :hints
   (("Goal"
     :do-not '(preprocess)
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-output-y-secant-consequence
        field-slope-reconstruction-consequence
        field-output-x-final-consequence
        field-fix-of-add field-fix-of-mul))))))

(defthm affine-distinct-x-secant-identity
  (implies
   (and (short-weierstrass-affine-point-p first)
        (short-weierstrass-affine-point-p second)
        (equal (affine-pair-classify first second) :distinct-x))
   (equal
    (field-mul
     (affine-distinct-x-slope first second)
     (field-sub
      (affine-coordinates-y first)
      (affine-distinct-x-output-y first second)))
    (field-add
     (field-add
      (field-mul
       (affine-distinct-x-output-x first second)
       (affine-distinct-x-output-x first second))
      (field-mul
       (affine-distinct-x-output-x first second)
       (affine-coordinates-x first)))
     (field-add
      (field-mul
       (affine-coordinates-x first)
       (affine-coordinates-x first))
      (field-fix (short-weierstrass-a))))))
  :rule-classes nil
  :hints
  (("Goal"
    :do-not '(preprocess)
    :use
    (affine-distinct-x-input-secant-identity
     affine-distinct-x-slope-reconstructs-y-difference
     affine-distinct-x-output-x-rearrangement
     affine-distinct-x-output-y-rearrangement
     (:instance
      field-secant-final-algebra
      (slope (affine-distinct-x-slope first second))
      (x1 (affine-coordinates-x first))
      (y1 (affine-coordinates-y first))
      (x2 (affine-coordinates-x second))
      (y2 (affine-coordinates-y second))
      (x3 (affine-distinct-x-output-x first second))
      (y3 (affine-distinct-x-output-y first second))
      (a (field-fix (short-weierstrass-a)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(field-sub
       field-mul-left-distributive
       field-mul-right-distributive
       field-mul-associative
       field-mul-commutative
       field-mul-of-neg-right
       field-mul-of-neg-left
       field-neg-of-add
       field-add-associative
       field-add-commutative
       field-add-inverse-middle
       field-add-inverse-left
       field-add-inverse-right
       field-add-zero-left
       field-add-zero-right
       field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-coordinates-y
       field-element-p-of-affine-distinct-x-slope
       field-element-p-of-affine-distinct-x-output-x
       field-element-p-of-affine-distinct-x-output-y
       field-element-p-of-add
       field-element-p-of-mul
       field-element-p-of-neg
       field-fix-when-field-element-p
       field-fix-idempotent
       field-fix-of-add
       field-fix-of-mul
       field-fix-of-neg)))))
