(in-package "GFIELD")

(include-book "affine-same-point-non-opposite-tangent-identity")

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
      '(field-mul-left-distributive field-add-inverse-right
        field-mul-zero-right field-fix-of-mul))))))

(local
 (defthm field-add-inverse-middle
   (equal (field-add x (field-add (field-neg x) y))
          (field-fix y))
   :hints
   (("Goal"
     :use ((:instance field-add-associative
                      (x x) (y (field-neg x)) (z y)))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-add-inverse-right field-add-zero-left
                       field-fix-idempotent))))))

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
     (union-theories (theory 'minimal-theory)
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
 (defthm field-mul-of-neg-left
   (equal (field-mul (field-neg x) y)
          (field-neg (field-mul x y)))
   :hints
   (("Goal"
     :use ((:instance field-mul-commutative
                      (x (field-neg x)) (y y))
           (:instance field-mul-commutative
                      (x y) (y x))
           (:instance field-mul-of-neg-right (x y) (y x)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-difference-of-squares
   (equal (field-sub (field-mul y1 y1) (field-mul y3 y3))
          (field-mul (field-sub y1 y3) (field-add y1 y3)))
   :hints
   (("Goal"
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-mul-left-distributive field-mul-right-distributive
        field-mul-associative field-mul-commutative field-mul-of-neg-right
        field-mul-of-neg-left field-neg-of-add field-add-associative
        field-add-commutative field-add-swap-first-two
        field-add-inverse-middle field-add-inverse-shuffle
        field-add-inverse-left field-add-inverse-right field-add-zero-left
        field-add-zero-right field-fix-of-add field-fix-of-mul
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
 (defthm field-same-point-non-opposite-cubic-factor
   (equal
    (field-mul
     (field-add (field-add (field-mul x3 x3) (field-mul x3 x1))
                (field-add (field-mul x1 x1) a))
     (field-sub x1 x3))
    (field-add
     (field-sub
      (field-mul (field-mul x1 x1) x1)
      (field-mul (field-mul x3 x3) x3))
     (field-mul a (field-sub x1 x3))))
   :hints
   (("Goal"
     :do-not '(preprocess)
     :use ((:instance field-cubic-cross-term-one (x x3) (y x1))
           (:instance field-cubic-cross-term-one (x x1) (y x3)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-mul-left-distributive field-mul-right-distributive
        field-mul-associative field-mul-commutative field-mul-of-neg-right
        field-mul-of-neg-left field-add-associative field-add-commutative
        field-add-swap-first-two
        field-add-inverse-middle field-add-inverse-shuffle
        field-fix-of-add field-fix-of-mul
        field-fix-of-neg))))))

(local
 (defthm field-tangent-square-difference
   (implies
    (and (equal (field-mul slope (field-sub y1 y3)) quadratic)
         (equal (field-add y1 y3)
                (field-mul slope (field-sub x1 x3))))
    (equal (field-sub (field-mul y1 y1) (field-mul y3 y3))
           (field-mul quadratic (field-sub x1 x3))))
   :rule-classes nil
   :hints
   (("Goal"
     :do-not '(preprocess)
     :use ((:instance field-difference-of-squares)
           (:instance field-mul-associative
                      (x (field-sub y1 y3)) (y slope)
                      (z (field-sub x1 x3))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-mul-associative field-mul-commutative field-fix-of-add
        field-fix-of-mul field-fix-of-neg))))))

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
           (:instance field-add-inverse-shuffle
                      (x b) (y d) (z e)))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-add-fix-right))))))

(local
 (defthm field-additive-finish-shape
   (equal (field-add a (field-add b (field-add x (field-neg y))))
          (field-add (field-add a x) (field-add b (field-neg y))))
   :hints
   (("Goal"
     :use ((:instance field-add-swap-first-two
                      (x b) (y x) (z (field-neg y)))
           (:instance field-add-associative
                      (x a) (y x) (z (field-add b (field-neg y)))))
     :in-theory
     (union-theories (theory 'minimal-theory) '(field-fix-of-add))))))

(local
 (defthm field-add-pair-with-negatives
   (equal (field-add (field-add a x)
                     (field-add (field-neg a) (field-neg x)))
          (field-zero))
   :hints
   (("Goal"
     :use ((:instance field-add-inverse-right (x (field-add a x)))
           (:instance field-neg-of-add (x a) (y x)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-additive-finish-zero
   (implies
    (equal (field-add b (field-neg y))
           (field-add (field-neg a) (field-neg x)))
    (equal (field-add a (field-add b (field-add x (field-neg y))))
           (field-zero)))
   :rule-classes nil
   :hints
   (("Goal"
     :do-not '(preprocess)
     :use ((:instance field-add-swap-first-two
                      (x b) (y x) (z (field-neg y)))
           (:instance field-additive-finish-shape)
           (:instance field-add-pair-with-negatives)
           (:instance field-add-fixed-congruence
                      (x1 (field-add a x)) (x2 (field-add a x))
                      (y1 (field-add b (field-neg y)))
                      (y2 (field-add (field-neg a) (field-neg x)))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-add-associative field-add-commutative field-add-swap-first-two
        field-add-inverse-middle field-add-inverse-shuffle
        field-add-cancel-separated field-add-inverse-left
        field-add-inverse-right field-add-zero-left field-add-zero-right
        field-fix-idempotent field-fix-of-add field-fix-of-neg))))))

(local
 (defthm field-curve-equation-from-difference
   (implies
    (and (equal (field-sub y1-square y3-square)
                (field-add (field-sub x1-cube x3-cube)
                           (field-sub ax1 ax3)))
         (equal y1-square (field-add x1-cube (field-add ax1 b))))
    (equal (field-sub y3-square
                      (field-add x3-cube (field-add ax3 b)))
           (field-zero)))
   :rule-classes nil
   :hints
   (("Goal"
     :do-not '(preprocess)
     :use ((:instance field-add-swap-first-two
                      (x b) (y x1-cube) (z (field-neg y3-square)))
           (:instance field-add-left-cancel-forward
                      (x x1-cube)
                      (y (field-add b (field-neg y3-square)))
                      (z (field-add (field-neg ax3)
                                    (field-neg x3-cube))))
           (:instance field-additive-inverse-unique
                      (x (field-add x3-cube (field-add ax3 b)))
                      (y (field-neg y3-square)))
           (:instance field-additive-finish-zero
                      (a ax3) (x x3-cube) (y y3-square)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-neg-of-add field-add-associative
        field-add-commutative field-add-swap-first-two
        field-add-inverse-middle field-add-inverse-shuffle
        field-add-cancel-separated
        field-add-left-cancel field-add-left-cancel-forward
        field-add-inverse-left field-add-inverse-right
        field-add-zero-left field-add-zero-right field-neg-of-neg
        field-fix-idempotent field-fix-of-add field-fix-of-neg))))))

(local
 (defthm field-same-point-non-opposite-closure-algebra
   (implies
    (and
     (equal (field-mul slope (field-sub y1 y3))
            (field-add (field-add (field-mul x3 x3) (field-mul x3 x1))
                       (field-add (field-mul x1 x1) a)))
     (equal (field-add y1 y3)
            (field-mul slope (field-sub x1 x3)))
     (equal (field-mul y1 y1)
            (field-add (field-mul (field-mul x1 x1) x1)
                       (field-add (field-mul a x1) b))))
    (equal (field-mul y3 y3)
           (field-add (field-mul (field-mul x3 x3) x3)
                      (field-add (field-mul a x3) b))))
   :rule-classes nil
   :hints
   (("Goal"
     :do-not '(preprocess)
     :use ((:instance field-tangent-square-difference
                      (quadratic
                       (field-add
                        (field-add (field-mul x3 x3) (field-mul x3 x1))
                        (field-add (field-mul x1 x1) a))))
           (:instance field-same-point-non-opposite-cubic-factor)
           (:instance field-curve-equation-from-difference
                      (y1-square (field-mul y1 y1))
                      (y3-square (field-mul y3 y3))
                      (x1-cube (field-mul (field-mul x1 x1) x1))
                      (x3-cube (field-mul (field-mul x3 x3) x3))
                      (ax1 (field-mul a x1))
                      (ax3 (field-mul a x3)))
           (:instance field-sub-equal-zero-implies-fixed-equal
                      (first (field-mul y3 y3))
                      (second
                       (field-add (field-mul (field-mul x3 x3) x3)
                                  (field-add (field-mul a x3) b)))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-mul-fixed-congruence
        field-mul-left-distributive field-mul-right-distributive
        field-mul-associative field-mul-commutative field-mul-of-neg-right
        field-mul-of-neg-left field-add-associative field-add-commutative
        field-add-inverse-middle field-add-inverse-shuffle
        field-add-inverse-left
        field-add-inverse-right field-add-zero-left field-add-zero-right
        field-fix-of-add field-fix-of-mul field-fix-of-neg))))))

(defthm short-weierstrass-affine-point-p-of-affine-same-point-non-opposite-output
  (implies
   (and (short-weierstrass-affine-point-p first)
        (equal (affine-pair-classify first second)
               :same-point-non-opposite))
   (short-weierstrass-affine-point-p
    (affine-same-point-non-opposite-output first)))
  :rule-classes nil
  :hints
  (("Goal"
    :do-not '(preprocess)
    :use
    (affine-same-point-non-opposite-tangent-identity
     affine-same-point-non-opposite-output-y-rearrangement
     (:instance short-weierstrass-affine-point-p-definition
                (coordinates first))
     (:instance short-weierstrass-affine-point-p-definition
                (coordinates (affine-same-point-non-opposite-output first)))
     (:instance field-same-point-non-opposite-closure-algebra
                (slope (affine-same-point-non-opposite-slope first))
                (x1 (affine-coordinates-x first))
                (y1 (affine-coordinates-y first))
                (x3 (affine-same-point-non-opposite-output-x first))
                (y3 (affine-same-point-non-opposite-output-y first))
                (a (field-fix (short-weierstrass-a)))
                (b (field-fix (short-weierstrass-b)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(short-weierstrass-equation-p short-weierstrass-rhs
       affine-coordinates-x-of-affine-same-point-non-opposite-output
       affine-coordinates-y-of-affine-same-point-non-opposite-output
       field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-coordinates-y
       field-element-p-of-affine-same-point-non-opposite-output-x
       field-element-p-of-affine-same-point-non-opposite-output-y
       field-add-commutative
       field-fix-when-field-element-p
       field-fix-idempotent field-fix-of-add field-fix-of-mul)))))
