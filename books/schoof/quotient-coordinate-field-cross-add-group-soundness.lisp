(in-package "GPOLY")

(include-book "quotient-coordinate-semantic-soundness")
(include-book "../curve/curve-point-addition-relation")

(defun quotient-coordinate-field-affine-point (x y)
  (gfield::affine-coordinates-make x y))

(defun quotient-coordinate-field-curve-point (x y)
  (gfield::curve-point-affine-coordinates
   (quotient-coordinate-field-affine-point x y)))

(local
 (defthm affine-fix-of-field-affine-point-local
   (equal (gfield::affine-coordinates-fix
           (quotient-coordinate-field-affine-point x y))
          (quotient-coordinate-field-affine-point x y))
   :hints (("Goal" :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(quotient-coordinate-field-affine-point
               gfield::affine-coordinates-fix
               gfield::affine-coordinates-x-of-make
               gfield::affine-coordinates-y-of-make)))
           ("Goal''" :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(gfield::affine-coordinates-make
               gfield::field-fix-idempotent))))))

(local
 (defthm field-sub-nonzero-implies-fixed-distinct-local
   (implies (not (equal (gfield::field-sub x2 x1)
                        (gfield::field-zero)))
            (not (equal (gfield::field-fix x1)
                        (gfield::field-fix x2))))
   :hints (("Goal"
            :use ((:instance gfield::field-add-fixed-congruence
                             (x1 x2) (x2 x1)
                             (y1 (gfield::field-neg x1))
                             (y2 (gfield::field-neg x1)))
                  (:instance gfield::field-add-inverse-right (x x1)))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(gfield::field-sub
                              gfield::field-fix-of-neg))))))

(local
 (defthm field-sub-is-fixed-local
   (equal (gfield::field-fix (gfield::field-sub x y))
          (gfield::field-sub x y))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
                            '(gfield::field-sub
                              gfield::field-element-p-of-add
                              gfield::field-element-p-of-neg
                              gfield::field-fix-when-field-element-p))))))

(local
 (defthm field-div-is-fixed-local
   (equal (gfield::field-fix (gfield::field-div x y))
          (gfield::field-div x y))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
                            '(gfield::field-div
                              gfield::field-element-p-of-mul
                              gfield::field-element-p-of-inv
                              gfield::field-fix-when-field-element-p))))))

(local
 (defthm quotient-times-denominator-local
   (implies (not (equal (gfield::field-sub x2 x1)
                        (gfield::field-zero)))
            (equal
             (gfield::field-mul
              (gfield::field-div (gfield::field-sub y2 y1)
                                 (gfield::field-sub x2 x1))
              (gfield::field-sub x2 x1))
             (gfield::field-sub y2 y1)))
   :hints (("Goal"
            :use ((:instance gfield::field-div-mul-denominator
                             (numerator (gfield::field-sub y2 y1))
                             (denominator (gfield::field-sub x2 x1))))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(field-sub-is-fixed-local))))))

(local
 (defthm field-mul-swap-first-two-local
   (equal (gfield::field-mul x (gfield::field-mul y z))
          (gfield::field-mul y (gfield::field-mul x z)))
   :hints (("Goal"
            :use ((:instance gfield::field-mul-associative (x x) (y y) (z z))
                  (:instance gfield::field-mul-associative (x y) (y x) (z z))
                  (:instance gfield::field-mul-commutative (x x) (y y)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm square-product-reassociate-local
   (equal (gfield::field-mul (gfield::field-mul d d)
                             (gfield::field-mul s s))
          (gfield::field-mul (gfield::field-mul s d)
                             (gfield::field-mul s d)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
                            '(gfield::field-mul-associative
                              gfield::field-mul-commutative
                              field-mul-swap-first-two-local))))))

(local
 (defthm denominator-square-times-slope-square-local
   (implies (not (equal (gfield::field-sub x2 x1)
                        (gfield::field-zero)))
            (equal
             (gfield::field-mul
              (gfield::field-mul (gfield::field-sub x2 x1)
                                 (gfield::field-sub x2 x1))
              (gfield::field-mul
               (gfield::field-div (gfield::field-sub y2 y1)
                                  (gfield::field-sub x2 x1))
               (gfield::field-div (gfield::field-sub y2 y1)
                                  (gfield::field-sub x2 x1))))
             (gfield::field-mul (gfield::field-sub y2 y1)
                                (gfield::field-sub y2 y1))))
   :hints (("Goal"
            :use (quotient-times-denominator-local
                  (:instance square-product-reassociate-local
                             (d (gfield::field-sub x2 x1))
                             (s (gfield::field-div
                                 (gfield::field-sub y2 y1)
                                 (gfield::field-sub x2 x1))))
                  (:instance gfield::field-mul-fixed-congruence
                             (x1 (gfield::field-mul
                                  (gfield::field-div
                                   (gfield::field-sub y2 y1)
                                   (gfield::field-sub x2 x1))
                                  (gfield::field-sub x2 x1)))
                             (x2 (gfield::field-sub y2 y1))
                             (y1 (gfield::field-mul
                                  (gfield::field-div
                                   (gfield::field-sub y2 y1)
                                   (gfield::field-sub x2 x1))
                                  (gfield::field-sub x2 x1)))
                             (y2 (gfield::field-sub y2 y1))))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(square-product-reassociate-local
                              field-sub-is-fixed-local
                              gfield::field-fix-of-mul))))))

(local
 (defthm denominator-square-nonzero-local
   (implies (not (equal (gfield::field-sub x2 x1)
                        (gfield::field-zero)))
            (not (equal
                  (gfield::field-mul (gfield::field-sub x2 x1)
                                     (gfield::field-sub x2 x1))
                  (gfield::field-zero))))
   :hints (("Goal"
            :use ((:instance gfield::field-mul-left-cancel-forward
                             (x (gfield::field-sub x2 x1))
                             (y (gfield::field-sub x2 x1))
                             (z (gfield::field-zero))))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(field-sub-is-fixed-local
                              gfield::field-fix-of-zero
                              gfield::field-mul-zero-right))))))

(local
 (defthm field-add-swap-first-two-local
   (equal (gfield::field-add x (gfield::field-add y z))
          (gfield::field-add y (gfield::field-add x z)))
   :hints (("Goal"
            :use ((:instance gfield::field-add-associative (x x) (y y) (z z))
                  (:instance gfield::field-add-associative (x y) (y x) (z z))
                  (:instance gfield::field-add-commutative (x x) (y y)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm three-add-reassociate-local
   (equal (gfield::field-add (gfield::field-add x3 x1) x2)
          (gfield::field-add x1 (gfield::field-add x2 x3)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
                            '(gfield::field-add-associative
                              gfield::field-add-commutative
                              field-add-swap-first-two-local))))))

(local
 (defthm cross-add-x-equation-to-secant-local
   (implies
    (and (not (equal (gfield::field-sub x2 x1) (gfield::field-zero)))
         (equal
          (gfield::field-mul
           (gfield::field-mul (gfield::field-sub x2 x1)
                              (gfield::field-sub x2 x1))
           (gfield::field-add x1 (gfield::field-add x2 x3)))
          (gfield::field-mul (gfield::field-sub y2 y1)
                             (gfield::field-sub y2 y1))))
    (equal
     (gfield::field-add (gfield::field-add x3 x1) x2)
     (gfield::field-mul
      (gfield::field-div (gfield::field-sub y2 y1)
                         (gfield::field-sub x2 x1))
      (gfield::field-div (gfield::field-sub y2 y1)
                         (gfield::field-sub x2 x1)))))
   :hints (("Goal"
            :use (denominator-square-times-slope-square-local
                  denominator-square-nonzero-local
                  three-add-reassociate-local
                  (:instance gfield::field-mul-left-cancel-forward
                             (x (gfield::field-mul
                                 (gfield::field-sub x2 x1)
                                 (gfield::field-sub x2 x1)))
                             (y (gfield::field-add x1
                                  (gfield::field-add x2 x3)))
                             (z (gfield::field-mul
                                 (gfield::field-div
                                  (gfield::field-sub y2 y1)
                                  (gfield::field-sub x2 x1))
                                 (gfield::field-div
                                  (gfield::field-sub y2 y1)
                                  (gfield::field-sub x2 x1))))))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(field-sub-is-fixed-local
                              field-div-is-fixed-local
                              gfield::field-fix-of-add
                              gfield::field-fix-of-mul))))))

(local
 (defthm replace-quotient-product-local
   (implies (equal (gfield::field-mul s d) n)
            (equal (gfield::field-mul n r)
                   (gfield::field-mul d (gfield::field-mul s r))))
   :hints (("Goal"
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(gfield::field-mul-associative
                              gfield::field-mul-commutative
                              field-mul-swap-first-two-local))))))

(local
 (defthm cross-add-y-equation-to-secant-local
   (implies
    (and (not (equal (gfield::field-sub x2 x1) (gfield::field-zero)))
         (equal
          (gfield::field-mul (gfield::field-sub x2 x1)
                             (gfield::field-add y1 y3))
          (gfield::field-mul (gfield::field-sub y2 y1)
                             (gfield::field-sub x1 x3))))
    (equal
     (gfield::field-add y3 y1)
     (gfield::field-mul
      (gfield::field-div (gfield::field-sub y2 y1)
                         (gfield::field-sub x2 x1))
      (gfield::field-sub x1 x3))))
   :hints (("Goal"
            :use (quotient-times-denominator-local
                  (:instance replace-quotient-product-local
                             (s (gfield::field-div
                                 (gfield::field-sub y2 y1)
                                 (gfield::field-sub x2 x1)))
                             (d (gfield::field-sub x2 x1))
                             (n (gfield::field-sub y2 y1))
                             (r (gfield::field-sub x1 x3)))
                  (:instance gfield::field-mul-left-cancel-forward
                             (x (gfield::field-sub x2 x1))
                             (y (gfield::field-add y1 y3))
                             (z (gfield::field-mul
                                 (gfield::field-div
                                  (gfield::field-sub y2 y1)
                                  (gfield::field-sub x2 x1))
                                 (gfield::field-sub x1 x3)))))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(gfield::field-mul-associative
                              gfield::field-mul-commutative
                              gfield::field-add-commutative
                              field-sub-is-fixed-local
                              field-div-is-fixed-local
                              gfield::field-fix-of-add
                              gfield::field-fix-of-mul))))))

(defthm quotient-coordinate-field-cross-add-implies-affine-secant-relation
  (implies
   (and (gfield::short-weierstrass-affine-point-p
         (quotient-coordinate-field-affine-point x1 y1))
        (gfield::short-weierstrass-affine-point-p
         (quotient-coordinate-field-affine-point x2 y2))
        (gfield::short-weierstrass-affine-point-p
         (quotient-coordinate-field-affine-point x3 y3))
        (quotient-coordinate-field-cross-add-p x1 y1 x2 y2 x3 y3)
        (not (equal (gfield::field-sub x2 x1) (gfield::field-zero))))
   (gfield::affine-distinct-x-secant-relation-p
    (quotient-coordinate-field-affine-point x1 y1)
    (quotient-coordinate-field-affine-point x2 y2)
    (gfield::field-div (gfield::field-sub y2 y1)
                       (gfield::field-sub x2 x1))
    (quotient-coordinate-field-affine-point x3 y3)))
  :rule-classes nil
  :hints (("Goal"
           :use (field-sub-nonzero-implies-fixed-distinct-local
                 quotient-times-denominator-local
                 cross-add-x-equation-to-secant-local
                 cross-add-y-equation-to-secant-local)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(quotient-coordinate-field-cross-add-p
              quotient-coordinate-field-affine-point
              gfield::affine-distinct-x-secant-relation-p
              gfield::affine-coordinates-x-of-make
              gfield::affine-coordinates-y-of-make
              field-div-is-fixed-local
              gfield::field-sub
              gfield::field-add-fix-left
              gfield::field-add-fix-right
              gfield::field-neg-of-fix)))))

(defthm quotient-coordinate-field-cross-add-implies-curve-point-addition
  (implies
   (and (gfield::short-weierstrass-affine-point-p
         (quotient-coordinate-field-affine-point x1 y1))
        (gfield::short-weierstrass-affine-point-p
         (quotient-coordinate-field-affine-point x2 y2))
        (gfield::short-weierstrass-affine-point-p
         (quotient-coordinate-field-affine-point x3 y3))
        (quotient-coordinate-field-cross-add-p x1 y1 x2 y2 x3 y3)
        (not (equal (gfield::field-sub x2 x1) (gfield::field-zero))))
   (gfield::curve-point-addition-relation-p
    (quotient-coordinate-field-curve-point x1 y1)
    (quotient-coordinate-field-curve-point x2 y2)
    (quotient-coordinate-field-curve-point x3 y3)))
  :rule-classes nil
  :hints (("Goal"
           :use (quotient-coordinate-field-cross-add-implies-affine-secant-relation
                 (:instance affine-fix-of-field-affine-point-local
                            (x x1) (y y1))
                 (:instance affine-fix-of-field-affine-point-local
                            (x x2) (y y2))
                 (:instance affine-fix-of-field-affine-point-local
                            (x x3) (y y3))
                 (:instance gfield::short-weierstrass-curve-point-p-of-affine
                            (coordinates
                             (quotient-coordinate-field-affine-point x1 y1)))
                 (:instance gfield::short-weierstrass-curve-point-p-of-affine
                            (coordinates
                             (quotient-coordinate-field-affine-point x2 y2))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(quotient-coordinate-field-curve-point
              quotient-coordinate-field-affine-point
              gfield::curve-point-addition-relation-p
              gfield::curve-point-fix-of-affine-coordinates
              gfield::curve-point-affine-coordinates-get-of-constructor
              gfield::affine-coordinates-fix-idempotent
              affine-fix-of-field-affine-point-local
              gfield::affine-coordinates-x-of-make
              gfield::affine-coordinates-y-of-make
              gfield::field-sub
              gfield::field-add-fix-left
              gfield::field-add-fix-right
              gfield::field-neg-of-fix
              gfield::affine-coordinates-fix-when-affine-coordinates-p
              gfield::affine-coordinates-p-of-fix)))))

(local
 (defthm field-sum-zero-implies-opposite-local
   (implies (equal (gfield::field-add y1 y2) (gfield::field-zero))
            (equal (gfield::field-fix y2) (gfield::field-neg y1)))
   :hints (("Goal"
            :use ((:instance gfield::field-add-left-cancel-forward
                             (x y1) (y y2) (z (gfield::field-neg y1))))
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(gfield::field-add-fix-right
               gfield::field-add-inverse-right
               gfield::field-fix-of-neg))))))

(defthm quotient-coordinate-field-cross-opposite-implies-affine-opposite-relation
  (implies
   (and (gfield::short-weierstrass-affine-point-p
         (quotient-coordinate-field-affine-point x1 y1))
        (gfield::short-weierstrass-affine-point-p
         (quotient-coordinate-field-affine-point x2 y2))
        (quotient-coordinate-field-cross-opposite-p x1 y1 x2 y2))
   (gfield::affine-opposite-y-infinity-relation-p
    (quotient-coordinate-field-affine-point x1 y1)
    (quotient-coordinate-field-affine-point x2 y2)
    (gfield::curve-point-infinity)))
  :rule-classes nil
  :hints (("Goal"
           :use (field-sum-zero-implies-opposite-local)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(quotient-coordinate-field-cross-opposite-p
              quotient-coordinate-field-affine-point
              gfield::affine-opposite-y-infinity-relation-p
              gfield::affine-coordinates-x-of-make
              gfield::affine-coordinates-y-of-make
              gfield::field-neg-of-fix
              gfield::curve-point-fix-of-infinity)))))

(defthm quotient-coordinate-field-cross-opposite-implies-curve-point-addition
  (implies
   (and (gfield::short-weierstrass-affine-point-p
         (quotient-coordinate-field-affine-point x1 y1))
        (gfield::short-weierstrass-affine-point-p
         (quotient-coordinate-field-affine-point x2 y2))
        (quotient-coordinate-field-cross-opposite-p x1 y1 x2 y2))
   (gfield::curve-point-addition-relation-p
    (quotient-coordinate-field-curve-point x1 y1)
    (quotient-coordinate-field-curve-point x2 y2)
    (gfield::curve-point-infinity)))
  :rule-classes nil
  :hints (("Goal"
           :use (quotient-coordinate-field-cross-opposite-implies-affine-opposite-relation
                 (:instance affine-fix-of-field-affine-point-local
                            (x x1) (y y1))
                 (:instance affine-fix-of-field-affine-point-local
                            (x x2) (y y2))
                 (:instance gfield::short-weierstrass-curve-point-p-of-affine
                            (coordinates
                             (quotient-coordinate-field-affine-point x1 y1)))
                 (:instance gfield::short-weierstrass-curve-point-p-of-affine
                            (coordinates
                             (quotient-coordinate-field-affine-point x2 y2))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(quotient-coordinate-field-curve-point
              gfield::curve-point-addition-relation-p
              gfield::curve-point-fix-of-affine-coordinates
              gfield::curve-point-affine-coordinates-get-of-constructor
              gfield::affine-coordinates-fix-idempotent
              gfield::curve-point-fix-of-infinity)))))

(verify-guards quotient-coordinate-field-affine-point)
(verify-guards quotient-coordinate-field-curve-point)
