(in-package "GFIELD")

(include-book "third-division-polynomial-expression")
(include-book "../field/common-summand-subtraction")

(defun third-division-polynomial-expanded-expression (x a b)
  (field-sub
   (field-add
    (field-add
     (field-nat-mul
      3
      (field-mul (field-mul (field-fix x) (field-fix x))
                 (field-mul (field-fix x) (field-fix x))))
     (field-nat-mul
      6
      (field-mul (field-fix a)
                 (field-mul (field-fix x) (field-fix x)))))
    (field-nat-mul 12
                   (field-mul (field-fix b) (field-fix x))))
   (field-mul (field-fix a) (field-fix a))))

(defthm field-element-p-of-third-division-polynomial-expanded-expression
  (field-element-p (third-division-polynomial-expanded-expression x a b))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(third-division-polynomial-expanded-expression field-sub
              field-element-p-of-add field-element-p-of-neg
              field-element-p-of-mul field-element-p-of-field-nat-mul)))))

(defthm third-division-polynomial-expanded-expression-of-fixes
  (equal (third-division-polynomial-expanded-expression
          (field-fix x) (field-fix a) (field-fix b))
         (third-division-polynomial-expanded-expression x a b))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(third-division-polynomial-expanded-expression
              field-fix-idempotent field-nat-mul-of-field-fix
              field-fix-of-add field-fix-of-mul)))))

(defthm psi3-scaled-product-distribution
  (equal
   (field-nat-mul
    12
    (field-mul x
               (field-add
                (field-add (field-mul (field-mul x x) x)
                           (field-mul a x))
                b)))
   (field-add
    (field-add
     (field-nat-mul 12 (field-mul x (field-mul (field-mul x x) x)))
     (field-nat-mul 12 (field-mul x (field-mul a x))))
    (field-nat-mul 12 (field-mul x b))))
  :hints (("Goal"
           :in-theory
           (union-theories (theory 'minimal-theory)
            '(field-nat-mul-of-add field-mul-left-distributive)))))

(defthm psi3-quartic-monomial-reassociation
  (equal (field-mul x (field-mul (field-mul x x) x))
         (field-mul (field-mul x x) (field-mul x x)))
  :hints (("Goal"
           :use ((:instance field-mul-associative
                            (x x) (y (field-mul x x)) (z x))
                 (:instance field-mul-associative
                            (x (field-mul x x)) (y x) (z x))
                 (:instance field-mul-commutative
                            (x x) (y (field-mul x x))))
           :in-theory (theory 'minimal-theory))))

(defthm psi3-quadratic-monomial-reassociation
  (equal (field-mul x (field-mul a x))
         (field-mul a (field-mul x x)))
  :hints (("Goal"
           :use ((:instance field-mul-associative (x x) (y a) (z x))
                 (:instance field-mul-associative (x a) (y x) (z x))
                 (:instance field-mul-commutative (x x) (y a)))
           :in-theory (theory 'minimal-theory))))

(defthm psi3-scaled-product-expansion
  (equal
   (field-nat-mul
    12
    (field-mul x
               (field-add
                (field-add (field-mul (field-mul x x) x)
                           (field-mul a x))
                b)))
   (field-add
    (field-add
     (field-nat-mul 12
                    (field-mul (field-mul x x) (field-mul x x)))
     (field-nat-mul 12 (field-mul a (field-mul x x))))
    (field-nat-mul 12 (field-mul b x))))
  :hints (("Goal"
           :use (psi3-scaled-product-distribution
                 psi3-quartic-monomial-reassociation
                 psi3-quadratic-monomial-reassociation
                 (:instance field-mul-commutative (x x) (y b)))
           :in-theory (theory 'minimal-theory))))

(defthm psi3-binomial-square-distribution
  (equal (field-mul (field-add u v) (field-add u v))
         (field-add (field-add (field-mul u u) (field-mul u v))
                    (field-add (field-mul v u) (field-mul v v))))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(field-mul-left-distributive field-mul-right-distributive)))))

(defthm psi3-three-times-square-product
  (equal (field-mul (field-nat-mul 3 q) (field-nat-mul 3 q))
         (field-nat-mul 9 (field-mul q q)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory
           (enable field-nat-mul field-mul-left-distributive
                   field-mul-right-distributive field-mul-associative
                   field-mul-commutative field-add-associative
                   field-add-commutative))))

(defthm psi3-cross-term-collection
  (equal (field-add (field-mul (field-nat-mul 3 q) a)
                    (field-mul a (field-nat-mul 3 q)))
         (field-nat-mul 6 (field-mul a q)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory
           (enable field-nat-mul field-mul-left-distributive
                   field-mul-right-distributive field-mul-associative
                   field-mul-commutative field-add-associative
                   field-add-commutative))))

(defthm psi3-tangent-square-expansion
  (equal
   (field-mul
    (field-add (field-nat-mul 3 (field-mul x x)) a)
    (field-add (field-nat-mul 3 (field-mul x x)) a))
   (field-add
    (field-add
     (field-nat-mul 9
                    (field-mul (field-mul x x) (field-mul x x)))
     (field-nat-mul 6 (field-mul a (field-mul x x))))
    (field-mul a a)))
  :hints (("Goal"
           :use ((:instance psi3-binomial-square-distribution
                            (u (field-nat-mul 3 (field-mul x x))) (v a))
                 (:instance psi3-three-times-square-product
                            (q (field-mul x x)))
                 (:instance psi3-cross-term-collection
                            (q (field-mul x x))))
           :in-theory
           (union-theories (theory 'minimal-theory)
            '(field-add-associative psi3-quartic-monomial-reassociation)))))

(defthm psi3-left-coefficient-decomposition
  (equal
   (field-add (field-add (field-nat-mul 12 quartic)
                         (field-nat-mul 12 quadratic))
              linear)
   (field-add
    (field-add (field-add (field-nat-mul 3 quartic)
                          (field-nat-mul 6 quadratic))
               linear)
    (field-add (field-nat-mul 9 quartic)
               (field-nat-mul 6 quadratic))))
  :hints (("Goal"
           :use ((:instance field-nat-mul-of-sum
                            (m 3) (n 9) (x quartic))
                 (:instance field-nat-mul-of-sum
                            (m 6) (n 6) (x quadratic)))
           :in-theory
           (union-theories (theory 'minimal-theory)
            '(nfix field-add-associative field-add-commutative
              field-add-swap-first-two
              field-fix-of-add)))))

(defthm psi3-right-coefficient-reordering
  (equal
   (field-add (field-add (field-nat-mul 9 quartic)
                         (field-nat-mul 6 quadratic))
              square)
   (field-add square
              (field-add (field-nat-mul 9 quartic)
                         (field-nat-mul 6 quadratic))))
  :hints (("Goal"
           :use ((:instance field-add-commutative
                            (x (field-add (field-nat-mul 9 quartic)
                                          (field-nat-mul 6 quadratic)))
                            (y square)))
           :in-theory (theory 'minimal-theory))))

(defthm psi3-coefficient-collection
  (equal
   (field-sub
    (field-add (field-add (field-nat-mul 12 quartic)
                          (field-nat-mul 12 quadratic))
               linear)
    (field-add (field-add (field-nat-mul 9 quartic)
                          (field-nat-mul 6 quadratic))
               square))
   (field-sub
    (field-add (field-add (field-nat-mul 3 quartic)
                          (field-nat-mul 6 quadratic))
               linear)
    square))
  :hints (("Goal"
           :use (psi3-left-coefficient-decomposition
                 psi3-right-coefficient-reordering
                 (:instance field-sub-eliminate-common-right-summand
                            (left
                             (field-add
                              (field-add (field-nat-mul 12 quartic)
                                         (field-nat-mul 12 quadratic))
                              linear))
                            (right
                             (field-add
                              (field-add (field-nat-mul 9 quartic)
                                         (field-nat-mul 6 quadratic))
                              square))
                            (left-core
                             (field-add
                              (field-add (field-nat-mul 3 quartic)
                                         (field-nat-mul 6 quadratic))
                              linear))
                            (right-core square)
                            (common
                             (field-add (field-nat-mul 9 quartic)
                                        (field-nat-mul 6 quadratic)))))
           :in-theory (theory 'minimal-theory))))

(defthm third-division-polynomial-expression-is-expanded-expression
  (equal (third-division-polynomial-expression x a b)
         (third-division-polynomial-expanded-expression x a b))
  :hints (("Goal"
           :use ((:instance psi3-scaled-product-expansion
                            (x (field-fix x))
                            (a (field-fix a))
                            (b (field-fix b)))
                 (:instance psi3-tangent-square-expansion
                            (x (field-fix x)) (a (field-fix a)))
                 (:instance psi3-coefficient-collection
                            (quartic
                             (field-mul
                              (field-mul (field-fix x) (field-fix x))
                              (field-mul (field-fix x) (field-fix x))))
                            (quadratic
                             (field-mul (field-fix a)
                                        (field-mul (field-fix x) (field-fix x))))
                            (linear
                             (field-nat-mul
                              12 (field-mul (field-fix b) (field-fix x))))
                            (square (field-mul (field-fix a) (field-fix a)))))
           :in-theory
           (union-theories (theory 'minimal-theory)
            '(third-division-polynomial-expression
              third-division-polynomial-expanded-expression)))))

(defthm short-weierstrass-psi3-is-expanded-expression
  (equal (short-weierstrass-psi3 x)
         (third-division-polynomial-expanded-expression
          x (short-weierstrass-a) (short-weierstrass-b)))
  :hints (("Goal"
           :use (short-weierstrass-psi3-is-third-division-polynomial-expression
                 (:instance third-division-polynomial-expression-is-expanded-expression
                            (a (short-weierstrass-a))
                            (b (short-weierstrass-b))))
           :in-theory (theory 'minimal-theory))))
