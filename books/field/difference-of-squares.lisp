(in-package "GFIELD")

(include-book "kernel")

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
       field-fix-of-neg)))))
