(in-package "GFIELD")

(include-book "kernel")

; Bounded additive and multiplicative bridges for the cubic factorization.
(local
 (defthm field-mul-of-neg-right-cubic-local
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
     (union-theories (theory 'minimal-theory)
                     '(field-add-inverse-right field-mul-zero-right
                       field-fix-of-mul))))))

(local
 (defthm field-mul-of-neg-left-cubic-local
   (equal (field-mul (field-neg x) y)
          (field-neg (field-mul x y)))
   :hints
   (("Goal"
     :use ((:instance field-mul-commutative (x (field-neg x)) (y y))
           (:instance field-mul-commutative (x y) (y x))
           (:instance field-mul-of-neg-right-cubic-local (x y) (y x)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-add-inverse-middle-cubic-local
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
 (defthm field-add-swap-first-two-cubic-local
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
 (defthm field-add-inverse-shuffle-cubic-local
   (equal (field-add x (field-add y (field-add (field-neg x) z)))
          (field-add y (field-fix z)))
   :hints
   (("Goal"
     :use ((:instance field-add-swap-first-two-cubic-local
                      (x x) (y y) (z (field-add (field-neg x) z)))
           (:instance field-add-inverse-middle-cubic-local (x x) (y z)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-add-swap-first-two-cubic-local
        field-add-inverse-middle-cubic-local field-add-fix-right))))))

(local
 (defthm field-neg-of-add-cubic-local
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
      '(field-add-associative field-add-inverse-shuffle-cubic-local
        field-add-inverse-right field-add-zero-left
        field-fix-of-add field-fix-of-neg))))))

(local
 (defthm field-add-cancel-separated-cubic-local
   (equal
    (field-add b (field-add c (field-add d (field-add (field-neg b) e))))
    (field-add c (field-add d (field-fix e))))
   :hints
   (("Goal"
     :use ((:instance field-add-swap-first-two-cubic-local
                      (x b) (y c)
                      (z (field-add d (field-add (field-neg b) e))))
           (:instance field-add-inverse-shuffle-cubic-local
                      (x b) (y d) (z e)))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-add-fix-right))))))

(local
 (defthm field-add-cancel-at-end-cubic-local
   (equal (field-add b (field-add c (field-add d (field-neg b))))
          (field-add c (field-fix d)))
   :hints
   (("Goal"
     :use ((:instance field-add-commutative (x d) (y (field-neg b)))
           (:instance field-add-inverse-shuffle-cubic-local
                      (x b) (y c) (z d)))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-add-fix-right field-fix-of-add))))))

(local
 (defthm field-mul-cubic-cross-term-local
   (equal (field-mul xc (field-mul xa xc))
          (field-mul xa (field-mul xc xc)))
   :hints
   (("Goal"
     :use ((:instance field-mul-associative (x xc) (y xa) (z xc))
           (:instance field-mul-associative (x xa) (y xc) (z xc))
           (:instance field-mul-commutative (x xc) (y xa)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-mul-cubic-cross-term-reversed-local
   (equal (field-mul xa (field-mul xc xc))
          (field-mul xc (field-mul xc xa)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-mul-associative (x xa) (y xc) (z xc))
           (:instance field-mul-associative (x xc) (y xa) (z xc))
           (:instance field-mul-associative (x xc) (y xc) (z xa))
           (:instance field-mul-commutative (x xa) (y xc)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-mul-cubic-other-cross-term-local
   (equal (field-mul xc (field-mul xa xa))
          (field-mul xa (field-mul xa xc)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-mul-associative (x xc) (y xa) (z xa))
           (:instance field-mul-associative (x xa) (y xc) (z xa))
           (:instance field-mul-associative (x xa) (y xa) (z xc))
           (:instance field-mul-commutative (x xc) (y xa)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-difference-of-cubes-reversed-local
   (equal
    (field-mul
     (field-add
      (field-add (field-mul xc xc) (field-mul xc xa))
      (field-mul xa xa))
     (field-sub xc xa))
    (field-sub
     (field-mul (field-mul xc xc) xc)
     (field-mul (field-mul xa xa) xa)))
   :hints
   (("Goal"
     :do-not '(preprocess)
     :use ((:instance field-mul-cubic-cross-term-local)
           (:instance field-mul-cubic-cross-term-reversed-local)
           (:instance field-mul-cubic-other-cross-term-local))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-mul-left-distributive
        field-mul-right-distributive field-mul-associative
        field-mul-commutative field-mul-of-neg-right-cubic-local
        field-mul-of-neg-left-cubic-local
        field-add-associative field-add-commutative
        field-add-swap-first-two-cubic-local
        field-add-inverse-middle-cubic-local
        field-add-inverse-shuffle-cubic-local
        field-add-cancel-separated-cubic-local
        field-add-cancel-at-end-cubic-local
        field-add-inverse-left field-add-inverse-right
        field-add-zero-left field-add-zero-right
        field-fix-of-add field-fix-of-mul field-fix-of-neg))))))

(defthm field-difference-of-cubes
  (equal
   (field-sub
    (field-mul (field-mul xc xc) xc)
    (field-mul (field-mul xa xa) xa))
   (field-mul
    (field-sub xc xa)
    (field-add
     (field-add (field-mul xc xc) (field-mul xc xa))
     (field-mul xa xa))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance field-difference-of-cubes-reversed-local)
          (:instance field-mul-commutative
                     (x (field-sub xc xa))
                     (y (field-add
                         (field-add (field-mul xc xc)
                                    (field-mul xc xa))
                         (field-mul xa xa)))))
    :in-theory (theory 'minimal-theory))))

(local
 (defthm field-sub-paired-sums-cubic-local
   (equal (field-sub (field-add p q) (field-add r s))
          (field-add (field-sub p r) (field-sub q s)))
   :hints
   (("Goal"
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-neg-of-add-cubic-local
        field-add-associative field-add-commutative
        field-add-swap-first-two-cubic-local
        field-fix-of-add field-fix-of-neg))))))

(local
 (defthm field-linear-difference-factorization-local
   (equal (field-sub (field-mul curve-a xc)
                     (field-mul curve-a xa))
          (field-mul (field-sub xc xa) curve-a))
   :hints
   (("Goal"
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-mul-right-distributive
        field-mul-commutative field-mul-of-neg-right-cubic-local
        field-fix-of-mul))))))

(local
 (defthm field-combine-common-left-factor-cubic-local
   (equal (field-add (field-mul difference cubic-sum)
                     (field-mul difference curve-a))
          (field-mul difference (field-add cubic-sum curve-a)))
   :hints
   (("Goal"
     :use ((:instance field-mul-left-distributive
                      (x difference) (y cubic-sum) (z curve-a)))
     :in-theory (theory 'minimal-theory)))))

(defthm field-cubic-plus-linear-difference-factorization
  (equal
   (field-sub
    (field-add (field-mul (field-mul xc xc) xc)
               (field-mul curve-a xc))
    (field-add (field-mul (field-mul xa xa) xa)
               (field-mul curve-a xa)))
   (field-mul
    (field-sub xc xa)
    (field-add
     (field-add
      (field-add (field-mul xc xc) (field-mul xc xa))
      (field-mul xa xa))
     curve-a)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance field-sub-paired-sums-cubic-local
                (p (field-mul (field-mul xc xc) xc))
                (q (field-mul curve-a xc))
                (r (field-mul (field-mul xa xa) xa))
                (s (field-mul curve-a xa)))
     (:instance field-difference-of-cubes)
     (:instance field-linear-difference-factorization-local)
     (:instance field-combine-common-left-factor-cubic-local
                (difference (field-sub xc xa))
                (cubic-sum
                 (field-add
                  (field-add (field-mul xc xc) (field-mul xc xa))
                  (field-mul xa xa)))))
    :in-theory (theory 'minimal-theory))))
