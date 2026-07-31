(in-package "GFIELD")

(include-book "kernel")

(local
 (defthm field-add-inverse-middle-common-summand-local
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
 (defthm field-add-swap-first-two-common-summand-local
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
 (defthm field-add-inverse-shuffle-common-summand-local
   (equal (field-add x (field-add y (field-add (field-neg x) z)))
          (field-add y (field-fix z)))
   :hints
   (("Goal"
     :use ((:instance field-add-swap-first-two-common-summand-local
                      (x x) (y y) (z (field-add (field-neg x) z)))
           (:instance field-add-inverse-middle-common-summand-local
                      (x x) (y z)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-add-swap-first-two-common-summand-local
        field-add-inverse-middle-common-summand-local
        field-add-fix-right))))))

(local
 (defthm field-neg-of-add-common-summand-local
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
        field-add-inverse-shuffle-common-summand-local
        field-add-inverse-right field-add-zero-left
        field-fix-of-add field-fix-of-neg))))))

(local
 (defthm field-sub-common-right-sums-local
   (equal (field-sub (field-add left-core common)
                     (field-add right-core common))
          (field-sub left-core right-core))
   :hints
   (("Goal"
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-neg-of-add-common-summand-local
        field-add-associative field-add-commutative
        field-add-inverse-middle-common-summand-local
        field-add-swap-first-two-common-summand-local
        field-add-inverse-shuffle-common-summand-local
        field-add-inverse-left field-add-inverse-right
        field-add-zero-left field-add-zero-right
        field-fix-of-add field-fix-of-neg))))))

(defthm field-sub-eliminate-common-right-summand
  (implies
   (and (equal left (field-add left-core common))
        (equal right (field-add right-core common)))
   (equal (field-sub left right)
          (field-sub left-core right-core)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance field-sub-common-right-sums-local))
    :in-theory (theory 'minimal-theory))))
