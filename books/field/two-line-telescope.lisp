(in-package "GFIELD")

(include-book "kernel")

(local
 (defthm field-add-inverse-tail-two-line-local
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
 (defthm field-add-swap-two-line-local
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
 (defthm field-add-inverse-shuffle-two-line-local
   (equal (field-add x (field-add y (field-add (field-neg x) z)))
          (field-add y (field-fix z)))
   :hints
   (("Goal"
     :use ((:instance field-add-swap-two-line-local
                      (x x) (y y) (z (field-add (field-neg x) z)))
           (:instance field-add-inverse-tail-two-line-local (x x) (y z)))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-add-swap-two-line-local
                       field-add-inverse-tail-two-line-local
                       field-add-fix-right))))))

(local
 (defthm field-neg-of-add-two-line-local
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
      '(field-add-associative field-add-inverse-shuffle-two-line-local
        field-add-inverse-right
        field-add-zero-left field-fix-of-add field-fix-of-neg))))))

(local
 (defthm field-mul-of-neg-left-two-line-local
   (equal (field-mul (field-neg x) y)
          (field-neg (field-mul x y)))
   :hints
   (("Goal"
     :use ((:instance field-additive-inverse-unique
                      (x (field-mul x y))
                      (y (field-mul (field-neg x) y)))
           (:instance field-mul-right-distributive
                      (x x) (y (field-neg x)) (z y)))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-add-inverse-right field-mul-zero-left
                       field-fix-of-mul))))))

; Stage A: subtracting the oriented difference removes the second ordinate.
(local
 (defthm field-ordinate-telescope-two-line-local
   (equal (field-sub (field-add ya yb) (field-sub yb ya))
          (field-add ya ya))
   :hints
   (("Goal"
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-neg-of-add-two-line-local field-neg-of-neg
        field-add-associative field-add-commutative
        field-add-swap-two-line-local field-add-inverse-tail-two-line-local
        field-add-inverse-left field-add-inverse-right
        field-add-zero-left field-add-zero-right
        field-add-fix-right field-fix-idempotent
        field-fix-of-add field-fix-of-neg))))))

; Stage B: preserve the requested right factor and (r-p) orientation.
(local
 (defthm field-product-difference-two-line-local
   (equal (field-sub (field-mul r delta) (field-mul p delta))
          (field-mul (field-sub r p) delta))
   :hints
   (("Goal"
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-mul-right-distributive
        field-mul-of-neg-left-two-line-local
        field-fix-of-add field-fix-of-mul field-fix-of-neg))))))

; Stage C: the constrained operations respect equality without element premises.
(local
 (defthm field-sub-congruence-two-line-local
   (implies (and (equal left-a left-b)
                 (equal right-a right-b))
            (equal (field-sub left-a right-a)
                   (field-sub left-b right-b)))
   :hints (("Goal" :in-theory (enable field-sub)))))

(defthm field-two-line-equations-imply-doubled-first-ordinate
  (implies
   (and
    (equal (field-sub yb ya)
           (field-mul p delta))
    (equal (field-add ya yb)
           (field-mul r delta)))
   (equal
    (field-add ya ya)
    (field-mul (field-sub r p) delta)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance field-sub-congruence-two-line-local
                     (left-a (field-add ya yb))
                     (left-b (field-mul r delta))
                     (right-a (field-sub yb ya))
                     (right-b (field-mul p delta)))
          (:instance field-ordinate-telescope-two-line-local)
          (:instance field-product-difference-two-line-local))
    :in-theory (theory 'minimal-theory))))
