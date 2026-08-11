(in-package "GFIELD")

(include-book "third-division-polynomial-expansion")
(include-book "../polynomial/generic/base")

; GPOLY stores the constant coefficient first.  Keep the literal evaluator
; expansion separate from the algebra that identifies its Horner monomials.
(local
 (defthm psi3-gpoly-literal-eval-is-horner-form
   (equal
    (gpoly::eval
     (list (field-neg (field-mul a a))
           (field-nat-mul 12 b)
           (field-nat-mul 6 a)
           (field-zero)
           (field-nat-mul 3 (field-one)))
     x)
    (field-add
     (field-neg (field-mul a a))
     (field-mul
      x
      (field-add
       (field-nat-mul 12 b)
       (field-mul
        x
        (field-add
         (field-nat-mul 6 a)
         (field-mul x
                    (field-mul x
                               (field-nat-mul 3 (field-one))))))))))
   :rule-classes nil
   :hints
   (("Goal"
     :expand
     ((gpoly::eval
       (list (field-neg (field-mul a a))
             (field-nat-mul 12 b)
             (field-nat-mul 6 a)
             (field-zero)
             (field-nat-mul 3 (field-one)))
       x))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(gpoly::eval car-cons cdr-cons field-fix-of-neg field-fix-of-mul
        field-nat-mul-of-field-fix field-fix-of-one field-fix-of-zero
        field-fix-when-field-element-p
        field-element-p-of-field-nat-mul
        field-mul-fix-left
        field-add-zero-left field-add-zero-right field-mul-zero-left
        field-mul-zero-right))))))

(local
 (defthm psi3-horner-linear-monomial
   (equal (field-mul x (field-nat-mul 12 b))
          (field-nat-mul 12 (field-mul b x)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-nat-mul-of-mul-right
                      (n 12) (x x) (y b))
           (:instance field-mul-commutative (x x) (y b))
           (:instance field-mul-commutative
                      (x x) (y (field-nat-mul 12 b))))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm psi3-horner-quadratic-monomial
   (equal (field-mul x (field-mul x (field-nat-mul 6 a)))
          (field-nat-mul 6 (field-mul a (field-mul x x))))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-nat-mul-of-mul-right
                      (n 6) (x (field-mul x x)) (y a))
           (:instance field-mul-associative
                      (x x) (y x) (z (field-nat-mul 6 a)))
           (:instance field-mul-commutative
                      (x (field-mul x x)) (y a))
           (:instance field-mul-commutative
                      (x (field-mul x x))
                      (y (field-nat-mul 6 a))))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm psi3-horner-quartic-monomial
   (equal
    (field-mul x
               (field-mul x
                          (field-mul x
                                     (field-mul x
                                                (field-nat-mul
                                                 3 (field-one))))))
    (field-nat-mul
     3
     (field-mul (field-mul x x) (field-mul x x))))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-nat-mul-of-mul-right
                      (n 3)
                      (x (field-mul (field-mul x x) (field-mul x x)))
                      (y (field-one)))
           (:instance field-mul-one-right
                      (x (field-mul (field-mul x x) (field-mul x x)))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-mul-associative field-fix-of-mul field-fix-of-one))))))

(local
 (defthm psi3-horner-additive-reordering
   (equal
    (field-add (field-neg square)
               (field-add linear (field-add quadratic quartic)))
    (field-sub
     (field-add (field-add quartic quadratic) linear)
     square))
   :rule-classes nil
   :hints
   (("Goal"
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-add-associative field-add-commutative
        field-add-swap-first-two))))))

(local
 (defthm psi3-gpoly-horner-is-common-form
   (equal
    (field-add
     (field-neg (field-mul a a))
     (field-mul
      x
      (field-add
       (field-nat-mul 12 b)
       (field-mul
        x
        (field-add
         (field-nat-mul 6 a)
         (field-mul x
                    (field-mul x
                               (field-nat-mul 3 (field-one)))))))))
    (field-add
     (field-neg (field-mul a a))
     (field-add
      (field-nat-mul 12 (field-mul b x))
      (field-add
       (field-nat-mul 6 (field-mul a (field-mul x x)))
       (field-nat-mul
        3 (field-mul (field-mul x x) (field-mul x x)))))))
   :rule-classes nil
   :hints
   (("Goal"
     :use (psi3-horner-linear-monomial
           psi3-horner-quadratic-monomial
           psi3-horner-quartic-monomial)
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-mul-left-distributive))))))

(local
 (defthm psi3-gpoly-common-form-is-expanded-expression
   (equal
    (field-add
     (field-neg (field-mul a a))
     (field-add
      (field-nat-mul 12 (field-mul b x))
      (field-add
       (field-nat-mul 6 (field-mul a (field-mul x x)))
       (field-nat-mul
        3 (field-mul (field-mul x x) (field-mul x x))))))
    (third-division-polynomial-expanded-expression x a b))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance psi3-horner-additive-reordering
                      (square (field-mul a a))
                      (linear
                       (field-nat-mul 12 (field-mul b x)))
                      (quadratic
                       (field-nat-mul
                        6 (field-mul a (field-mul x x))))
                      (quartic
                       (field-nat-mul
                        3
                        (field-mul (field-mul x x)
                                   (field-mul x x))))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(third-division-polynomial-expanded-expression
        field-mul-fix-left field-mul-fix-right))))))

(defthm third-division-polynomial-gpoly-eval-is-expanded-expression
  (equal
   (gpoly::eval
    (list (field-neg (field-mul a a))
          (field-nat-mul 12 b)
          (field-nat-mul 6 a)
          (field-zero)
          (field-nat-mul 3 (field-one)))
    x)
   (third-division-polynomial-expanded-expression x a b))
  :rule-classes nil
  :hints
  (("Goal"
    :use (psi3-gpoly-literal-eval-is-horner-form
          psi3-gpoly-horner-is-common-form
          psi3-gpoly-common-form-is-expanded-expression)
    :in-theory (theory 'minimal-theory))))

(defthm third-division-polynomial-normalized-gpoly-eval-is-expanded-expression
  (equal
   (gpoly::eval
    (gpoly::normalize
     (list (field-neg (field-mul a a))
           (field-nat-mul 12 b)
           (field-nat-mul 6 a)
           (field-zero)
           (field-nat-mul 3 (field-one))))
    x)
   (third-division-polynomial-expanded-expression x a b))
  :rule-classes nil
  :hints
  (("Goal"
    :use (third-division-polynomial-gpoly-eval-is-expanded-expression
          (:instance gpoly::eval-of-normalize
                     (gpoly::x x)
                     (poly
                      (list (field-neg (field-mul a a))
                            (field-nat-mul 12 b)
                            (field-nat-mul 6 a)
                            (field-zero)
                            (field-nat-mul 3 (field-one))))))
    :in-theory (theory 'minimal-theory))))
