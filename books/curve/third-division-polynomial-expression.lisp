(in-package "GFIELD")

(include-book "../curve/third-division-polynomial")
(include-book "../polynomial/generic/base")

(defun third-division-polynomial-expression (x a b)
  (field-sub
   (field-nat-mul 12
                  (field-mul (field-fix x)
                             (field-add
                              (field-add
                               (field-mul (field-mul (field-fix x) (field-fix x))
                                          (field-fix x))
                               (field-mul (field-fix a) (field-fix x)))
                              (field-fix b))))
   (field-mul
    (field-add (field-nat-mul 3 (field-mul (field-fix x) (field-fix x)))
               (field-fix a))
    (field-add (field-nat-mul 3 (field-mul (field-fix x) (field-fix x)))
               (field-fix a)))))

(defthm field-element-p-of-third-division-polynomial-expression
  (field-element-p (third-division-polynomial-expression x a b))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(third-division-polynomial-expression field-sub
              field-element-p-of-add field-element-p-of-neg
              field-element-p-of-mul field-element-p-of-field-nat-mul)))))

(defthm third-division-polynomial-expression-of-fixes
  (equal (third-division-polynomial-expression
          (field-fix x) (field-fix a) (field-fix b))
         (third-division-polynomial-expression x a b))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(third-division-polynomial-expression field-fix-idempotent
              field-nat-mul-of-field-fix field-fix-of-add field-fix-of-mul)))))

(defthm short-weierstrass-psi3-is-third-division-polynomial-expression
  (equal (short-weierstrass-psi3 x)
         (third-division-polynomial-expression
          x (short-weierstrass-a) (short-weierstrass-b)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(short-weierstrass-psi3 short-weierstrass-rhs
              short-weierstrass-tangent-numerator
              third-division-polynomial-expression
              field-fix-idempotent field-fix-of-add field-fix-of-mul
              field-mul-of-fixes field-nat-mul-of-field-fix
              field-add-associative)))))

