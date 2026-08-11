(in-package "GPOLY")

(include-book "finite-field-third-division-polynomial")
(include-book "f11-division-polynomial-correspondence")
(include-book "../curve/f11-golden")

(defun f11-natural-scalar (n x)
  (declare (xargs :measure (nfix n)))
  (let ((n (nfix n)))
    (if (zp n)
        (gfield::f11-zero)
      (gfield::f11-add (gfield::f11-fix x)
                       (f11-natural-scalar (1- n) x)))))

(defthm f11-natural-scalar-is-natural-coefficient-times
  (equal (f11-natural-scalar n x)
         (gfield::f11-mul (f11-natural-coefficient n)
                          (gfield::f11-fix x)))
  :hints (("Goal"
           :induct (f11-natural-scalar n x)
           :in-theory (enable f11-natural-scalar
                              f11-natural-coefficient
                              gfield::f11-add
                              gfield::f11-mul
                              gfield::f11-fix
                              gfield::f11-zero
                              gfield::f11-one))))

(defthm f11-element-p-of-natural-scalar
  (gfield::f11-element-p (f11-natural-scalar n x)))

(defthm f11-natural-scalar-of-fix
  (equal (f11-natural-scalar n (gfield::f11-fix x))
         (f11-natural-scalar n x)))

(defun f11-third-division-polynomial-expanded-expression (x a b)
  (let* ((x (gfield::f11-fix x))
         (a (gfield::f11-fix a))
         (b (gfield::f11-fix b))
         (x2 (gfield::f11-mul x x))
         (x4 (gfield::f11-mul x2 x2)))
    (gfield::f11-add
     (gfield::f11-neg (gfield::f11-mul a a))
     (gfield::f11-add
      (f11-natural-scalar 12 (gfield::f11-mul b x))
      (gfield::f11-add
       (f11-natural-scalar 6 (gfield::f11-mul a x2))
       (f11-natural-scalar 3 x4))))))

(defthm f11-element-p-of-third-division-polynomial-expanded-expression
  (gfield::f11-element-p
   (f11-third-division-polynomial-expanded-expression x a b)))

(defthm f11-third-division-polynomial-expanded-expression-of-fixes
  (equal (f11-third-division-polynomial-expanded-expression
          (gfield::f11-fix x) (gfield::f11-fix a) (gfield::f11-fix b))
         (f11-third-division-polynomial-expanded-expression x a b)))

(local
 (defun f11-third-division-polynomial-functional-expression (x a b)
  (gfield::f11-add
   (gfield::f11-add
    (gfield::f11-add
     (f11-natural-scalar
      3 (gfield::f11-mul
         (gfield::f11-mul (gfield::f11-fix x) (gfield::f11-fix x))
         (gfield::f11-mul (gfield::f11-fix x) (gfield::f11-fix x))))
     (f11-natural-scalar
      6 (gfield::f11-mul
         (gfield::f11-fix a)
         (gfield::f11-mul (gfield::f11-fix x) (gfield::f11-fix x)))))
    (f11-natural-scalar
     12 (gfield::f11-mul (gfield::f11-fix b) (gfield::f11-fix x))))
   (gfield::f11-neg
    (gfield::f11-mul (gfield::f11-fix a) (gfield::f11-fix a))))))

(local
 (defthm f11-third-division-polynomial-functional-expression-is-expanded-expression
  (equal (f11-third-division-polynomial-functional-expression x a b)
         (f11-third-division-polynomial-expanded-expression x a b))
  :hints (("Goal" :in-theory
           (enable f11-third-division-polynomial-functional-expression
                   f11-third-division-polynomial-expanded-expression
                   gfield::f11-add-associative-for-context
                   gfield::f11-add-commutative-for-context
                   gfield::f11-mul-associative-for-context)))))

(local
 (defthm f11-third-division-polynomial-natural-scalar-normalized-eval
  (equal
   (f11-eval
    (f11-normalize
     (list (gfield::f11-neg (gfield::f11-mul a a))
           (f11-natural-scalar 12 b)
           (f11-natural-scalar 6 a)
           (gfield::f11-zero)
           (f11-natural-scalar 3 (gfield::f11-one)))) x)
   (f11-third-division-polynomial-functional-expression x a b))
  :rule-classes nil
  :hints
  (("Goal"
    :by (:functional-instance
         gfield::third-division-polynomial-normalized-gpoly-eval-is-expanded-expression
         (gfield::field-element-p gfield::f11-element-p)
         (gfield::field-fix gfield::f11-fix)
         (gfield::field-zero gfield::f11-zero)
         (gfield::field-one gfield::f11-one)
         (gfield::field-add gfield::f11-add)
         (gfield::field-mul gfield::f11-mul)
         (gfield::field-neg gfield::f11-neg)
         (gfield::field-inv gfield::f11-inv)
         (gfield::field-sub
          (lambda (x y) (gfield::f11-add x (gfield::f11-neg y))))
         (gfield::field-nat-mul f11-natural-scalar)
         (gfield::third-division-polynomial-expanded-expression
          f11-third-division-polynomial-functional-expression)
         (fix-coefficients f11-fix-coefficients)
         (trim-trailing-zeros f11-trim-trailing-zeros)
         (normalize f11-normalize)
         (eval f11-eval))
    :in-theory (theory 'minimal-theory))
   (and stable-under-simplificationp
        (list :use (theory 'gfield::f11-finite-field-context-instance-theory)
              :in-theory
              (list 'quote
                    (union-theories
                     '((:definition nfix)
                       (:definition zp)
                       (:definition gfield::f11-zero)
                       (:definition gfield::f11-one)
                       (:definition f11-natural-scalar)
                       (:definition f11-natural-coefficient)
                       (:definition f11-third-division-polynomial-functional-expression)
                       (:definition f11-fix-coefficients)
                       (:definition f11-trim-trailing-zeros)
                       (:definition f11-normalize)
                       (:definition f11-eval))
                     (theory 'minimal-theory))))))))

(defthm f11-third-division-polynomial-normalized-dense-eval-is-expanded-expression
  (equal
   (f11-eval
    (f11-normalize
     (list (gfield::f11-neg (gfield::f11-mul a a))
           (gfield::f11-mul (f11-natural-coefficient 12) b)
           (gfield::f11-mul (f11-natural-coefficient 6) a)
           (gfield::f11-zero)
           (f11-natural-coefficient 3))) x)
   (f11-third-division-polynomial-expanded-expression x a b))
  :rule-classes nil
  :hints (("Goal"
           :use (f11-third-division-polynomial-natural-scalar-normalized-eval
                 f11-third-division-polynomial-functional-expression-is-expanded-expression)
           :in-theory (enable f11-natural-scalar-is-natural-coefficient-times
                              gfield::f11-mul))))

(defthm f11-division-polynomial-index-3-correspondence
  (equal
   (f11-division-polynomial 3 a b)
   (f11-normalize
    (list
     (gfield::f11-neg
      (gfield::f11-mul (gfield::f11-fix a) (gfield::f11-fix a)))
     (gfield::f11-mul (f11-natural-coefficient 12) (gfield::f11-fix b))
     (gfield::f11-mul (f11-natural-coefficient 6) (gfield::f11-fix a))
     (gfield::f11-zero)
     (f11-natural-coefficient 3))))
  :rule-classes nil
  :hints (("Goal"
           :use (f11-division-polynomial-evaluator-base-equations
                 f11-division-polynomial-base-index-3-from-finite-field-instance)
           :in-theory (theory 'minimal-theory))))

(defthm f11-division-polynomial-index-3-eval-is-expanded-expression
  (equal (f11-eval (f11-division-polynomial 3 a b) x)
         (f11-third-division-polynomial-expanded-expression x a b))
  :rule-classes nil
  :hints (("Goal"
           :use (f11-division-polynomial-index-3-correspondence
                 (:instance
                  f11-third-division-polynomial-normalized-dense-eval-is-expanded-expression
                  (a (gfield::f11-fix a))
                  (b (gfield::f11-fix b))))
           :in-theory (enable gfield::f11-mul))))

(defthm f11-golden-division-polynomial-index-3
  (equal (f11-division-polynomial 3 1 6) '(10 6 6 0 3))
  :rule-classes nil
  :hints (("Goal" :use (:instance f11-division-polynomial-index-3-correspondence
                                  (a 1) (b 6))
           :in-theory (enable f11-normalize f11-fix-coefficients
                              f11-trim-trailing-zeros f11-natural-coefficient
                              gfield::f11-neg gfield::f11-mul gfield::f11-add
                              gfield::f11-fix gfield::f11-zero
                              gfield::f11-one))))

(defthm f11-golden-division-polynomial-index-3-eval
  (equal (f11-eval (f11-division-polynomial 3 1 6) x)
         (f11-third-division-polynomial-expanded-expression x 1 6))
  :rule-classes nil
  :hints (("Goal" :use (:instance
                         f11-division-polynomial-index-3-eval-is-expanded-expression
                         (a 1) (b 6))
           :in-theory (theory 'minimal-theory))))

(defthm f11-golden-literal-division-polynomial-index-3-eval
  (equal (f11-eval '(10 6 6 0 3) x)
         (f11-third-division-polynomial-expanded-expression x 1 6))
  :rule-classes nil
  :hints (("Goal" :use (f11-golden-division-polynomial-index-3
                         f11-golden-division-polynomial-index-3-eval)
           :in-theory (theory 'minimal-theory))))

(verify-guards f11-natural-scalar)
(verify-guards f11-third-division-polynomial-expanded-expression)
