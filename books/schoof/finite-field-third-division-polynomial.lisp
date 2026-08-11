(in-package "GPOLY")

(include-book "../curve/third-division-polynomial-gpoly")
(include-book "division-polynomial-sequence")

; Repeated addition in the jointly constrained field.  This deliberately
; mirrors GFIELD::FIELD-NAT-MUL; the coefficient theorem below is the seam to
; the representation used by the division-polynomial books.
(defun finite-field-natural-scalar (n x)
  (declare (xargs :measure (nfix n)))
  (let ((n (nfix n)))
    (if (zp n)
        (gfield::finite-field-zero)
      (gfield::finite-field-add
       (gfield::finite-field-fix x)
       (finite-field-natural-scalar (1- n) x)))))

(local
 (defthm finite-field-mul-zero-left-for-natural-scalar
   (equal (gfield::finite-field-mul (gfield::finite-field-zero) x)
          (gfield::finite-field-zero))
   :hints
   (("Goal"
     :by (:functional-instance
          gfield::field-mul-zero-left
          (gfield::field-element-p gfield::finite-field-element-p)
          (gfield::field-fix gfield::finite-field-fix)
          (gfield::field-zero gfield::finite-field-zero)
          (gfield::field-one gfield::finite-field-one)
          (gfield::field-add gfield::finite-field-add)
          (gfield::field-mul gfield::finite-field-mul)
          (gfield::field-neg gfield::finite-field-neg)
          (gfield::field-inv gfield::finite-field-inv))
     :in-theory (theory 'minimal-theory))
    (and stable-under-simplificationp
         (list :use (theory 'gfield::finite-field-context-instance-theory)
               :in-theory (list 'quote (theory 'minimal-theory)))))))

(defthm finite-field-natural-scalar-is-natural-coefficient-times
  (equal (finite-field-natural-scalar n x)
         (gfield::finite-field-mul
          (finite-field-natural-coefficient n)
          (gfield::finite-field-fix x)))
  :hints (("Goal"
           :induct (finite-field-natural-scalar n x)
           :in-theory
           (enable finite-field-natural-scalar
                   finite-field-natural-coefficient
                   finite-field-mul-zero-left-for-natural-scalar
                   gfield::finite-field-mul-left-distributive))))

(defun finite-field-third-division-polynomial-expanded-expression (x a b)
  (gfield::finite-field-add
   (gfield::finite-field-add
    (gfield::finite-field-add
     (finite-field-natural-scalar
      3 (gfield::finite-field-mul
         (gfield::finite-field-mul (gfield::finite-field-fix x)
                                   (gfield::finite-field-fix x))
         (gfield::finite-field-mul (gfield::finite-field-fix x)
                                   (gfield::finite-field-fix x))))
     (finite-field-natural-scalar
      6 (gfield::finite-field-mul
         (gfield::finite-field-fix a)
         (gfield::finite-field-mul (gfield::finite-field-fix x)
                                   (gfield::finite-field-fix x)))))
    (finite-field-natural-scalar
     12 (gfield::finite-field-mul (gfield::finite-field-fix b)
                                  (gfield::finite-field-fix x))))
   (gfield::finite-field-neg
    (gfield::finite-field-mul (gfield::finite-field-fix a)
                              (gfield::finite-field-fix a)))))

(defthm finite-field-element-p-of-third-division-polynomial-expanded-expression
  (gfield::finite-field-element-p
   (finite-field-third-division-polynomial-expanded-expression x a b)))

(defthm finite-field-third-division-polynomial-expanded-expression-of-fixes
  (equal
   (finite-field-third-division-polynomial-expanded-expression
    (gfield::finite-field-fix x)
    (gfield::finite-field-fix a)
    (gfield::finite-field-fix b))
   (finite-field-third-division-polynomial-expanded-expression x a b)))

(defthm finite-field-third-division-polynomial-expanded-expression-of-coefficient-fixes
  (equal
   (finite-field-third-division-polynomial-expanded-expression
    x (gfield::finite-field-fix a) (gfield::finite-field-fix b))
   (finite-field-third-division-polynomial-expanded-expression x a b))
  :hints (("Goal"
           :in-theory
           (enable finite-field-third-division-polynomial-expanded-expression))))

(defmacro def-psi3-finite-field-transport (name formula source)
  `(defthm ,name
     ,formula
     :rule-classes nil
     :hints
     (("Goal"
       :by (:functional-instance
            ,source
            (gfield::field-element-p gfield::finite-field-element-p)
            (gfield::field-fix gfield::finite-field-fix)
            (gfield::field-zero gfield::finite-field-zero)
            (gfield::field-one gfield::finite-field-one)
            (gfield::field-add gfield::finite-field-add)
            (gfield::field-mul gfield::finite-field-mul)
            (gfield::field-neg gfield::finite-field-neg)
            (gfield::field-inv gfield::finite-field-inv)
            (gfield::field-sub
             (lambda (x y)
               (gfield::finite-field-add
                x (gfield::finite-field-neg y))))
            (gfield::field-nat-mul finite-field-natural-scalar)
            (gfield::third-division-polynomial-expanded-expression
             finite-field-third-division-polynomial-expanded-expression)
            (fix-coefficients finite-field-poly-fix-coefficients)
            (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
            (normalize finite-field-poly-normalize)
            (eval finite-field-poly-eval))
       :in-theory (theory 'minimal-theory))
      (and stable-under-simplificationp
           (list :use (theory 'gfield::finite-field-context-instance-theory)
                 :in-theory
                 (list 'quote
                       (union-theories
                        '((:definition finite-field-natural-scalar)
                          (:definition finite-field-third-division-polynomial-expanded-expression)
                          (:definition finite-field-poly-fix-coefficients)
                          (:definition finite-field-poly-trim-trailing-zeros)
                          (:definition finite-field-poly-normalize)
                          (:definition finite-field-poly-eval))
                        (theory 'minimal-theory))))))))

(def-psi3-finite-field-transport
  finite-field-third-division-polynomial-natural-scalar-dense-eval
  (equal
   (finite-field-poly-eval
    (list (gfield::finite-field-neg (gfield::finite-field-mul a a))
          (finite-field-natural-scalar 12 b)
          (finite-field-natural-scalar 6 a)
          (gfield::finite-field-zero)
          (finite-field-natural-scalar 3 (gfield::finite-field-one))) x)
   (finite-field-third-division-polynomial-expanded-expression x a b))
  gfield::third-division-polynomial-gpoly-eval-is-expanded-expression)

(def-psi3-finite-field-transport
  finite-field-third-division-polynomial-natural-scalar-normalized-eval
  (equal
   (finite-field-poly-eval
    (finite-field-poly-normalize
     (list (gfield::finite-field-neg (gfield::finite-field-mul a a))
           (finite-field-natural-scalar 12 b)
           (finite-field-natural-scalar 6 a)
           (gfield::finite-field-zero)
           (finite-field-natural-scalar 3 (gfield::finite-field-one)))) x)
   (finite-field-third-division-polynomial-expanded-expression x a b))
  gfield::third-division-polynomial-normalized-gpoly-eval-is-expanded-expression)

(defthm finite-field-third-division-polynomial-dense-eval-is-expanded-expression
  (equal
   (finite-field-poly-eval
    (list (gfield::finite-field-neg (gfield::finite-field-mul a a))
          (gfield::finite-field-mul (finite-field-natural-coefficient 12) b)
          (gfield::finite-field-mul (finite-field-natural-coefficient 6) a)
          (gfield::finite-field-zero)
          (finite-field-natural-coefficient 3)) x)
   (finite-field-third-division-polynomial-expanded-expression x a b))
  :rule-classes nil
  :hints (("Goal" :use finite-field-third-division-polynomial-natural-scalar-dense-eval
           :in-theory (enable finite-field-natural-scalar-is-natural-coefficient-times
                              gfield::finite-field-mul-commutative
                              gfield::finite-field-mul-one-left
                              finite-field-element-p-of-natural-coefficient))))

(defthm finite-field-third-division-polynomial-normalized-dense-eval-is-expanded-expression
  (equal
   (finite-field-poly-eval
    (finite-field-poly-normalize
     (list (gfield::finite-field-neg (gfield::finite-field-mul a a))
           (gfield::finite-field-mul (finite-field-natural-coefficient 12) b)
           (gfield::finite-field-mul (finite-field-natural-coefficient 6) a)
           (gfield::finite-field-zero)
           (finite-field-natural-coefficient 3))) x)
   (finite-field-third-division-polynomial-expanded-expression x a b))
  :rule-classes nil
  :hints (("Goal" :use finite-field-third-division-polynomial-natural-scalar-normalized-eval
           :in-theory (enable finite-field-natural-scalar-is-natural-coefficient-times
                              gfield::finite-field-mul-commutative
                              gfield::finite-field-mul-one-left
                              finite-field-element-p-of-natural-coefficient))))

(defthm finite-field-division-polynomial-index-3-correspondence
  (equal
   (finite-field-division-polynomial 3 a b)
   (finite-field-poly-normalize
    (list
     (gfield::finite-field-neg
      (gfield::finite-field-mul (gfield::finite-field-fix a)
                                (gfield::finite-field-fix a)))
     (gfield::finite-field-mul (finite-field-natural-coefficient 12)
                               (gfield::finite-field-fix b))
     (gfield::finite-field-mul (finite-field-natural-coefficient 6)
                               (gfield::finite-field-fix a))
     (gfield::finite-field-zero)
     (finite-field-natural-coefficient 3))))
  :rule-classes nil
  :hints (("Goal"
           :use (finite-field-division-polynomial-evaluator-base-equations
                 finite-field-division-polynomial-base-index-3)
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-division-polynomial-index-3-eval-is-expanded-expression
  (equal
   (finite-field-poly-eval (finite-field-division-polynomial 3 a b) x)
   (finite-field-third-division-polynomial-expanded-expression x a b))
  :rule-classes nil
  :hints (("Goal"
           :use (finite-field-division-polynomial-index-3-correspondence
                 finite-field-third-division-polynomial-expanded-expression-of-coefficient-fixes
                 (:instance
                  finite-field-third-division-polynomial-normalized-dense-eval-is-expanded-expression
                  (a (gfield::finite-field-fix a))
                  (b (gfield::finite-field-fix b))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(gfield::finite-field-mul-fix-left
              gfield::finite-field-mul-fix-right)))))

(verify-guards finite-field-natural-scalar)
(verify-guards finite-field-third-division-polynomial-expanded-expression)
