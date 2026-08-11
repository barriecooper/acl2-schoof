(in-package "GPOLY")

(include-book "f11-third-division-polynomial")

(defthm f11-psi3-index-3-eval-minimal-theory-client
  (equal (f11-eval (f11-division-polynomial 3 a b) x)
         (f11-third-division-polynomial-expanded-expression x a b))
  :rule-classes nil
  :hints (("Goal" :use f11-division-polynomial-index-3-eval-is-expanded-expression
           :in-theory (theory 'minimal-theory))))

(defthm f11-golden-psi3-coefficients-minimal-theory-client
  (equal (f11-division-polynomial 3 1 6) '(10 6 6 0 3))
  :rule-classes nil
  :hints (("Goal" :use f11-golden-division-polynomial-index-3
           :in-theory (theory 'minimal-theory))))

(defthm f11-golden-literal-psi3-eval-minimal-theory-client
  (equal (f11-eval '(10 6 6 0 3) x)
         (f11-third-division-polynomial-expanded-expression x 1 6))
  :rule-classes nil
  :hints (("Goal" :use f11-golden-literal-division-polynomial-index-3-eval
           :in-theory (theory 'minimal-theory))))
