(in-package "GPOLY")

(include-book "finite-field-third-division-polynomial")

(defthm finite-field-psi3-normalized-eval-minimal-theory-client
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
  :hints (("Goal" :use finite-field-third-division-polynomial-normalized-dense-eval-is-expanded-expression
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-psi3-index-3-polynomial-minimal-theory-client
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
  :hints (("Goal" :use finite-field-division-polynomial-index-3-correspondence
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-psi3-index-3-eval-minimal-theory-client
  (equal (finite-field-poly-eval
          (finite-field-division-polynomial 3 a b) x)
         (finite-field-third-division-polynomial-expanded-expression x a b))
  :rule-classes nil
  :hints (("Goal" :use finite-field-division-polynomial-index-3-eval-is-expanded-expression
           :in-theory (theory 'minimal-theory))))
