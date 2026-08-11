(in-package "GFIELD")

(include-book "third-division-polynomial-expansion")

(defthm third-division-polynomial-expansion-minimal-theory-client
  (equal (third-division-polynomial-expression x a b)
         (third-division-polynomial-expanded-expression x a b))
  :hints (("Goal"
           :use third-division-polynomial-expression-is-expanded-expression
           :in-theory (theory 'minimal-theory))))

(defthm short-weierstrass-psi3-expansion-minimal-theory-client
  (equal (short-weierstrass-psi3 x)
         (third-division-polynomial-expanded-expression
          x (short-weierstrass-a) (short-weierstrass-b)))
  :hints (("Goal"
           :use short-weierstrass-psi3-is-expanded-expression
           :in-theory (theory 'minimal-theory))))
