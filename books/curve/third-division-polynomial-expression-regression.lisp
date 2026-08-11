(in-package "GFIELD")
(include-book "third-division-polynomial-expression")

(defthm third-division-polynomial-expression-minimal-theory-client
  (equal (short-weierstrass-psi3 x)
         (third-division-polynomial-expression
          x (short-weierstrass-a) (short-weierstrass-b)))
  :hints (("Goal"
           :use short-weierstrass-psi3-is-third-division-polynomial-expression
           :in-theory (theory 'minimal-theory))))
