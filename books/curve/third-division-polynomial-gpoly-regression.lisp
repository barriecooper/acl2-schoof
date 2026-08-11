(in-package "GFIELD")

(include-book "third-division-polynomial-gpoly")

(defthm third-division-polynomial-gpoly-eval-minimal-theory-client
  (equal
   (gpoly::eval
    (list (field-neg (field-mul a a))
          (field-nat-mul 12 b)
          (field-nat-mul 6 a)
          (field-zero)
          (field-nat-mul 3 (field-one)))
    x)
   (third-division-polynomial-expanded-expression x a b))
  :hints
  (("Goal"
    :use third-division-polynomial-gpoly-eval-is-expanded-expression
    :in-theory (theory 'minimal-theory))))

(defthm third-division-polynomial-normalized-gpoly-eval-minimal-theory-client
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
  :hints
  (("Goal"
    :use third-division-polynomial-normalized-gpoly-eval-is-expanded-expression
    :in-theory (theory 'minimal-theory))))
