(in-package "GFIELD")

(include-book "curve-point-addition-relation-associativity")

; Public-interface regression: the full tagged client invokes only the final
; semantic theorem, with the entire implementation and proof assembly opaque.
(defthm curve-point-addition-relation-associative-client-regression
  (implies
   (and
    (short-weierstrass-characteristic-p)
    (short-weierstrass-curve-point-p a)
    (short-weierstrass-curve-point-p b)
    (short-weierstrass-curve-point-p c)
    (curve-point-addition-relation-p a b ab)
    (curve-point-addition-relation-p b c bc)
    (curve-point-addition-relation-p ab c left)
    (curve-point-addition-relation-p a bc right))
   (equal (curve-point-fix left)
          (curve-point-fix right)))
  :rule-classes nil
  :hints
  (("Goal"
    :use curve-point-addition-relation-associative
    :in-theory (theory 'minimal-theory))))
