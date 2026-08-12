(in-package "GPOLY")

(include-book "quotient-coordinate-semantics")

(defthm quotient-coordinate-semantic-multiplication-minimal-theory-client
  (implies (and (equal (eval modulus x0) (gfield::field-zero))
                (quotient-coordinate-semantic-curve-p x0 y0 a b))
           (equal
            (quotient-coordinate-semantic-eval
             (quotient-coordinate-mul left right a b modulus) x0 y0)
            (gfield::field-mul
             (quotient-coordinate-semantic-eval left x0 y0)
             (quotient-coordinate-semantic-eval right x0 y0))))
  :rule-classes nil
  :hints (("Goal" :use quotient-coordinate-semantic-eval-of-mul
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-semantic-power-minimal-theory-client
  (implies (and (equal (eval modulus x0) (gfield::field-zero))
                (quotient-coordinate-semantic-curve-p x0 y0 a b))
           (equal
            (quotient-coordinate-semantic-eval
             (quotient-coordinate-pow coordinate n a b modulus) x0 y0)
            (gfield::field-pow
             (quotient-coordinate-semantic-eval coordinate x0 y0) n)))
  :rule-classes nil
  :hints (("Goal" :use quotient-coordinate-semantic-eval-of-pow
           :in-theory (theory 'minimal-theory))))
