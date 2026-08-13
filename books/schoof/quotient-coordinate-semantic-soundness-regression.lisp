(in-package "GPOLY")

(include-book "quotient-coordinate-semantic-soundness")

(defthm quotient-coordinate-frobenius-semantic-soundness-minimal-theory-client
  (implies (and (equal (eval modulus x0) (gfield::field-zero))
                (quotient-coordinate-semantic-curve-p x0 y0 a b))
           (equal
            (quotient-coordinate-semantic-eval
             (quotient-coordinate-frobenius coordinate q a b modulus) x0 y0)
            (gfield::field-pow
             (quotient-coordinate-semantic-eval coordinate x0 y0) q)))
  :rule-classes nil
  :hints (("Goal" :use quotient-coordinate-semantic-eval-of-frobenius
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-frobenius-iterate-semantic-soundness-minimal-theory-client
  (implies (and (equal (eval modulus x0) (gfield::field-zero))
                (quotient-coordinate-semantic-curve-p x0 y0 a b))
           (equal
            (quotient-coordinate-semantic-eval
             (quotient-coordinate-frobenius-iterate
              coordinate q iterations a b modulus) x0 y0)
            (gfield::field-pow
             (quotient-coordinate-semantic-eval coordinate x0 y0)
             (expt (nfix q) (nfix iterations)))))
  :rule-classes nil
  :hints (("Goal" :use quotient-coordinate-semantic-eval-of-frobenius-iterate
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-cross-add-semantic-soundness-minimal-theory-client
  (implies
   (and (equal (eval modulus x0) (gfield::field-zero))
        (quotient-coordinate-semantic-curve-p x0 y0 a b)
        (quotient-coordinate-cross-add-p
         x1 y1 x2 y2 x3 y3 a b modulus))
   (quotient-coordinate-field-cross-add-p
    (quotient-coordinate-semantic-eval x1 x0 y0)
    (quotient-coordinate-semantic-eval y1 x0 y0)
    (quotient-coordinate-semantic-eval x2 x0 y0)
    (quotient-coordinate-semantic-eval y2 x0 y0)
    (quotient-coordinate-semantic-eval x3 x0 y0)
    (quotient-coordinate-semantic-eval y3 x0 y0)))
  :rule-classes nil
  :hints (("Goal" :use quotient-coordinate-cross-add-p-semantic-soundness
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-cross-opposite-semantic-soundness-minimal-theory-client
  (implies
   (and (equal (eval modulus x0) (gfield::field-zero))
        (quotient-coordinate-cross-opposite-p x1 y1 x2 y2 modulus))
   (quotient-coordinate-field-cross-opposite-p
    (quotient-coordinate-semantic-eval x1 x0 y0)
    (quotient-coordinate-semantic-eval y1 x0 y0)
    (quotient-coordinate-semantic-eval x2 x0 y0)
    (quotient-coordinate-semantic-eval y2 x0 y0)))
  :rule-classes nil
  :hints (("Goal" :use quotient-coordinate-cross-opposite-p-semantic-soundness
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-trace-candidate-semantic-soundness-minimal-theory-client
  (implies
   (and (equal (eval modulus x0) (gfield::field-zero))
        (quotient-coordinate-semantic-curve-p x0 y0 a b)
        (quotient-coordinate-trace-candidate-p x y q trace a b modulus))
   (quotient-coordinate-field-trace-candidate-p
    (quotient-coordinate-semantic-eval x x0 y0)
    (quotient-coordinate-semantic-eval y x0 y0)
    q trace))
  :rule-classes nil
  :hints (("Goal" :use quotient-coordinate-trace-candidate-p-semantic-soundness
           :in-theory (theory 'minimal-theory))))
