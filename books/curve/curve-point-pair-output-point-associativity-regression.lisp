(in-package "GFIELD")

(include-book "curve-point-pair-output-point-associativity")

; Canonical-output client regression.
(defthm curve-point-pair-output-point-canonical-client-regression
  (equal
   (curve-point-fix (curve-point-pair-output-point first second))
   (curve-point-pair-output-point first second))
  :hints
  (("Goal"
    :use curve-point-fix-of-curve-point-pair-output-point
    :in-theory (theory 'minimal-theory))))

; Fixed-output client regression.
(defthm curve-point-pair-output-point-associative-fixed-client-regression
  (implies
   (and
    (short-weierstrass-characteristic-p)
    (short-weierstrass-curve-point-p a)
    (short-weierstrass-curve-point-p b)
    (short-weierstrass-curve-point-p c))
   (equal
    (curve-point-fix
     (curve-point-pair-output-point
      (curve-point-pair-output-point a b) c))
    (curve-point-fix
     (curve-point-pair-output-point
      a (curve-point-pair-output-point b c)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use curve-point-pair-output-point-associative-fixed
    :in-theory (theory 'minimal-theory))))

; Final public-interface regression: only the executable associativity theorem
; is visible to this minimal-theory client.
(defthm curve-point-pair-output-point-associative-client-regression
  (implies
   (and
    (short-weierstrass-characteristic-p)
    (short-weierstrass-curve-point-p a)
    (short-weierstrass-curve-point-p b)
    (short-weierstrass-curve-point-p c))
   (equal
    (curve-point-pair-output-point
     (curve-point-pair-output-point a b) c)
    (curve-point-pair-output-point
     a (curve-point-pair-output-point b c))))
  :rule-classes nil
  :hints
  (("Goal"
    :use curve-point-pair-output-point-associative
    :in-theory (theory 'minimal-theory))))
