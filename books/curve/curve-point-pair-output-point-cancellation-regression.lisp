(in-package "GFIELD")

(include-book "curve-point-pair-output-point-cancellation")

; These clients deliberately expose only their corresponding public theorem.
(defthm curve-point-pair-output-point-cancel-left-client-regression
  (implies
   (and
    (short-weierstrass-characteristic-p)
    (short-weierstrass-curve-point-p a)
    (short-weierstrass-curve-point-p b)
    (short-weierstrass-curve-point-p c)
    (equal (curve-point-pair-output-point a b)
           (curve-point-pair-output-point a c)))
   (equal b c))
  :rule-classes nil
  :hints (("Goal" :use curve-point-pair-output-point-cancel-left
           :in-theory (theory 'minimal-theory))))

(defthm curve-point-pair-output-point-cancel-right-client-regression
  (implies
   (and
    (short-weierstrass-characteristic-p)
    (short-weierstrass-curve-point-p a)
    (short-weierstrass-curve-point-p b)
    (short-weierstrass-curve-point-p c)
    (equal (curve-point-pair-output-point b a)
           (curve-point-pair-output-point c a)))
   (equal b c))
  :rule-classes nil
  :hints (("Goal" :use curve-point-pair-output-point-cancel-right
           :in-theory (theory 'minimal-theory))))
