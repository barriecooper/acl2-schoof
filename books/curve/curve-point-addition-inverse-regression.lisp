(in-package "GFIELD")

(include-book "curve-point-addition-inverse")

; Each client theorem deliberately exposes only its corresponding public
; boundary over MINIMAL-THEORY.
(defthm curve-point-neg-canonical-client-regression
  (equal (curve-point-fix (curve-point-neg point))
         (curve-point-neg point))
  :hints (("Goal" :use curve-point-fix-of-neg
           :in-theory (theory 'minimal-theory))))

(defthm curve-point-neg-fixing-client-regression
  (equal (curve-point-neg (curve-point-fix point))
         (curve-point-neg point))
  :hints (("Goal" :use curve-point-neg-of-fix
           :in-theory (theory 'minimal-theory))))

(defthm curve-point-neg-closure-client-regression
  (implies (short-weierstrass-curve-point-p point)
           (short-weierstrass-curve-point-p (curve-point-neg point)))
  :rule-classes nil
  :hints (("Goal" :use short-weierstrass-curve-point-p-of-neg
           :in-theory (theory 'minimal-theory))))

(defthm curve-point-neg-involution-client-regression
  (equal (curve-point-neg (curve-point-neg point))
         (curve-point-fix point))
  :hints (("Goal" :use curve-point-neg-of-neg
           :in-theory (theory 'minimal-theory))))

(defthm curve-point-identity-left-client-regression
  (implies (short-weierstrass-curve-point-p point)
           (equal (curve-point-pair-output-point
                   (curve-point-infinity) point)
                  point))
  :rule-classes nil
  :hints (("Goal" :use curve-point-pair-output-point-identity-left
           :in-theory (theory 'minimal-theory))))

(defthm curve-point-identity-right-client-regression
  (implies (short-weierstrass-curve-point-p point)
           (equal (curve-point-pair-output-point
                   point (curve-point-infinity))
                  point))
  :rule-classes nil
  :hints (("Goal" :use curve-point-pair-output-point-identity-right
           :in-theory (theory 'minimal-theory))))

(defthm curve-point-inverse-right-client-regression
  (implies (short-weierstrass-curve-point-p point)
           (equal (curve-point-pair-output-point
                   point (curve-point-neg point))
                  (curve-point-infinity)))
  :rule-classes nil
  :hints (("Goal" :use curve-point-pair-output-point-with-negate-right
           :in-theory (theory 'minimal-theory))))

(defthm curve-point-inverse-left-client-regression
  (implies (short-weierstrass-curve-point-p point)
           (equal (curve-point-pair-output-point
                   (curve-point-neg point) point)
                  (curve-point-infinity)))
  :rule-classes nil
  :hints (("Goal" :use curve-point-pair-output-point-with-negate-left
           :in-theory (theory 'minimal-theory))))
