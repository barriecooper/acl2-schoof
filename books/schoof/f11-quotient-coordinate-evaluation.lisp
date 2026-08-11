(in-package "GPOLY")

(include-book "f11-quotient-coordinate")
(include-book "f11-third-division-polynomial")

; The maintained index-3 division polynomial is used as the quotient modulus;
; this is only a coordinate-ring annihilation statement.
(defthm f11-golden-psi3-eval-at-universal-x
  (let ((modulus (f11-division-polynomial 3 1 6)))
    (equal
     (f11-quotient-coordinate-eval
      modulus (f11-quotient-coordinate-x modulus) 1 6 modulus)
     (f11-quotient-coordinate-zero modulus)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  f11-quotient-coordinate-modulus-eval-at-universal-x
                  (modulus (f11-division-polynomial 3 1 6))
                  (a 1) (b 6)))
           :in-theory (theory 'minimal-theory))))

; This spelling is composed through the maintained coefficient theorem rather
; than by repeating the quartic coefficient calculation.
(defthm f11-golden-literal-psi3-eval-at-universal-x
  (equal
   (f11-quotient-coordinate-eval
    '(10 6 6 0 3)
    (f11-quotient-coordinate-x '(10 6 6 0 3))
    1 6 '(10 6 6 0 3))
   (f11-quotient-coordinate-zero '(10 6 6 0 3)))
  :rule-classes nil
  :hints (("Goal"
           :use (f11-golden-division-polynomial-index-3
                 f11-golden-psi3-eval-at-universal-x)
           :in-theory (theory 'minimal-theory))))
