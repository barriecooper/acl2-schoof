(in-package "GPOLY")

(include-book "square-free")
(include-book "derivative-regression")
(include-book "f7-division")

(defun f7-poly-square-free-p (polynomial)
  (declare (xargs :guard t))
  (equal
   (f7-poly-monic-euclidean-gcd
    polynomial
    (f7-poly-derivative polynomial))
   (f7-polynomial-one)))

(verify-guards f7-poly-square-free-p)

(defthm square-free-obstruction-minimal-theory-client
  (implies
   (poly-square-free-p polynomial)
   (not (poly-has-square-divisor-p polynomial divisor)))
  :hints
  (("Goal"
    :use ((:instance
           poly-square-free-p-implies-not-poly-has-square-divisor-p))
    :in-theory (theory 'minimal-theory))))

(defthm f7-poly-square-free-execution-regressions
  (and
   ; Zero, one, and a nonzero constant.
   (equal (f7-poly-square-free-p nil) nil)
   (equal (f7-poly-square-free-p (f7-polynomial-one)) t)
   (equal (f7-poly-square-free-p (f7-const 3)) t)
   ; x and x^2.
   (equal (f7-poly-square-free-p '(0 1)) t)
   (equal (f7-poly-square-free-p '(0 0 1)) nil)
   ; (x+1)^2 and (x+1)(x+2).
   (equal (f7-poly-square-free-p '(1 2 1)) nil)
   (equal (f7-poly-square-free-p '(2 3 1)) t)
   ; Characteristic-seven derivative-zero examples x^7 and x^7+1.
   (equal (f7-poly-derivative '(0 0 0 0 0 0 0 1)) nil)
   (equal (f7-poly-square-free-p '(0 0 0 0 0 0 0 1)) nil)
   (equal (f7-poly-derivative '(1 0 0 0 0 0 0 1)) nil)
   (equal (f7-poly-square-free-p '(1 0 0 0 0 0 0 1)) nil)
   ; The existing irreducible F7 modulus x^2+1 has nonzero derivative.
   (equal (f7-poly-square-free-p '(1 0 1)) t))
  :rule-classes nil)
