(in-package "GPOLY")

(include-book "f11-production-reduced-ring")
(include-book "../../schoof/f11-division-polynomial")

(defun f11-psi3-modulus ()
  (f11-division-polynomial 3 1 6))

(defthm f11-psi3-modulus-exact
  (equal (f11-psi3-modulus) '(10 6 6 0 3)))

(defthm f11-psi3-modulus-canonical-and-nonzero
  (and (f11-canonical-polynomial-p (f11-psi3-modulus))
       (consp (f11-psi3-modulus))))

(defthm f11-psi3-production-reduction-regressions
  (let* ((m (f11-psi3-modulus))
         (m+1 (f11-poly-add m '(1)))
         (m+2 (f11-poly-add m '(2))))
    (and (equal (f11-normalize '(21 -5 17 0 14 0)) '(10 6 6 0 3))
         (equal (f11-poly-remainder nil m) nil)
         (equal (f11-poly-remainder '(3 4) m) '(3 4))
         (equal (f11-poly-remainder m m) nil)
         (equal (f11-poly-quotient m m) '(1))
         (equal (f11-poly-remainder 'malformed m) nil)
         (equal (f11-poly-remainder '(1 2 . malformed) m) '(1 2))
         (equal (f11-poly-remainder '(1 2) nil) '(1 2))
         (equal (f11-poly-remainder '(1 2) 'malformed) '(1 2))
         (equal (f11-poly-reduced-add m+1 m+2 m) '(3))
         (equal (f11-poly-reduced-neg m+1 m) '(10))
         (equal (f11-poly-reduced-sub m+1 m+2 m) '(10))
         (equal (f11-poly-reduced-mul m+1 m+2 m) '(2))
         (equal (f11-poly-reduced-one m) '(1)))))

(verify-guards f11-psi3-modulus)
