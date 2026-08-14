(in-package "GPOLY")
(include-book "finite-field-factor-degree-bound")
(include-book "f11-production-euclidean-stack")

; F11 is concrete execution coverage only; the factor theorem is owned above.
(defthm f11-linear-times-cubic-product-regression
  (equal (f11-poly-mul '(1 1) '(1 0 0 1)) '(1 1 0 1 1)))

(defthm f11-quadratic-times-quadratic-product-regression
  (equal (f11-poly-mul '(1 0 1) '(1 0 1)) '(1 0 2 0 1)))

(defthm f11-linear-divides-explicit-quartic-regression
  (f11-poly-divides-p '(1 1) '(1 1 0 1 1)))

(defthm f11-quadratic-divides-explicit-quartic-regression
  (f11-poly-divides-p '(1 0 1) '(1 0 2 0 1)))

(defthm f11-monic-degree-totalized-regression
  (and (equal (f11-poly-degree (f11-poly-monic-normalize '(2 4 3))) 2)
       (equal (f11-poly-degree (f11-poly-monic-normalize '(13 4 3))) 2)
       (equal (f11-poly-degree (f11-poly-monic-normalize '(2 4 3 0))) 2)
       (equal (f11-poly-degree
               (f11-poly-monic-normalize '(2 4 3 . tail))) 2))
  :rule-classes nil)

(defthm f11-factor-examples-have-degree-four-regression
  (and (equal (f11-poly-degree '(1 1 0 1 1)) 4)
       (equal (f11-poly-degree '(1 0 2 0 1)) 4))
  :rule-classes nil)
