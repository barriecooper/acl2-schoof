(in-package "GPOLY")
(include-book "scale")

; Recursive shifted scaling, rather than a second coefficient-convolution
; implementation, reuses the already certified raw addition and scaling.
(def-mul-instance raw-mul poly-mul raw-add raw-scale normalize
                  gfield::field-zero)

(defthm raw-mul-when-atom-left
  (implies (atom x) (equal (raw-mul x y) nil)))

(defthm raw-mul-when-atom-right
  (implies (atom y) (equal (raw-mul x y) nil)))

(defthm raw-mul-of-cons
  (equal (raw-mul (cons a x) y)
         (if (consp y)
             (raw-add (raw-scale a y)
                      (cons (gfield::field-zero) (raw-mul x y)))
           nil)))

(defthm true-listp-of-raw-mul
  (true-listp (raw-mul x y)))

(defthm coefficient-list-p-of-raw-mul
  (coefficient-list-p (raw-mul x y)))

(defthm canonical-polynomial-p-of-poly-mul
  (canonical-polynomial-p (poly-mul x y)))

(defthm polynomial-p-of-poly-mul
  (polynomial-p (poly-mul x y)))

(defthm poly-mul-of-nil-left
  (equal (poly-mul nil x) nil))

(defthm poly-mul-of-nil-right
  (equal (poly-mul x nil) nil))

(defthm eval-of-zero-cons
  (equal (eval (cons (gfield::field-zero) poly) x)
         (gfield::field-mul x (eval poly x))))

(defthm eval-of-raw-mul
  (equal (eval (raw-mul f g) x)
         (gfield::field-mul (eval f x) (eval g x)))
  :hints (("Goal" :induct (raw-mul f g)
           :in-theory (enable gfield::field-mul-right-distributive
                              gfield::field-mul-associative
                              gfield::field-mul-commutative))))

(defthm eval-of-poly-mul
  (equal (eval (poly-mul f g) x)
         (gfield::field-mul (eval f x) (eval g x))))

(defthm poly-mul-normalize-left
  (equal (poly-mul (normalize x) y) (poly-mul x y)))

(defthm poly-mul-normalize-right
  (equal (poly-mul x (normalize y)) (poly-mul x y)))

(defthm poly-mul-fix-coefficients-left
  (equal (poly-mul (fix-coefficients x) y) (poly-mul x y)))

(defthm poly-mul-fix-coefficients-right
  (equal (poly-mul x (fix-coefficients y)) (poly-mul x y)))

(defcong equal equal (poly-mul x y) 1)
(defcong equal equal (poly-mul x y) 2)

(defthm raw-mul-of-one-left
  (equal (raw-mul (list (gfield::field-one)) x)
         (fix-coefficients x)))

(defthm raw-mul-by-singleton-right
  (equal (raw-mul x (list a)) (raw-scale a x))
  :hints (("Goal" :induct (raw-scale a x)
           :in-theory (enable gfield::field-mul-commutative))))

(defthm poly-mul-of-one-left
  (equal (poly-mul (list (gfield::field-one)) x) (normalize x)))

(defthm poly-mul-one-left-when-canonical
  (implies (canonical-polynomial-p x)
           (equal (poly-mul (list (gfield::field-one)) x) x)))

(defthm poly-mul-of-one-right
  (equal (poly-mul x (list (gfield::field-one))) (normalize x))
  :hints (("Goal" :in-theory (enable poly-mul poly-scale))))

(defthm poly-mul-one-right-when-canonical
  (implies (canonical-polynomial-p x)
           (equal (poly-mul x (list (gfield::field-one))) x)))
