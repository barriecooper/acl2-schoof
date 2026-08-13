(in-package "GPOLY")

(include-book "base-ambient-context")
(include-book "remainder-evaluation")

; Dense ascending evaluation after embedding every existing GFIELD coefficient.
; Like EVAL, an atomic tail is discarded.
(defun ambient-eval (poly x)
  (if (atom poly)
      (gfield::ambient-zero)
    (gfield::ambient-add
     (gfield::base-to-ambient (car poly))
     (gfield::ambient-mul (gfield::ambient-fix x)
                          (ambient-eval (cdr poly) x)))))

(defthm ambient-eval-of-atom
  (implies (atom poly)
           (equal (ambient-eval poly x) (gfield::ambient-zero))))
(defthm ambient-eval-of-nil
  (equal (ambient-eval nil x) (gfield::ambient-zero)))
(defthm ambient-eval-of-ambient-fix
  (equal (ambient-eval poly (gfield::ambient-fix x))
         (ambient-eval poly x))
  :hints (("Goal" :induct (ambient-eval poly x)
           :in-theory (enable ambient-eval))))
(defthm ambient-fix-of-ambient-eval
  (equal (gfield::ambient-fix (ambient-eval poly x))
         (ambient-eval poly x)))

(defthm ambient-eval-of-fix-coefficients
  (equal (ambient-eval (fix-coefficients poly) x)
         (ambient-eval poly x))
  :hints (("Goal" :induct (fix-coefficients poly)
           :in-theory (enable fix-coefficients ambient-eval))))

(defthm ambient-eval-of-zero-cons
  (equal (ambient-eval (cons (gfield::field-zero) poly) x)
         (gfield::ambient-mul x (ambient-eval poly x))))

(local (defthm base-to-ambient-when-field-fix-zero
  (implies (equal (gfield::field-fix coefficient) (gfield::field-zero))
           (equal (gfield::base-to-ambient coefficient)
                  (gfield::ambient-zero)))
  :hints (("Goal" :use ((:instance gfield::base-to-ambient-fixed-congruence
                           (x coefficient) (y (gfield::field-zero)))
                          gfield::base-to-ambient-zero)))))

(defthm ambient-eval-of-trim-trailing-zeros
  (equal (ambient-eval (trim-trailing-zeros poly) x)
         (ambient-eval poly x))
  :hints (("Goal" :induct (trim-trailing-zeros poly)
           :in-theory (enable trim-trailing-zeros ambient-eval))))

(defthm ambient-eval-of-normalize
  (equal (ambient-eval (normalize poly) x) (ambient-eval poly x))
  :hints (("Goal" :in-theory (enable normalize))))

(defthm ambient-eval-of-zero
  (equal (ambient-eval nil x) (gfield::ambient-zero)))
(defthm ambient-eval-of-one
  (equal (ambient-eval (polynomial-one) x) (gfield::ambient-one)))

(defthm ambient-eval-of-raw-add
  (equal (ambient-eval (raw-add first second) x)
         (gfield::ambient-add (ambient-eval first x)
                              (ambient-eval second x)))
  :hints (("Goal" :induct (raw-add first second)
           :in-theory (enable raw-add ambient-eval
                              gfield::ambient-add-associative
                              gfield::ambient-add-commutative
                              gfield::ambient-add-interchange
                              gfield::ambient-mul-left-distributive))))
(defthm ambient-eval-of-poly-add
  (equal (ambient-eval (poly-add first second) x)
         (gfield::ambient-add (ambient-eval first x)
                              (ambient-eval second x))))

(defthm ambient-eval-of-raw-neg
  (equal (ambient-eval (raw-neg poly) x)
         (gfield::ambient-neg (ambient-eval poly x)))
  :hints (("Goal" :induct (raw-neg poly)
           :in-theory (enable raw-neg ambient-eval))))
(defthm ambient-eval-of-poly-neg
  (equal (ambient-eval (poly-neg poly) x)
         (gfield::ambient-neg (ambient-eval poly x))))
(defthm ambient-eval-of-poly-sub
  (equal (ambient-eval (poly-sub first second) x)
         (gfield::ambient-sub (ambient-eval first x)
                              (ambient-eval second x)))
  :hints (("Goal" :in-theory (enable poly-sub gfield::ambient-sub))))

(defthm ambient-eval-of-raw-scale
  (equal (ambient-eval (raw-scale coefficient poly) x)
         (gfield::ambient-mul (gfield::base-to-ambient coefficient)
                              (ambient-eval poly x)))
  :hints (("Goal" :induct (raw-scale coefficient poly)
           :in-theory (enable raw-scale ambient-eval
                              gfield::ambient-mul-right-distributive
                              gfield::ambient-mul-associative
                              gfield::ambient-mul-commutative
                              gfield::ambient-mul-interchange))))
(defthm ambient-eval-of-raw-mul
  (equal (ambient-eval (raw-mul first second) x)
         (gfield::ambient-mul (ambient-eval first x)
                              (ambient-eval second x)))
  :hints (("Goal" :induct (raw-mul first second)
           :in-theory (enable raw-mul ambient-eval
                              gfield::ambient-mul-right-distributive
                              gfield::ambient-mul-associative
                              gfield::ambient-mul-commutative))))
(defthm ambient-eval-of-poly-mul
  (equal (ambient-eval (poly-mul first second) x)
         (gfield::ambient-mul (ambient-eval first x)
                              (ambient-eval second x))))

(local
 (defthm ambient-eval-of-poly-divmod-reconstruction-congruence
  (equal
   (ambient-eval
    (poly-add
     (poly-mul (mv-nth 0 (poly-divmod polynomial modulus))
               (normalize modulus))
     (mv-nth 1 (poly-divmod polynomial modulus))) x)
   (ambient-eval (normalize polynomial) x))
  :rule-classes nil
  :hints (("Goal" :use ((:instance poly-divmod-reconstruction
                                   (f polynomial) (g modulus)))
           :in-theory (theory 'minimal-theory)))))

(local
 (defthm ambient-eval-of-poly-divmod-reconstruction
  (equal
   (gfield::ambient-add
    (gfield::ambient-mul
     (ambient-eval (mv-nth 0 (poly-divmod polynomial modulus)) x)
     (ambient-eval modulus x))
    (ambient-eval (mv-nth 1 (poly-divmod polynomial modulus)) x))
   (ambient-eval polynomial x))
  :rule-classes nil
  :hints (("Goal"
           :use (ambient-eval-of-poly-divmod-reconstruction-congruence)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(ambient-eval-of-poly-add
                         ambient-eval-of-poly-mul
                         ambient-eval-of-normalize))))))

(defthm ambient-eval-of-poly-remainder-at-root
  (implies (equal (ambient-eval modulus x) (gfield::ambient-zero))
           (equal (ambient-eval (poly-remainder polynomial modulus) x)
                  (ambient-eval polynomial x)))
  :rule-classes nil
  :hints (("Goal"
           :use (ambient-eval-of-poly-divmod-reconstruction
                 (:instance poly-remainder-is-divmod-remainder
                            (dividend polynomial)))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(gfield::ambient-mul-zero-right
                         gfield::ambient-add-zero-left
                         ambient-fix-of-ambient-eval)))))

(verify-guards ambient-eval)
