(in-package "GPOLY")
(include-book "fixed-modulus-coefficients")
(include-book "f7x2-fixed-modulus-field-regression")

; Concrete F7X2 proving client for the generic representation.  These local
; functions are the direct F7 images required by functional instantiation; the
; public concrete API remains the existing F7X2 projection pair.
(local (defun f7x2-coefficient-regression-modulus () '(1 0 1)))

(local
 (defthm f7x2-coefficient-regression-modulus-irreducible
   (f7-poly-irreducible-p (f7x2-coefficient-regression-modulus))
   :rule-classes nil
   :hints (("Goal" :use f7-x-squared-plus-one-is-irreducible
            :in-theory (disable f7-poly-irreducible-p
                                f7-poly-reducible-p)))))

(local
 (defun f7-poly-coefficient-for-coefficient-regression (n polynomial)
   (declare (xargs :measure (nfix n)))
   (if (zp (nfix n))
       (if (consp polynomial)
           (gfield::f7-fix (car polynomial))
         (gfield::f7-zero))
     (f7-poly-coefficient-for-coefficient-regression
      (1- (nfix n))
      (if (consp polynomial) (cdr polynomial) nil)))))

(local
 (defun f7-same-polynomial-coefficients-p-for-regression
     (count first second)
   (if (zp (nfix count))
       t
     (and (equal (f7-poly-coefficient-for-coefficient-regression 0 first)
                 (f7-poly-coefficient-for-coefficient-regression 0 second))
          (f7-same-polynomial-coefficients-p-for-regression
           (1- (nfix count))
           (if (consp first) (cdr first) nil)
           (if (consp second) (cdr second) nil))))))

(local
 (defun f7x2-coefficient-count-for-regression ()
   (nfix (f7-poly-degree
          (f7-normalize (f7x2-coefficient-regression-modulus))))))

(local
 (defun f7x2-coefficient-vector-aux-for-regression (count polynomial)
   (declare (xargs :measure (nfix count)))
   (if (zp (nfix count))
       nil
     (cons (if (consp polynomial)
               (gfield::f7-fix (car polynomial))
             (gfield::f7-zero))
           (f7x2-coefficient-vector-aux-for-regression
            (1- (nfix count))
            (if (consp polynomial) (cdr polynomial) nil))))))

(local
 (defun f7x2-coefficient-vector-for-regression (x)
   (f7x2-coefficient-vector-aux-for-regression
    (f7x2-coefficient-count-for-regression)
    (f7x2-fix x))))

(local
 (defun f7x2-reconstruct-for-regression (coefficients)
   (f7-normalize coefficients)))

(local
 (defthm f7x2-fixed-modulus-coefficient-count-equals-two
  (equal (f7x2-coefficient-count-for-regression) 2)
  :hints (("Goal" :in-theory
           (enable f7x2-coefficient-count-for-regression
                   f7x2-coefficient-regression-modulus
                   f7-poly-degree f7-normalize f7-fix-coefficients
                   f7-trim-trailing-zeros)))))

(local
 (defthm f7x2-coefficient-vector-aux-two
   (equal (f7x2-coefficient-vector-aux-for-regression 2 polynomial)
          (list (gfield::f7-fix (car polynomial))
                (gfield::f7-fix (cadr polynomial))))
   :hints (("Goal" :cases ((consp polynomial) (consp (cdr polynomial)))
            :in-theory (enable f7x2-coefficient-vector-aux-for-regression
                               gfield::f7-zero)))))

(local
 (defthm f7x2-fixed-modulus-coefficient-vector-is-projection-pair
  (equal (f7x2-coefficient-vector-for-regression x)
         (list (f7x2-constant-coefficient x)
               (f7x2-linear-coefficient x)))
  :hints
  (("Goal"
    :use (f7x2-fixed-modulus-coefficient-count-equals-two
          (:instance f7x2-coefficient-vector-aux-two
                     (polynomial (f7x2-fix x))))
    :in-theory (e/d (f7x2-coefficient-vector-for-regression
                     f7x2-constant-coefficient f7x2-linear-coefficient)
                    (f7x2-coefficient-count-for-regression
                     f7x2-coefficient-vector-aux-for-regression
                     f7x2-fix f7-poly-remainder))))))

; This direct specialization is also the concrete execution-facing statement;
; the generic theorem independently supplies its representation proof.
(local
 (defthm f7x2-fixed-modulus-reconstruct-of-coefficient-vector
  (equal (f7x2-reconstruct-for-regression
          (f7x2-coefficient-vector-for-regression x))
         (f7x2-fix x))
  :hints (("Goal"
           :use ((:instance f7x2-reconstruct-from-coefficients
                            (value (f7x2-fix x)))
                 (:instance f7x2-element-p-of-f7x2-fix)
                 (:instance f7x2-fix-idempotent)
                 (:instance
                  f7x2-fixed-modulus-coefficient-vector-is-projection-pair))
           :in-theory (e/d (f7x2-reconstruct-for-regression)
                           (f7x2-fix f7-normalize
                            f7x2-coefficient-vector-for-regression
                            f7x2-constant-coefficient
                            f7x2-linear-coefficient))))))

(local
 (defthm f7x2-fixed-modulus-coefficient-vector-extensionality
  (implies
   (equal (f7x2-coefficient-vector-for-regression first)
          (f7x2-coefficient-vector-for-regression second))
   (equal (f7x2-fix first) (f7x2-fix second)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance f7x2-fix-coefficient-extensionality)
          (:instance f7x2-fixed-modulus-coefficient-vector-is-projection-pair
                     (x first))
          (:instance f7x2-fixed-modulus-coefficient-vector-is-projection-pair
                     (x second)))
    :in-theory (disable f7x2-fix f7x2-coefficient-vector-for-regression
                        f7x2-constant-coefficient
                        f7x2-linear-coefficient)))))

(local (verify-guards f7-poly-coefficient-for-coefficient-regression))
(local (verify-guards f7-same-polynomial-coefficients-p-for-regression))
(local (verify-guards f7x2-coefficient-regression-modulus))
(local (verify-guards f7x2-coefficient-count-for-regression))
(local (verify-guards f7x2-coefficient-vector-aux-for-regression))
(local (verify-guards f7x2-coefficient-vector-for-regression))
(local (verify-guards f7x2-reconstruct-for-regression))

(local
 (assert-event
 (and (equal (f7x2-coefficient-vector-for-regression nil) '(0 0))
      (equal (f7x2-coefficient-vector-for-regression '(1)) '(1 0))
      (equal (f7x2-coefficient-vector-for-regression '(3)) '(3 0))
      (equal (f7x2-coefficient-vector-for-regression '(3 4)) '(3 4))
      (equal (f7x2-coefficient-vector-for-regression '(0 0 1)) '(6 0))
      (equal (f7x2-coefficient-vector-for-regression '(bad 9 also-bad)) '(0 2))
      (equal (f7x2-coefficient-vector-for-regression '(1 2 . bad-tail)) '(1 2))
      (equal (f7x2-coefficient-vector-for-regression '(3 0 0)) '(3 0))
      (equal (f7x2-coefficient-vector-for-regression 'malformed) '(0 0))
      (equal (f7x2-reconstruct-for-regression '(3 0)) '(3))))
)
