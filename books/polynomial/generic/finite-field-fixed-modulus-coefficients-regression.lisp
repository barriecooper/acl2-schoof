(in-package "GPOLY")

(include-book "finite-field-fixed-modulus-coefficients")
(include-book "f7-division")

(defthm finite-field-fixed-modulus-vector-minimal-theory-client
  (implies (consp (finite-field-poly-normalize modulus))
           (equal (finite-field-fixed-modulus-reconstruct
                   (finite-field-fixed-modulus-coefficient-vector x modulus))
                  (finite-field-poly-remainder x modulus)))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use finite-field-fixed-modulus-reconstruct-of-coefficient-vector)))


(defthm finite-field-fixed-modulus-vector-round-trip-minimal-theory-client
  (implies
   (and (consp (finite-field-poly-normalize modulus))
        (finite-field-coefficient-list-p coefficients)
        (equal (len coefficients)
               (finite-field-fixed-modulus-coefficient-count modulus)))
   (equal (finite-field-fixed-modulus-coefficient-vector
           (finite-field-fixed-modulus-reconstruct coefficients) modulus)
          coefficients))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use finite-field-fixed-modulus-coefficient-vector-of-reconstruct)))

(defthm finite-field-fixed-modulus-zero-modulus-minimal-theory-client
  (implies (equal (finite-field-poly-normalize modulus) nil)
           (equal (finite-field-fixed-modulus-coefficient-vector x modulus)
                  nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use finite-field-fixed-modulus-coefficient-vector-zero-normalized-modulus)))

(defun f7-fixed-modulus-coefficient-count (modulus)
  (if (consp (f7-normalize modulus))
      (1- (len (f7-normalize modulus)))
    0))

(defun f7-fixed-modulus-coefficient-vector-aux (count polynomial)
  (declare (xargs :guard (natp count)
                  :measure (nfix count)))
  (if (zp (nfix count))
      nil
    (cons (if (consp polynomial)
              (gfield::f7-fix (car polynomial))
            (gfield::f7-zero))
          (f7-fixed-modulus-coefficient-vector-aux
           (1- (nfix count))
           (if (consp polynomial) (cdr polynomial) nil)))))

(defun f7-fixed-modulus-coefficient-vector (x modulus)
  (f7-fixed-modulus-coefficient-vector-aux
   (f7-fixed-modulus-coefficient-count modulus)
   (f7-poly-remainder x modulus)))

(defun f7-fixed-modulus-reconstruct (coefficients)
  (f7-normalize coefficients))

(assert-event
 (and (equal (f7-fixed-modulus-coefficient-count '(1 0 1)) 2)
      (equal (f7-fixed-modulus-coefficient-vector nil '(1 0 1)) '(0 0))
      (equal (f7-fixed-modulus-coefficient-vector '(3) '(1 0 1)) '(3 0))
      (equal (f7-fixed-modulus-coefficient-vector '(3 4) '(1 0 1)) '(3 4))
      (equal (f7-fixed-modulus-coefficient-vector '(0 0 1) '(1 0 1)) '(6 0))
      (equal (f7-fixed-modulus-coefficient-vector '(bad 9 also-bad) '(1 0 1)) '(0 2))
      (equal (f7-fixed-modulus-coefficient-vector '(1 2 . bad-tail) '(1 0 1)) '(1 2))
      (equal (f7-fixed-modulus-reconstruct '(3 0)) '(3))
      (equal (f7-fixed-modulus-coefficient-vector
              (f7-fixed-modulus-reconstruct '(3 0)) '(1 0 1))
             '(3 0))
      (equal (f7-fixed-modulus-coefficient-vector 'malformed '(1 0 1)) '(0 0))
      (equal (f7-fixed-modulus-coefficient-vector '(1 2 3) nil) nil)
      (equal (f7-fixed-modulus-reconstruct
              (f7-fixed-modulus-coefficient-vector '(1 2 3) nil))
             nil)))

(verify-guards f7-fixed-modulus-coefficient-count)
(verify-guards f7-fixed-modulus-coefficient-vector-aux)
(verify-guards f7-fixed-modulus-coefficient-vector)
(verify-guards f7-fixed-modulus-reconstruct)
