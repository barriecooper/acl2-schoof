(in-package "GPOLY")

(include-book "finite-field-fixed-modulus-carrier")
(include-book "finite-field-fixed-modulus-coefficients-regression")

(defthm finite-field-fixed-modulus-carrier-coverage-minimal-theory-client
  (member-equal (finite-field-fixed-modulus-reconstruct
                 (finite-field-fixed-modulus-coefficient-vector x modulus))
                (finite-field-fixed-modulus-elements modulus))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use member-equal-of-finite-field-fixed-modulus-fix-and-elements)))

(defthm finite-field-fixed-modulus-cardinality-minimal-theory-client
  (equal (finite-field-fixed-modulus-cardinality modulus)
         (finite-field-fixed-modulus-coefficient-vector-coding-bound modulus))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use finite-field-fixed-modulus-cardinality-equals-bound)))

(defthm finite-field-fixed-modulus-no-duplicates-minimal-theory-client
  (no-duplicatesp-equal (finite-field-fixed-modulus-elements modulus))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use no-duplicatesp-equal-of-finite-field-fixed-modulus-elements)))


(defun f7-carrier-coefficient-vector-unrank (width k)
  (declare (xargs :guard (natp width)
                  :measure (nfix width)))
  (if (zp (nfix width))
      nil
    (cons (gfield::f7-fix (mod (nfix k) 7))
          (f7-carrier-coefficient-vector-unrank
           (1- (nfix width))
           (floor (nfix k) 7)))))

(defun f7-fixed-modulus-coefficient-vector-coding-bound (modulus)
  (declare (xargs :guard t))
  (expt 7 (f7-fixed-modulus-coefficient-count modulus)))

(defun f7-fixed-modulus-coefficient-vector-unrank (modulus k)
  (declare (xargs :guard t))
  (f7-carrier-coefficient-vector-unrank
   (f7-fixed-modulus-coefficient-count modulus)
   k))

(defun f7-fixed-modulus-unrank (modulus k)
  (declare (xargs :guard t))
  (f7-fixed-modulus-reconstruct
   (f7-fixed-modulus-coefficient-vector-unrank modulus k)))

(defun f7-fixed-modulus-unrank-list (modulus indices)
  (declare (xargs :guard (true-listp indices)))
  (if (endp indices)
      nil
    (cons (f7-fixed-modulus-unrank modulus (car indices))
          (f7-fixed-modulus-unrank-list modulus (cdr indices)))))

(defun f7-fixed-modulus-elements (modulus)
  (declare (xargs :guard t))
  (f7-fixed-modulus-unrank-list
   modulus
   (gfield::finite-natural-range-from-count
    0 (f7-fixed-modulus-coefficient-vector-coding-bound modulus))))

(assert-event
 (and (equal (f7-fixed-modulus-coefficient-count '(1 0 1)) 2)
      (equal (f7-fixed-modulus-coefficient-vector-coding-bound '(1 0 1)) 49)
      (equal (len (f7-fixed-modulus-elements '(1 0 1))) 49)
      (no-duplicatesp-equal (f7-fixed-modulus-elements '(1 0 1)))
      (equal (f7-fixed-modulus-unrank '(1 0 1) 0) nil)
      (equal (f7-fixed-modulus-unrank '(1 0 1) 48) '(6 6))
      (equal (f7-fixed-modulus-reconstruct '(3 0)) '(3))
      (member-equal '(3) (f7-fixed-modulus-elements '(1 0 1)))
      (member-equal (f7-poly-remainder '(1 0 1) '(1 0 1))
                    (f7-fixed-modulus-elements '(1 0 1)))
      (member-equal (f7-poly-remainder '(5 4 3) '(1 0 1))
                    (f7-fixed-modulus-elements '(1 0 1)))
      (equal (f7-fixed-modulus-elements nil) (list nil))))

(verify-guards f7-carrier-coefficient-vector-unrank)
(verify-guards f7-fixed-modulus-coefficient-vector-coding-bound)
(verify-guards f7-fixed-modulus-coefficient-vector-unrank)
(verify-guards f7-fixed-modulus-unrank)
(verify-guards f7-fixed-modulus-unrank-list)
(verify-guards f7-fixed-modulus-elements)
