(in-package "GPOLY")

(include-book "finite-field-reduction")
(local (include-book "arithmetic-5/top" :dir :system))

(defun finite-field-fixed-modulus-coefficient-count (modulus)
  (declare (xargs :guard t))
  (if (consp (finite-field-poly-normalize modulus))
      (1- (len (finite-field-poly-normalize modulus)))
    0))

(defthm natp-of-finite-field-fixed-modulus-coefficient-count
  (natp (finite-field-fixed-modulus-coefficient-count modulus))
  :rule-classes :type-prescription)

(defun finite-field-fixed-modulus-coefficient-vector-aux (count polynomial)
  (declare (xargs :guard (natp count)
                  :measure (nfix count)))
  (if (zp (nfix count))
      nil
    (cons (if (consp polynomial)
              (gfield::finite-field-fix (car polynomial))
            (gfield::finite-field-zero))
          (finite-field-fixed-modulus-coefficient-vector-aux
           (1- (nfix count))
           (if (consp polynomial) (cdr polynomial) nil)))))

(defun finite-field-fixed-modulus-coefficient-vector (x modulus)
  (declare (xargs :guard t))
  (finite-field-fixed-modulus-coefficient-vector-aux
   (finite-field-fixed-modulus-coefficient-count modulus)
   (finite-field-poly-remainder x modulus)))

(defun finite-field-fixed-modulus-reconstruct (coefficients)
  (declare (xargs :guard t))
  (finite-field-poly-normalize coefficients))

(defthm true-listp-of-finite-field-fixed-modulus-coefficient-vector-aux
  (true-listp (finite-field-fixed-modulus-coefficient-vector-aux count polynomial))
  :rule-classes :type-prescription)

(defthm len-of-finite-field-fixed-modulus-coefficient-vector-aux
  (equal (len (finite-field-fixed-modulus-coefficient-vector-aux count polynomial))
         (nfix count)))

(defthm len-of-finite-field-fixed-modulus-coefficient-vector
  (equal (len (finite-field-fixed-modulus-coefficient-vector x modulus))
         (finite-field-fixed-modulus-coefficient-count modulus))
  :hints (("Goal" :in-theory (enable finite-field-fixed-modulus-coefficient-vector))))

(local
 (defthm finite-field-coefficient-list-p-of-vector-aux
   (finite-field-coefficient-list-p
    (finite-field-fixed-modulus-coefficient-vector-aux count polynomial))
   :hints (("Goal" :induct
            (finite-field-fixed-modulus-coefficient-vector-aux count polynomial)
            :in-theory (enable finite-field-fixed-modulus-coefficient-vector-aux
                               finite-field-coefficient-list-p)))))

(defthm finite-field-coefficient-list-p-of-fixed-modulus-coefficient-vector
  (finite-field-coefficient-list-p
   (finite-field-fixed-modulus-coefficient-vector x modulus))
  :hints (("Goal" :in-theory (enable finite-field-fixed-modulus-coefficient-vector))))

(local
 (defthm finite-field-poly-coefficient-when-coefficient-list-p-and-bounded
   (implies (and (finite-field-coefficient-list-p coefficients)
                 (natp index)
                 (< index (len coefficients)))
            (equal (finite-field-poly-coefficient index coefficients)
                   (nth index coefficients)))
   :hints (("Goal" :induct (finite-field-poly-coefficient index coefficients)
            :in-theory (enable finite-field-poly-coefficient
                               finite-field-coefficient-list-p)))))

(defthm finite-field-poly-coefficient-of-fixed-modulus-reconstruct-when-bounded
  (implies (and (finite-field-coefficient-list-p coefficients)
                (natp index)
                (< index (len coefficients)))
           (equal (finite-field-poly-coefficient
                   index (finite-field-fixed-modulus-reconstruct coefficients))
                  (nth index coefficients)))
  :hints (("Goal" :use ((:instance finite-field-poly-coefficient-of-poly-normalize
                                   (n index) (polynomial coefficients))
                         (:instance finite-field-poly-coefficient-when-coefficient-list-p-and-bounded))
           :in-theory (enable finite-field-fixed-modulus-reconstruct))))

(defthm finite-field-canonical-polynomial-p-of-fixed-modulus-reconstruct
  (finite-field-canonical-polynomial-p
   (finite-field-fixed-modulus-reconstruct coefficients))
  :hints (("Goal" :use ((:instance finite-field-canonical-polynomial-p-of-poly-normalize
                                   (xs coefficients)))
           :in-theory (enable finite-field-fixed-modulus-reconstruct))))

(local
 (defthm normalize-of-padded-finite-field-coefficient-list
   (implies (and (finite-field-canonical-polynomial-p polynomial)
                 (<= (len polynomial) (nfix count)))
            (equal (finite-field-poly-normalize
                    (finite-field-fixed-modulus-coefficient-vector-aux count polynomial))
                   polynomial))
   :hints (("Goal" :induct (finite-field-fixed-modulus-coefficient-vector-aux count polynomial)
            :in-theory (enable finite-field-fixed-modulus-coefficient-vector-aux
                               finite-field-poly-normalize
                               finite-field-poly-fix-coefficients
                               finite-field-poly-trim-trailing-zeros
                               finite-field-canonical-polynomial-p)))))

(local
 (defthm len-of-finite-field-remainder-at-most-coefficient-count
   (implies (consp (finite-field-poly-normalize modulus))
            (<= (len (finite-field-poly-remainder x modulus))
                (finite-field-fixed-modulus-coefficient-count modulus)))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance finite-field-poly-remainder-strict-length-bound
                                    (dividend x)))
            :in-theory (enable finite-field-fixed-modulus-coefficient-count)))))

(defthm finite-field-fixed-modulus-reconstruct-of-coefficient-vector
  (implies (consp (finite-field-poly-normalize modulus))
           (equal (finite-field-fixed-modulus-reconstruct
                   (finite-field-fixed-modulus-coefficient-vector x modulus))
                  (finite-field-poly-remainder x modulus)))
  :hints (("Goal" :use ((:instance finite-field-poly-remainder-canonical
                                   (dividend x))
                         (:instance len-of-finite-field-remainder-at-most-coefficient-count)
                         (:instance normalize-of-padded-finite-field-coefficient-list
                                    (count (finite-field-fixed-modulus-coefficient-count modulus))
                                    (polynomial (finite-field-poly-remainder x modulus))))
           :in-theory (e/d (finite-field-fixed-modulus-reconstruct
                            finite-field-fixed-modulus-coefficient-vector)
                           (finite-field-poly-remainder
                            finite-field-poly-normalize
                            finite-field-canonical-polynomial-p)))) )

(defthm finite-field-fixed-modulus-coefficient-vector-of-remainder
  (equal (finite-field-fixed-modulus-coefficient-vector
          (finite-field-poly-remainder x modulus) modulus)
         (finite-field-fixed-modulus-coefficient-vector x modulus))
  :hints (("Goal" :use ((:instance finite-field-poly-remainder-idempotent
                                   (dividend x)))
           :in-theory (enable finite-field-fixed-modulus-coefficient-vector))))

(defthm finite-field-fixed-modulus-coefficient-vector-zero-normalized-modulus
  (implies (equal (finite-field-poly-normalize modulus) nil)
           (equal (finite-field-fixed-modulus-coefficient-vector x modulus)
                  nil))
  :hints (("Goal" :in-theory (enable finite-field-fixed-modulus-coefficient-vector
                                     finite-field-fixed-modulus-coefficient-vector-aux
                                     finite-field-fixed-modulus-coefficient-count
                                     finite-field-poly-degree))))

(defthm finite-field-fixed-modulus-reconstruct-of-coefficient-vector-zero-normalized-modulus
  (implies (equal (finite-field-poly-normalize modulus) nil)
           (equal (finite-field-fixed-modulus-reconstruct
                   (finite-field-fixed-modulus-coefficient-vector x modulus))
                  nil))
  :hints (("Goal" :in-theory (enable finite-field-fixed-modulus-reconstruct))))

(verify-guards finite-field-fixed-modulus-coefficient-count)
(verify-guards finite-field-fixed-modulus-coefficient-vector-aux)
(verify-guards finite-field-fixed-modulus-coefficient-vector)
(verify-guards finite-field-fixed-modulus-reconstruct)
