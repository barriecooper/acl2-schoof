(in-package "GPOLY")
(include-book "fixed-modulus-field")
(include-book "coefficient")
(local (include-book "arithmetic-5/top" :dir :system))

; A reduced representative modulo a degree-n modulus has exactly n semantic
; coefficient slots.  The natural-number fixing is relevant only to the total
; definition: irreducibility makes the configured modulus degree positive.
(defun fixed-modulus-coefficient-count ()
  (declare (xargs :guard t))
  (nfix (poly-degree (normalize (fixed-modulus-field-modulus)))))

(defthm natp-of-fixed-modulus-coefficient-count
  (natp (fixed-modulus-coefficient-count))
  :rule-classes :type-prescription)

(defthm fixed-modulus-coefficient-count-definition
  (equal (fixed-modulus-coefficient-count)
         (poly-degree (normalize (fixed-modulus-field-modulus))))
  :hints
  (("Goal"
    :use (fixed-modulus-field-modulus-irreducible
          (:instance poly-irreducible-p-implies-positive-degree
                     (poly (fixed-modulus-field-modulus))))
    :in-theory (enable fixed-modulus-coefficient-count))))

(defthm posp-of-fixed-modulus-coefficient-count
  (posp (fixed-modulus-coefficient-count))
  :hints
  (("Goal"
    :use (fixed-modulus-field-modulus-irreducible
          (:instance poly-irreducible-p-implies-positive-degree
                     (poly (fixed-modulus-field-modulus))))
    :in-theory (enable fixed-modulus-coefficient-count))))

; The existing transparent fixer has guard T; this downstream execution book
; records its guard verification before using it from another guarded function.
(verify-guards fixed-modulus-field-fix)

; This is a single-pass zero-padding traversal.  It deliberately retains all
; COUNT slots, including final field zeroes; polynomial normalization is a
; separate operation below.
(defun fixed-modulus-coefficient-vector-aux (count polynomial)
  (declare (xargs :guard (natp count)
                  :measure (nfix count)))
  (if (zp (nfix count))
      nil
    (cons (if (consp polynomial)
              (gfield::field-fix (car polynomial))
            (gfield::field-zero))
          (fixed-modulus-coefficient-vector-aux
           (1- (nfix count))
           (if (consp polynomial) (cdr polynomial) nil)))))

(defun fixed-modulus-coefficient-vector (x)
  (declare (xargs :guard t))
  (fixed-modulus-coefficient-vector-aux
   (fixed-modulus-coefficient-count)
   (fixed-modulus-field-fix x)))

(defun fixed-modulus-reconstruct (coefficients)
  (declare (xargs :guard t))
  (normalize coefficients))

(defthm true-listp-of-fixed-modulus-coefficient-vector-aux
  (true-listp (fixed-modulus-coefficient-vector-aux count polynomial))
  :rule-classes :type-prescription)

(defthm len-of-fixed-modulus-coefficient-vector-aux
  (equal (len (fixed-modulus-coefficient-vector-aux count polynomial))
         (nfix count)))

(defthm true-listp-of-fixed-modulus-coefficient-vector
  (true-listp (fixed-modulus-coefficient-vector x))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fixed-modulus-coefficient-vector))))

(defthm len-of-fixed-modulus-coefficient-vector
  (equal (len (fixed-modulus-coefficient-vector x))
         (fixed-modulus-coefficient-count))
  :hints (("Goal" :in-theory (e/d (fixed-modulus-coefficient-vector)
                                    (fixed-modulus-coefficient-count-definition)))))

(local
 (defun fixed-modulus-coefficient-vector-projection-induction
     (index count polynomial)
   (declare (xargs :measure (nfix index)))
   (if (or (zp (nfix index)) (zp (nfix count)))
       (list index count polynomial)
     (fixed-modulus-coefficient-vector-projection-induction
      (1- (nfix index)) (1- (nfix count))
      (if (consp polynomial) (cdr polynomial) nil)))))

(local
 (defthm car-of-fixed-modulus-coefficient-vector-aux-when-positive
   (implies (posp (nfix count))
            (equal (car (fixed-modulus-coefficient-vector-aux count polynomial))
                   (poly-coefficient 0 polynomial)))
   :hints (("Goal" :in-theory (enable fixed-modulus-coefficient-vector-aux
                                      poly-coefficient)))))

(local
 (defthm nth-of-fixed-modulus-coefficient-vector-aux
   (implies (and (natp index)
                 (< index (nfix count)))
            (equal (nth index
                        (fixed-modulus-coefficient-vector-aux count polynomial))
                   (poly-coefficient index polynomial)))
   :hints
   (("Goal"
     :induct (fixed-modulus-coefficient-vector-projection-induction
              index count polynomial)
     :in-theory (enable poly-coefficient
                        fixed-modulus-coefficient-vector-aux)))))

(defthm nth-of-fixed-modulus-coefficient-vector-when-bounded
  (implies (and (natp index)
                (< index (fixed-modulus-coefficient-count)))
           (equal (nth index (fixed-modulus-coefficient-vector x))
                  (poly-coefficient index (fixed-modulus-field-fix x))))
  :hints (("Goal" :in-theory (enable fixed-modulus-coefficient-vector))))

(defthm field-element-p-of-nth-of-fixed-modulus-coefficient-vector
  (implies (and (natp index)
                (< index (fixed-modulus-coefficient-count)))
           (gfield::field-element-p
            (nth index (fixed-modulus-coefficient-vector x))))
  :hints
  (("Goal"
    :use ((:instance field-element-p-of-poly-coefficient
                     (n index) (polynomial (fixed-modulus-field-fix x)))))))

(defthm fixed-modulus-coefficient-vector-of-fix
  (equal (fixed-modulus-coefficient-vector (fixed-modulus-field-fix x))
         (fixed-modulus-coefficient-vector x))
  :hints
  (("Goal"
    :use fixed-modulus-field-fix-idempotent
    :in-theory (enable fixed-modulus-coefficient-vector))))

(defthm canonical-polynomial-p-of-fixed-modulus-reconstruct
  (canonical-polynomial-p (fixed-modulus-reconstruct coefficients))
  :hints (("Goal" :in-theory (enable fixed-modulus-reconstruct))))

(local
 (defthm canonical-polynomial-p-of-fixed-modulus-field-fix
   (canonical-polynomial-p (fixed-modulus-field-fix x))
   :hints
   (("Goal"
     :use ((:instance poly-remainder-canonical
                      (dividend x)
                      (modulus (fixed-modulus-field-modulus))))
     :in-theory (enable fixed-modulus-field-fix)))))

(local
 (defthm len-of-fixed-modulus-field-fix-at-most-coefficient-count
   (<= (len (fixed-modulus-field-fix x))
       (fixed-modulus-coefficient-count))
   :rule-classes :linear
   :hints
   (("Goal"
     :use (fixed-modulus-field-modulus-irreducible
           (:instance poly-irreducible-p-implies-normalize-nonzero
                      (poly (fixed-modulus-field-modulus)))
           (:instance poly-remainder-strict-length-bound
                      (dividend x)
                      (modulus (fixed-modulus-field-modulus)))
           (:instance poly-degree-when-canonical-nonzero
                      (p (normalize (fixed-modulus-field-modulus)))))
     :in-theory (enable fixed-modulus-field-fix
                        fixed-modulus-coefficient-count)))))

(local
 (defthm coefficient-list-p-of-fixed-modulus-coefficient-vector-aux
   (coefficient-list-p
    (fixed-modulus-coefficient-vector-aux count polynomial))
   :hints (("Goal" :induct
            (fixed-modulus-coefficient-vector-aux count polynomial)))))

(local
 (defthm normalize-of-padded-coefficient-list
   (implies (and (canonical-polynomial-p polynomial)
                 (<= (len polynomial) (nfix count)))
            (equal (normalize
                    (fixed-modulus-coefficient-vector-aux count polynomial))
                   polynomial))
   :hints
   (("Goal"
     :induct (fixed-modulus-coefficient-vector-aux count polynomial)
     :in-theory (enable normalize fix-coefficients trim-trailing-zeros
                        canonical-polynomial-p)))))

(defthm fixed-modulus-reconstruct-of-coefficient-vector
  (equal (fixed-modulus-reconstruct
          (fixed-modulus-coefficient-vector x))
         (fixed-modulus-field-fix x))
  :hints
  (("Goal"
    :use ((:instance canonical-polynomial-p-of-fixed-modulus-field-fix)
          (:instance len-of-fixed-modulus-field-fix-at-most-coefficient-count)
          (:instance normalize-of-padded-coefficient-list
                     (count (fixed-modulus-coefficient-count))
                     (polynomial (fixed-modulus-field-fix x))))
    :in-theory (e/d (fixed-modulus-reconstruct
                     fixed-modulus-coefficient-vector)
                    (fixed-modulus-coefficient-count-definition
                     fixed-modulus-field-fix poly-remainder normalize
                     canonical-polynomial-p)))))

(local
 (defthm same-coefficients-implies-equal-padded-vectors
   (implies (same-polynomial-coefficients-p count first second)
            (equal (fixed-modulus-coefficient-vector-aux count first)
                   (fixed-modulus-coefficient-vector-aux count second)))
   :hints
   (("Goal"
     :induct (same-polynomial-coefficients-p count first second)
     :in-theory (enable same-polynomial-coefficients-p poly-coefficient)))))

(defthm fixed-modulus-fix-coefficient-extensionality
  (implies
   (same-polynomial-coefficients-p
    (fixed-modulus-coefficient-count)
    (fixed-modulus-field-fix first)
    (fixed-modulus-field-fix second))
   (equal (fixed-modulus-field-fix first)
          (fixed-modulus-field-fix second)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance fixed-modulus-reconstruct-of-coefficient-vector (x first))
          (:instance fixed-modulus-reconstruct-of-coefficient-vector (x second))
          (:instance same-coefficients-implies-equal-padded-vectors
                     (count (fixed-modulus-coefficient-count))
                     (first (fixed-modulus-field-fix first))
                     (second (fixed-modulus-field-fix second))))
    :in-theory (enable fixed-modulus-coefficient-vector))))

(local
 (defthm equal-padded-vectors-implies-same-coefficients
   (implies
    (equal (fixed-modulus-coefficient-vector-aux count first)
           (fixed-modulus-coefficient-vector-aux count second))
    (same-polynomial-coefficients-p count first second))
   :hints
   (("Goal"
     :induct (same-polynomial-coefficients-p count first second)
     :in-theory (enable same-polynomial-coefficients-p poly-coefficient
                        fixed-modulus-coefficient-vector-aux)))))

(defthm fixed-modulus-fix-coefficient-vector-extensionality
  (implies
   (equal (fixed-modulus-coefficient-vector first)
          (fixed-modulus-coefficient-vector second))
   (equal (fixed-modulus-field-fix first)
          (fixed-modulus-field-fix second)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance fixed-modulus-fix-coefficient-extensionality)
          (:instance equal-padded-vectors-implies-same-coefficients
                     (count (fixed-modulus-coefficient-count))
                     (first (fixed-modulus-field-fix first))
                     (second (fixed-modulus-field-fix second))))
    :in-theory (enable fixed-modulus-coefficient-vector))))

(defthm fixed-modulus-coefficient-vector-extensionality
  (implies
   (and (fixed-modulus-field-element-p first)
        (fixed-modulus-field-element-p second)
        (equal (fixed-modulus-coefficient-vector first)
               (fixed-modulus-coefficient-vector second)))
   (equal first second))
  :rule-classes nil
  :hints
  (("Goal"
    :use (fixed-modulus-fix-coefficient-vector-extensionality
          (:instance fixed-modulus-field-fix-when-element-p (x first))
          (:instance fixed-modulus-field-fix-when-element-p (x second))))))

(verify-guards fixed-modulus-coefficient-count)
(verify-guards fixed-modulus-coefficient-vector-aux)
(verify-guards fixed-modulus-coefficient-vector)
(verify-guards fixed-modulus-reconstruct)
