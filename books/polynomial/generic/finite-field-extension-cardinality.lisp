(in-package "GPOLY")

(include-book "finite-field-fixed-modulus-carrier")

; This book is deliberately only the cardinality-facing bridge for the
; explicit finite-field-prefixed fixed-modulus representative layer.  The
; representative count below does not assert field laws; clients that need a
; field must separately instantiate the irreducible fixed-modulus field package.

(defun finite-field-extension-representative-count (modulus)
  (declare (xargs :guard t))
  (finite-field-fixed-modulus-cardinality modulus))

(defun finite-field-extension-representatives (modulus)
  (declare (xargs :guard t))
  (finite-field-fixed-modulus-elements modulus))

(defthm member-equal-of-finite-field-extension-fix-and-representatives
  (member-equal (finite-field-fixed-modulus-reconstruct
                 (finite-field-fixed-modulus-coefficient-vector x modulus))
                (finite-field-extension-representatives modulus))
  :rule-classes nil
  :hints (("Goal"
           :use member-equal-of-finite-field-fixed-modulus-fix-and-elements
           :in-theory (enable finite-field-extension-representatives))))

(defthm no-duplicatesp-equal-of-finite-field-extension-representatives
  (no-duplicatesp-equal (finite-field-extension-representatives modulus))
  :rule-classes nil
  :hints (("Goal"
           :use no-duplicatesp-equal-of-finite-field-fixed-modulus-elements
           :in-theory (enable finite-field-extension-representatives))))

(defthm len-of-finite-field-extension-representatives
  (equal (len (finite-field-extension-representatives modulus))
         (finite-field-fixed-modulus-coefficient-vector-coding-bound modulus))
  :hints (("Goal" :in-theory (enable finite-field-extension-representatives))))

(defthm finite-field-extension-representative-count-equals-len
  (equal (finite-field-extension-representative-count modulus)
         (len (finite-field-extension-representatives modulus)))
  :hints (("Goal" :in-theory (enable finite-field-extension-representative-count
                                     finite-field-extension-representatives
                                     finite-field-fixed-modulus-cardinality))))

(defthm finite-field-extension-representative-count-equals-coding-bound
  (equal (finite-field-extension-representative-count modulus)
         (finite-field-fixed-modulus-coefficient-vector-coding-bound modulus))
  :hints (("Goal" :in-theory (enable finite-field-extension-representative-count))))

(defthm finite-field-extension-representative-count-equals-radix-power
  (equal (finite-field-extension-representative-count modulus)
         (expt (nfix (gfield::finite-field-bound))
               (finite-field-fixed-modulus-coefficient-count modulus)))
  :hints (("Goal" :in-theory (enable finite-field-extension-representative-count
                                     finite-field-fixed-modulus-coefficient-vector-coding-bound
                                     finite-field-coefficient-vector-coding-bound))))

(defthm finite-field-fixed-modulus-coefficient-count-when-normalized-nonzero
  (implies (consp (finite-field-poly-normalize modulus))
           (equal (finite-field-fixed-modulus-coefficient-count modulus)
                  (finite-field-poly-degree
                   (finite-field-poly-normalize modulus))))
  :hints (("Goal"
           :use ((:instance finite-field-canonical-polynomial-p-of-poly-normalize
                            (xs modulus))
                 (:instance finite-field-poly-degree-when-canonical-nonzero
                            (p (finite-field-poly-normalize modulus))))
           :in-theory (enable finite-field-fixed-modulus-coefficient-count))))

(defthm finite-field-extension-representative-count-equals-degree-power
  (implies (consp (finite-field-poly-normalize modulus))
           (equal (finite-field-extension-representative-count modulus)
                  (expt (nfix (gfield::finite-field-bound))
                        (finite-field-poly-degree
                         (finite-field-poly-normalize modulus)))))
  :hints (("Goal"
           :use finite-field-fixed-modulus-coefficient-count-when-normalized-nonzero
           :in-theory (disable finite-field-fixed-modulus-coefficient-count-when-normalized-nonzero))))

(defthm finite-field-extension-representative-count-zero-normalized-modulus
  (implies (equal (finite-field-poly-normalize modulus) nil)
           (equal (finite-field-extension-representative-count modulus) 1))
  :hints (("Goal" :in-theory (enable finite-field-extension-representative-count
                                     finite-field-fixed-modulus-cardinality
                                     finite-field-fixed-modulus-elements-zero-normalized-modulus))))

(verify-guards finite-field-extension-representative-count)
(verify-guards finite-field-extension-representatives)
