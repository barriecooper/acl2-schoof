(in-package "GFIELD")

(include-book "pfield-adapter")

; A small project-local half-open natural range avoids importing the broad VL
; utility dependency closure merely for elementary finite-list facts.
(defun pfield-natural-range-from-count (start count)
  (declare (xargs :guard (and (natp start) (natp count))
                  :measure (nfix count)))
  (if (zp (nfix count))
      nil
    (cons (nfix start)
          (pfield-natural-range-from-count (+ 1 (nfix start))
                                           (1- (nfix count))))))

(defthm true-listp-of-pfield-natural-range-from-count
  (true-listp (pfield-natural-range-from-count start count))
  :rule-classes :type-prescription)

(defthm member-equal-of-pfield-natural-range-from-count
  (iff (member-equal x (pfield-natural-range-from-count start count))
       (and (natp x)
            (<= (nfix start) x)
            (< x (+ (nfix start) (nfix count)))))
  :hints (("Goal" :induct (pfield-natural-range-from-count start count)
           :in-theory (enable pfield-natural-range-from-count))))

(defthm no-duplicatesp-equal-of-pfield-natural-range-from-count
  (no-duplicatesp-equal (pfield-natural-range-from-count start count))
  :hints (("Goal" :induct (pfield-natural-range-from-count start count)
           :in-theory (enable pfield-natural-range-from-count))))

(defthm len-of-pfield-natural-range-from-count
  (equal (len (pfield-natural-range-from-count start count))
         (nfix count))
  :hints (("Goal" :induct (pfield-natural-range-from-count start count)
           :in-theory (enable pfield-natural-range-from-count))))

(verify-guards pfield-natural-range-from-count)

; Ascending canonical representatives for the half-open interval [0,p).
(defun pfield-elements ()
  (declare (xargs :guard t))
  (pfield-natural-range-from-count 0 (pfield-modulus)))

; Cardinality is definitionally tied to the certified finite carrier witness.
(defun pfield-cardinality ()
  (declare (xargs :guard t))
  (len (pfield-elements)))

(defthm true-listp-of-pfield-elements
  (true-listp (pfield-elements))
  :rule-classes :type-prescription)

(defthm member-equal-of-pfield-elements
  (iff (member-equal x (pfield-elements))
       (and (natp x)
            (< x (pfield-modulus))))
  :hints (("Goal" :in-theory (enable pfield-elements))))

(defthm no-duplicatesp-equal-of-pfield-elements
  (no-duplicatesp-equal (pfield-elements))
  :hints (("Goal" :in-theory (enable pfield-elements))))

(defthm pfield-element-p-of-member-equal-of-pfield-elements
  (implies (member-equal x (pfield-elements))
           (pfield-element-p x))
  :hints (("Goal" :in-theory (enable pfield-element-p pfield::fep))))

(defthm pfield-fix-when-member-equal-of-pfield-elements
  (implies (member-equal x (pfield-elements))
           (equal (pfield-fix x) x))
  :hints (("Goal" :use pfield-element-p-of-member-equal-of-pfield-elements
           :in-theory (disable pfield-elements))))

(defthm member-equal-of-pfield-fix-and-pfield-elements
  (member-equal (pfield-fix x) (pfield-elements))
  :hints (("Goal"
           :use ((:instance pfield-fep-of-pfield-fix))
           :in-theory (enable member-equal-of-pfield-elements
                              pfield::fep))))

(defthm len-of-pfield-elements
  (equal (len (pfield-elements)) (pfield-modulus))
  :hints (("Goal" :in-theory (enable pfield-elements))))

(defthm pfield-cardinality-equals-len-of-pfield-elements
  (equal (pfield-cardinality) (len (pfield-elements)))
  :hints (("Goal" :in-theory (enable pfield-cardinality))))

(defthm pfield-cardinality-equals-modulus
  (equal (pfield-cardinality) (pfield-modulus))
  :hints (("Goal" :use len-of-pfield-elements
           :in-theory (enable pfield-cardinality))))

(defthm posp-of-pfield-cardinality
  (posp (pfield-cardinality))
  :hints (("Goal" :use (pfield-cardinality-equals-modulus
                         pfield-modulus-lower-bound))))

(verify-guards pfield-elements)
(verify-guards pfield-cardinality)
