(in-package "GPOLY")

(include-book "finite-field-coefficient-vector-coding")
(include-book "../../algebra/finite-bijection")
(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm consp-when-positive-len-local
   (implies (< 0 (len x))
            (consp x))))

(local
 (defthm not-consp-when-zero-len-local
   (implies (equal (len x) 0)
            (not (consp x)))))

(defun finite-field-fixed-modulus-unrank (modulus k)
  (declare (xargs :guard t))
  (finite-field-fixed-modulus-reconstruct
   (finite-field-fixed-modulus-coefficient-vector-unrank modulus k)))

(defun finite-field-fixed-modulus-unrank-list (modulus indices)
  (declare (xargs :guard (true-listp indices)))
  (if (endp indices)
      nil
    (cons (finite-field-fixed-modulus-unrank modulus (car indices))
          (finite-field-fixed-modulus-unrank-list modulus (cdr indices)))))

(defun finite-field-fixed-modulus-elements (modulus)
  (declare (xargs :guard t))
  (finite-field-fixed-modulus-unrank-list
   modulus
   (gfield::finite-natural-range-from-count
    0 (finite-field-fixed-modulus-coefficient-vector-coding-bound modulus))))

(defun finite-field-fixed-modulus-cardinality (modulus)
  (declare (xargs :guard t))
  (len (finite-field-fixed-modulus-elements modulus)))

(defthm posp-of-finite-field-fixed-modulus-coefficient-vector-coding-bound
  (posp (finite-field-fixed-modulus-coefficient-vector-coding-bound modulus))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable finite-field-fixed-modulus-coefficient-vector-coding-bound))))

(defthm finite-field-fixed-modulus-remainder-of-unrank
  (equal (finite-field-poly-remainder (finite-field-fixed-modulus-unrank modulus k) modulus)
         (finite-field-fixed-modulus-unrank modulus k))
  :hints (("Goal" :cases ((consp (finite-field-poly-normalize modulus))))
          ("Subgoal 2"
           :in-theory (enable finite-field-fixed-modulus-unrank
                              finite-field-fixed-modulus-coefficient-vector-unrank
                              finite-field-fixed-modulus-coefficient-count
                              finite-field-coefficient-vector-unrank
                              finite-field-fixed-modulus-reconstruct))
          ("Subgoal 1"
           :use ((:instance finite-field-poly-remainder-when-reduced-p
                            (polynomial (finite-field-fixed-modulus-unrank modulus k)))
                 (:instance finite-field-poly-reduced-p-of-fixed-modulus-reconstruct-when-vector-p
                            (coefficients (finite-field-fixed-modulus-coefficient-vector-unrank modulus k))))
           :in-theory (enable finite-field-fixed-modulus-unrank))))

(defthm finite-field-fixed-modulus-unrank-of-rank
  (equal (finite-field-fixed-modulus-unrank
          modulus
          (finite-field-fixed-modulus-coefficient-vector-rank x modulus))
         (finite-field-fixed-modulus-reconstruct
          (finite-field-fixed-modulus-coefficient-vector x modulus)))
  :hints (("Goal"
           :use ((:instance finite-field-coefficient-vector-unrank-of-rank
                            (width (finite-field-fixed-modulus-coefficient-count modulus))
                            (coefficients (finite-field-fixed-modulus-coefficient-vector x modulus)))
                 (:instance natp-of-finite-field-fixed-modulus-coefficient-count))
           :in-theory (e/d (finite-field-fixed-modulus-unrank
                            finite-field-fixed-modulus-coefficient-vector-rank
                            finite-field-fixed-modulus-coefficient-vector-unrank)
                           (finite-field-coefficient-vector-unrank-of-rank
                            finite-field-fixed-modulus-coefficient-vector)))))




(defthm natp-of-finite-field-fixed-modulus-coefficient-vector-rank
  (natp (finite-field-fixed-modulus-coefficient-vector-rank x modulus))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable finite-field-fixed-modulus-coefficient-vector-rank))))

(defthm finite-field-fixed-modulus-fix-idempotent
  (equal (finite-field-fixed-modulus-reconstruct
          (finite-field-fixed-modulus-coefficient-vector
           (finite-field-fixed-modulus-reconstruct
            (finite-field-fixed-modulus-coefficient-vector x modulus))
           modulus))
         (finite-field-fixed-modulus-reconstruct
          (finite-field-fixed-modulus-coefficient-vector x modulus)))
  :hints (("Goal"
           :use ((:instance finite-field-fixed-modulus-coefficient-vector-of-reconstruct
                            (coefficients (finite-field-fixed-modulus-coefficient-vector x modulus))))
           :in-theory (disable finite-field-fixed-modulus-coefficient-vector-of-reconstruct
                               finite-field-fixed-modulus-coefficient-vector))))

(defthm finite-field-fixed-modulus-fix-of-unrank
  (equal (finite-field-fixed-modulus-reconstruct
          (finite-field-fixed-modulus-coefficient-vector
           (finite-field-fixed-modulus-unrank modulus k) modulus))
         (finite-field-fixed-modulus-unrank modulus k))
  :hints (("Goal"
           :use ((:instance finite-field-fixed-modulus-coefficient-vector-of-reconstruct
                            (coefficients (finite-field-fixed-modulus-coefficient-vector-unrank modulus k))))
           :in-theory (e/d (finite-field-fixed-modulus-unrank)
                           (finite-field-fixed-modulus-coefficient-vector-of-reconstruct
                            finite-field-fixed-modulus-coefficient-vector)))))

(defthm finite-field-fixed-modulus-rank-of-unrank-when-bounded
  (implies (and (natp k)
                (< k (finite-field-fixed-modulus-coefficient-vector-coding-bound modulus)))
           (equal (finite-field-fixed-modulus-coefficient-vector-rank
                   (finite-field-fixed-modulus-unrank modulus k) modulus)
                  k))
  :hints (("Goal"
           :use ((:instance finite-field-fixed-modulus-coefficient-vector-rank-of-unrank)
                 (:instance finite-field-fixed-modulus-coefficient-vector-of-reconstruct
                            (coefficients (finite-field-fixed-modulus-coefficient-vector-unrank modulus k))))
           :in-theory (e/d (finite-field-fixed-modulus-unrank
                            finite-field-fixed-modulus-coefficient-vector-rank)
                           (finite-field-fixed-modulus-coefficient-vector-of-reconstruct
                            finite-field-fixed-modulus-coefficient-vector-rank-of-unrank
                            finite-field-fixed-modulus-coefficient-vector)))) )

(defthm member-equal-of-finite-field-fixed-modulus-fix-and-elements
  (member-equal (finite-field-fixed-modulus-reconstruct
                 (finite-field-fixed-modulus-coefficient-vector x modulus))
                (finite-field-fixed-modulus-elements modulus))
  :rule-classes nil
  :hints (("Goal"
           :by (:functional-instance
                gfield::member-equal-of-finite-fix-and-finite-elements
                (gfield::finite-fix (lambda (x) (finite-field-fixed-modulus-reconstruct (finite-field-fixed-modulus-coefficient-vector x modulus))))
                (gfield::finite-rank (lambda (x) (finite-field-fixed-modulus-coefficient-vector-rank x modulus)))
                (gfield::finite-unrank (lambda (k) (finite-field-fixed-modulus-unrank modulus k)))
                (gfield::finite-bound (lambda () (finite-field-fixed-modulus-coefficient-vector-coding-bound modulus)))
                (gfield::finite-unrank-list (lambda (indices) (finite-field-fixed-modulus-unrank-list modulus indices)))
                (gfield::finite-elements (lambda () (finite-field-fixed-modulus-elements modulus)))
                (gfield::finite-cardinality (lambda () (finite-field-fixed-modulus-cardinality modulus))))
           :in-theory (union-theories (theory 'minimal-theory) '(finite-field-fixed-modulus-rank-of-unrank-when-bounded finite-field-fixed-modulus-unrank-of-rank finite-field-fixed-modulus-remainder-of-unrank finite-field-fixed-modulus-fix-of-unrank finite-field-fixed-modulus-fix-idempotent posp-of-finite-field-fixed-modulus-coefficient-vector-coding-bound finite-field-fixed-modulus-coefficient-vector-rank-upper-bound natp-of-finite-field-fixed-modulus-coefficient-vector-rank (:definition finite-field-fixed-modulus-unrank-list) (:definition finite-field-fixed-modulus-elements) (:definition finite-field-fixed-modulus-cardinality))))))

(defthm no-duplicatesp-equal-of-finite-field-fixed-modulus-elements
  (no-duplicatesp-equal (finite-field-fixed-modulus-elements modulus))
  :rule-classes nil
  :hints (("Goal"
           :by (:functional-instance
                gfield::no-duplicatesp-equal-of-finite-elements
                (gfield::finite-fix (lambda (x) (finite-field-fixed-modulus-reconstruct (finite-field-fixed-modulus-coefficient-vector x modulus))))
                (gfield::finite-rank (lambda (x) (finite-field-fixed-modulus-coefficient-vector-rank x modulus)))
                (gfield::finite-unrank (lambda (k) (finite-field-fixed-modulus-unrank modulus k)))
                (gfield::finite-bound (lambda () (finite-field-fixed-modulus-coefficient-vector-coding-bound modulus)))
                (gfield::finite-unrank-list (lambda (indices) (finite-field-fixed-modulus-unrank-list modulus indices)))
                (gfield::finite-elements (lambda () (finite-field-fixed-modulus-elements modulus))))
           :in-theory (union-theories (theory 'minimal-theory) '(finite-field-fixed-modulus-rank-of-unrank-when-bounded finite-field-fixed-modulus-unrank-of-rank finite-field-fixed-modulus-remainder-of-unrank finite-field-fixed-modulus-fix-of-unrank finite-field-fixed-modulus-fix-idempotent posp-of-finite-field-fixed-modulus-coefficient-vector-coding-bound finite-field-fixed-modulus-coefficient-vector-rank-upper-bound natp-of-finite-field-fixed-modulus-coefficient-vector-rank (:definition finite-field-fixed-modulus-unrank-list) (:definition finite-field-fixed-modulus-elements) (:definition finite-field-fixed-modulus-cardinality))))))

(defthm len-of-finite-field-fixed-modulus-elements
  (equal (len (finite-field-fixed-modulus-elements modulus))
         (finite-field-fixed-modulus-coefficient-vector-coding-bound modulus))
  :hints (("Goal"
           :by (:functional-instance
                gfield::len-of-finite-elements
                (gfield::finite-fix (lambda (x) (finite-field-fixed-modulus-reconstruct (finite-field-fixed-modulus-coefficient-vector x modulus))))
                (gfield::finite-rank (lambda (x) (finite-field-fixed-modulus-coefficient-vector-rank x modulus)))
                (gfield::finite-unrank (lambda (k) (finite-field-fixed-modulus-unrank modulus k)))
                (gfield::finite-bound (lambda () (finite-field-fixed-modulus-coefficient-vector-coding-bound modulus)))
                (gfield::finite-unrank-list (lambda (indices) (finite-field-fixed-modulus-unrank-list modulus indices)))
                (gfield::finite-elements (lambda () (finite-field-fixed-modulus-elements modulus))))
           :in-theory (union-theories (theory 'minimal-theory) '(finite-field-fixed-modulus-rank-of-unrank-when-bounded finite-field-fixed-modulus-unrank-of-rank finite-field-fixed-modulus-remainder-of-unrank finite-field-fixed-modulus-fix-of-unrank finite-field-fixed-modulus-fix-idempotent posp-of-finite-field-fixed-modulus-coefficient-vector-coding-bound finite-field-fixed-modulus-coefficient-vector-rank-upper-bound natp-of-finite-field-fixed-modulus-coefficient-vector-rank (:definition finite-field-fixed-modulus-unrank-list) (:definition finite-field-fixed-modulus-elements) (:definition finite-field-fixed-modulus-cardinality))))))

(defthm finite-field-fixed-modulus-cardinality-equals-bound
  (equal (finite-field-fixed-modulus-cardinality modulus)
         (finite-field-fixed-modulus-coefficient-vector-coding-bound modulus))
  :hints (("Goal" :in-theory (enable finite-field-fixed-modulus-cardinality))))

(defthm finite-field-fixed-modulus-elements-zero-normalized-modulus
  (implies (equal (finite-field-poly-normalize modulus) nil)
           (equal (finite-field-fixed-modulus-elements modulus) (list nil)))
  :hints (("Goal" :in-theory (enable finite-field-fixed-modulus-elements
                                     finite-field-fixed-modulus-unrank
                                     finite-field-fixed-modulus-unrank-list
                                     gfield::finite-natural-range-from-count))))

(verify-guards finite-field-fixed-modulus-unrank)
(verify-guards finite-field-fixed-modulus-unrank-list)
(verify-guards finite-field-fixed-modulus-elements)
(verify-guards finite-field-fixed-modulus-cardinality)
