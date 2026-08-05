(in-package "GPOLY")

(include-book "finite-field-fixed-modulus-coefficients")
(local (include-book "arithmetic-5/top" :dir :system))

(defun finite-field-coefficient-vector-coding-bound (width)
  (declare (xargs :guard (natp width)))
  (expt (nfix (gfield::finite-field-bound)) (nfix width)))

(defun finite-field-coefficient-vector-rank (coefficients)
  (declare (xargs :guard t))
  (if (consp coefficients)
      (+ (gfield::finite-field-rank (car coefficients))
         (* (nfix (gfield::finite-field-bound))
            (finite-field-coefficient-vector-rank (cdr coefficients))))
    0))

(defun finite-field-coefficient-vector-unrank (width k)
  (declare (xargs :guard (natp width)
                  :measure (nfix width)))
  (if (zp (nfix width))
      nil
    (cons (gfield::finite-field-unrank
           (mod (nfix k) (nfix (gfield::finite-field-bound))))
          (finite-field-coefficient-vector-unrank
           (1- (nfix width))
           (floor (nfix k) (nfix (gfield::finite-field-bound)))))))

(verify-guards finite-field-coefficient-vector-coding-bound)
(verify-guards finite-field-coefficient-vector-rank)
(verify-guards finite-field-coefficient-vector-unrank)

(defthm posp-of-finite-field-coefficient-vector-coding-bound
  (posp (finite-field-coefficient-vector-coding-bound width))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable finite-field-coefficient-vector-coding-bound))))

(defthm natp-of-finite-field-coefficient-vector-rank
  (natp (finite-field-coefficient-vector-rank coefficients))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable gfield::posp-of-finite-field-bound))))

(defthm true-listp-of-finite-field-coefficient-vector-unrank
  (true-listp (finite-field-coefficient-vector-unrank width k))
  :rule-classes :type-prescription)

(defthm len-of-finite-field-coefficient-vector-unrank
  (equal (len (finite-field-coefficient-vector-unrank width k))
         (nfix width)))


(local
 (defthm finite-field-element-p-of-finite-field-unrank-local
   (gfield::finite-field-element-p (gfield::finite-field-unrank k))
   :hints (("Goal" :use ((:instance gfield::finite-field-element-p-of-finite-field-fix
                                    (gfield::x (gfield::finite-field-unrank k)))
                          (:instance gfield::finite-field-fix-of-finite-field-unrank (gfield::k k)))
            :in-theory (disable gfield::finite-field-element-p-of-finite-field-fix
                                gfield::finite-field-fix-of-finite-field-unrank)))))

(defthm finite-field-coefficient-list-p-of-finite-field-coefficient-vector-unrank
  (finite-field-coefficient-list-p
   (finite-field-coefficient-vector-unrank width k))
  :hints (("Goal" :in-theory (enable finite-field-coefficient-list-p))))

(local
 (defthm mixed-radix-step-upper-bound-local
   (implies (and (natp digit) (< digit radix)
                 (natp rest) (< rest (expt radix width))
                 (posp radix) (natp width))
            (< (+ digit (* radix rest))
               (expt radix (+ 1 width))))
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm finite-field-coefficient-vector-rank-upper-bound-by-len
   (implies (finite-field-coefficient-list-p coefficients)
            (< (finite-field-coefficient-vector-rank coefficients)
               (expt (nfix (gfield::finite-field-bound))
                     (len coefficients))))
   :hints (("Goal" :induct (finite-field-coefficient-vector-rank coefficients)
            :nonlinearp t
            :in-theory (enable finite-field-coefficient-list-p
                               gfield::posp-of-finite-field-bound)))))

(defthm finite-field-coefficient-vector-rank-upper-bound
  (implies (and (finite-field-coefficient-list-p coefficients)
                (equal (len coefficients) (nfix width)))
           (< (finite-field-coefficient-vector-rank coefficients)
              (finite-field-coefficient-vector-coding-bound width)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use finite-field-coefficient-vector-rank-upper-bound-by-len
           :in-theory (enable finite-field-coefficient-vector-coding-bound))))

(defthm finite-field-coefficient-vector-rank-of-unrank
  (implies (and (natp k)
                (< k (finite-field-coefficient-vector-coding-bound width)))
           (equal (finite-field-coefficient-vector-rank
                   (finite-field-coefficient-vector-unrank width k))
                  k))
  :hints (("Goal" :induct (finite-field-coefficient-vector-unrank width k)
           :in-theory (enable finite-field-coefficient-vector-coding-bound))))


(local
 (defthm mod-of-mixed-radix-step-local
   (implies (and (natp digit) (< digit radix) (posp radix) (natp rest))
            (equal (mod (+ digit (* radix rest)) radix) digit))))

(local
 (defthm floor-of-mixed-radix-step-local
   (implies (and (natp digit) (< digit radix) (posp radix) (natp rest))
            (equal (floor (+ digit (* radix rest)) radix) rest))))

(local
 (defthm finite-field-coefficient-vector-unrank-of-rank-by-len
   (implies (finite-field-coefficient-list-p coefficients)
            (equal (finite-field-coefficient-vector-unrank
                    (len coefficients)
                    (finite-field-coefficient-vector-rank coefficients))
                   coefficients))
   :hints (("Goal" :induct (finite-field-coefficient-vector-rank coefficients)
            :in-theory (enable finite-field-coefficient-list-p
                               finite-field-coefficient-vector-coding-bound
                               gfield::posp-of-finite-field-bound)))))

(defthm finite-field-coefficient-vector-unrank-of-rank
  (implies (and (natp width)
                (finite-field-coefficient-list-p coefficients)
                (equal (len coefficients) (nfix width)))
           (equal (finite-field-coefficient-vector-unrank
                   width
                   (finite-field-coefficient-vector-rank coefficients))
                  coefficients))
  :hints (("Goal" :use finite-field-coefficient-vector-unrank-of-rank-by-len)))

(defthm finite-field-coefficient-vector-rank-zero-width
  (equal (finite-field-coefficient-vector-rank nil) 0))

(defthm finite-field-coefficient-vector-unrank-zero-width
  (equal (finite-field-coefficient-vector-unrank 0 k) nil))

(defthm finite-field-coefficient-vector-coding-bound-zero-width
  (equal (finite-field-coefficient-vector-coding-bound 0) 1)
  :hints (("Goal" :in-theory (enable finite-field-coefficient-vector-coding-bound))))

(defun finite-field-fixed-modulus-coefficient-vector-rank (x modulus)
  (declare (xargs :guard t))
  (finite-field-coefficient-vector-rank
   (finite-field-fixed-modulus-coefficient-vector x modulus)))

(defun finite-field-fixed-modulus-coefficient-vector-unrank (modulus k)
  (declare (xargs :guard t))
  (finite-field-coefficient-vector-unrank
   (finite-field-fixed-modulus-coefficient-count modulus)
   k))

(defun finite-field-fixed-modulus-coefficient-vector-coding-bound (modulus)
  (declare (xargs :guard t))
  (finite-field-coefficient-vector-coding-bound
   (finite-field-fixed-modulus-coefficient-count modulus)))

(verify-guards finite-field-fixed-modulus-coefficient-vector-rank)
(verify-guards finite-field-fixed-modulus-coefficient-vector-unrank)
(verify-guards finite-field-fixed-modulus-coefficient-vector-coding-bound)

(defthm finite-field-coefficient-list-p-of-fixed-modulus-coefficient-vector-unrank
  (finite-field-coefficient-list-p
   (finite-field-fixed-modulus-coefficient-vector-unrank modulus k))
  :hints (("Goal" :in-theory (enable finite-field-fixed-modulus-coefficient-vector-unrank))))

(defthm len-of-finite-field-fixed-modulus-coefficient-vector-unrank
  (equal (len (finite-field-fixed-modulus-coefficient-vector-unrank modulus k))
         (finite-field-fixed-modulus-coefficient-count modulus))
  :hints (("Goal" :in-theory (enable finite-field-fixed-modulus-coefficient-vector-unrank))))

(defthm finite-field-fixed-modulus-coefficient-vector-rank-upper-bound
  (< (finite-field-fixed-modulus-coefficient-vector-rank x modulus)
     (finite-field-fixed-modulus-coefficient-vector-coding-bound modulus))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use ((:instance finite-field-coefficient-vector-rank-upper-bound
                                   (coefficients (finite-field-fixed-modulus-coefficient-vector x modulus))
                                   (width (finite-field-fixed-modulus-coefficient-count modulus))))
           :in-theory (enable finite-field-fixed-modulus-coefficient-vector-rank
                              finite-field-fixed-modulus-coefficient-vector-coding-bound))))

(defthm finite-field-fixed-modulus-coefficient-vector-rank-of-unrank
  (implies (and (natp k)
                (< k (finite-field-fixed-modulus-coefficient-vector-coding-bound modulus)))
           (equal (finite-field-coefficient-vector-rank
                   (finite-field-fixed-modulus-coefficient-vector-unrank modulus k))
                  k))
  :hints (("Goal" :use ((:instance finite-field-coefficient-vector-rank-of-unrank
                                   (width (finite-field-fixed-modulus-coefficient-count modulus))))
           :in-theory (enable finite-field-fixed-modulus-coefficient-vector-unrank
                              finite-field-fixed-modulus-coefficient-vector-coding-bound))))

