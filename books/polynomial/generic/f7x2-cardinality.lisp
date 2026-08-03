(in-package "GPOLY")

(include-book "f7x2-representation")
(include-book "../../field/pfield-cardinality")
(include-book "kestrel/arithmetic-light/mod2" :dir :system)
(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm true-listp-of-f7x2-fix-for-guards
   (true-listp (f7x2-fix x))
   :hints (("Goal" :use f7x2-fix-normalized
            :in-theory (disable f7x2-fix f7-normalize)))))

(verify-guards f7x2-constant-coefficient
  :hints (("Goal" :use true-listp-of-f7x2-fix-for-guards)))
(verify-guards f7x2-linear-coefficient
  :hints (("Goal" :use true-listp-of-f7x2-fix-for-guards)))

; The two canonical coefficients are the radix-7 digits.  Both projections fix
; arbitrary inputs, so ranking has fixer-induced total semantics.
(defun f7x2-rank (x)
  (+ (f7x2-constant-coefficient x)
     (* 7 (f7x2-linear-coefficient x))))

; Unranking is total and periodic modulo 49.  Normalization removes the padded
; linear zero without changing either decoded coefficient.
(defun f7x2-unrank (k)
  (let* ((index (mod (nfix k) 49))
         (constant (mod index 7))
         (linear (floor index 7)))
    (f7-normalize
     (list (gfield::f7-fix constant)
           (gfield::f7-fix linear)))))

(verify-guards f7x2-rank)
(verify-guards f7x2-unrank)

(defun f7x2-unrank-list (indices)
  (declare (xargs :guard (true-listp indices)))
  (if (endp indices)
      nil
    (cons (f7x2-unrank (car indices))
          (f7x2-unrank-list (cdr indices)))))

(defun f7x2-elements ()
  (declare (xargs :guard t))
  (f7x2-unrank-list
   (gfield::pfield-natural-range-from-count 0 49)))

(defun f7x2-cardinality ()
  (declare (xargs :guard t))
  (len (f7x2-elements)))

(local
 (defthm f7-element-p-bounds-for-cardinality
   (implies (gfield::f7-element-p x)
            (and (natp x) (< x 7)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable gfield::f7-element-p pfield::fep)))))

(local
 (defthm natp-of-f7x2-constant-coefficient
   (natp (f7x2-constant-coefficient x))
   :rule-classes :type-prescription
   :hints (("Goal" :use f7-element-p-of-f7x2-constant-coefficient))))
(local
 (defthm f7x2-constant-coefficient-upper-bound
   (< (f7x2-constant-coefficient x) 7)
   :rule-classes :linear
   :hints (("Goal" :use f7-element-p-of-f7x2-constant-coefficient))))
(local
 (defthm natp-of-f7x2-linear-coefficient
   (natp (f7x2-linear-coefficient x))
   :rule-classes :type-prescription
   :hints (("Goal" :use f7-element-p-of-f7x2-linear-coefficient))))
(local
 (defthm f7x2-linear-coefficient-upper-bound
   (< (f7x2-linear-coefficient x) 7)
   :rule-classes :linear
   :hints (("Goal" :use f7-element-p-of-f7x2-linear-coefficient))))

(defthm natp-of-f7x2-rank
  (natp (f7x2-rank x))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable f7x2-rank))))

(defthm f7x2-rank-upper-bound
  (< (f7x2-rank x) 49)
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable f7x2-rank))))

(defthm f7x2-rank-of-f7x2-fix
  (equal (f7x2-rank (f7x2-fix x))
         (f7x2-rank x))
  :hints (("Goal"
           :use ((:instance f7x2-constant-coefficient-of-fix)
                 (:instance f7x2-linear-coefficient-of-fix))
           :in-theory (e/d (f7x2-rank)
                           (f7x2-fix f7x2-constant-coefficient
                                    f7x2-linear-coefficient)))))

(local
 (defthm decoded-index-is-natural-and-bounded
   (let ((index (mod (nfix k) 49)))
     (and (natp index) (< index 49)))
   ))

(local
 (defthm decoded-linear-digit-is-natural-and-bounded
   (let ((index (mod (nfix k) 49)))
     (and (natp (floor index 7))
          (< (floor index 7) 7)))
   ))

(local
 (defthm f7-fix-of-small-natural
   (implies (and (natp x) (< x 7))
            (equal (gfield::f7-fix x) x))
   :hints (("Goal" :in-theory (enable gfield::f7-fix pfield::fep-fix)))))

(local
 (defthm f7x2-unrank-is-normalized-two-digits
   (equal (f7x2-unrank k)
          (f7-normalize
           (list (mod (mod (nfix k) 49) 7)
                 (floor (mod (nfix k) 49) 7))))
   :hints (("Goal" :in-theory (enable f7x2-unrank)))))

(defthm f7x2-element-p-of-f7x2-unrank
  (f7x2-element-p (f7x2-unrank k))
  :hints (("Goal"
           :use ((:instance f7x2-element-p-characterization
                            (x (f7x2-unrank k))))
           :in-theory (enable f7x2-unrank f7-poly-degree
                              f7-normalize f7-fix-coefficients
                              f7-trim-trailing-zeros))))

(defthm f7x2-fix-of-f7x2-unrank
  (equal (f7x2-fix (f7x2-unrank k))
         (f7x2-unrank k))
  :hints (("Goal"
           :use ((:instance f7x2-fix-when-f7x2-element-p
                            (x (f7x2-unrank k)))
                 (:instance f7x2-element-p-of-f7x2-unrank))
           :in-theory (disable f7x2-fix f7x2-unrank
                               f7x2-element-p))))

(defthm f7x2-constant-coefficient-of-f7x2-unrank
  (equal (f7x2-constant-coefficient (f7x2-unrank k))
         (mod (mod (nfix k) 49) 7))
  :hints (("Goal"
           :use ((:instance f7x2-fix-of-f7x2-unrank)
                 (:instance f7x2-unrank-is-normalized-two-digits))
           :in-theory (e/d (f7x2-constant-coefficient
                            f7-normalize f7-fix-coefficients
                            f7-trim-trailing-zeros)
                           (f7x2-fix f7x2-unrank)))))

(defthm f7x2-linear-coefficient-of-f7x2-unrank
  (equal (f7x2-linear-coefficient (f7x2-unrank k))
         (floor (mod (nfix k) 49) 7))
  :hints (("Goal"
           :use ((:instance f7x2-fix-of-f7x2-unrank)
                 (:instance f7x2-unrank-is-normalized-two-digits))
           :in-theory (e/d (f7x2-linear-coefficient
                            f7-normalize f7-fix-coefficients
                            f7-trim-trailing-zeros)
                           (f7x2-fix f7x2-unrank)))))

(local
 (defthm mod-of-radix-seven-pair
   (implies (and (natp a) (< a 7) (natp b) (< b 7))
            (equal (mod (+ a (* 7 b)) 7) a))))

(local
 (defthm floor-of-radix-seven-pair
   (implies (and (natp a) (< a 7) (natp b) (< b 7))
            (equal (floor (+ a (* 7 b)) 7) b))))

(local
 (defthm mod-49-of-f7x2-rank
   (equal (mod (f7x2-rank x) 49) (f7x2-rank x))
   :hints (("Goal"
            :use ((:instance acl2::mod-when-<
                             (x (f7x2-rank x)) (y 49))
                  (:instance natp-of-f7x2-rank)
                  (:instance f7x2-rank-upper-bound))
            :in-theory (disable f7x2-rank mod)))))

(local
 (defthm constant-coefficient-of-unrank-rank
   (equal (f7x2-constant-coefficient (f7x2-unrank (f7x2-rank x)))
          (f7x2-constant-coefficient x))
   :hints (("Goal"
            :use ((:instance f7x2-constant-coefficient-of-f7x2-unrank
                             (k (f7x2-rank x)))
                  (:instance mod-49-of-f7x2-rank)
                  (:instance f7-element-p-of-f7x2-constant-coefficient)
                  (:instance f7-element-p-of-f7x2-linear-coefficient)
                  (:instance mod-of-radix-seven-pair
                             (a (f7x2-constant-coefficient x))
                             (b (f7x2-linear-coefficient x))))
            :in-theory (e/d (f7x2-rank)
                            (f7x2-unrank f7x2-constant-coefficient
                             f7x2-linear-coefficient mod))))))

(local
 (defthm linear-coefficient-of-unrank-rank
   (equal (f7x2-linear-coefficient (f7x2-unrank (f7x2-rank x)))
          (f7x2-linear-coefficient x))
   :hints (("Goal"
            :use ((:instance f7x2-linear-coefficient-of-f7x2-unrank
                             (k (f7x2-rank x)))
                  (:instance mod-49-of-f7x2-rank)
                  (:instance f7-element-p-of-f7x2-constant-coefficient)
                  (:instance f7-element-p-of-f7x2-linear-coefficient)
                  (:instance floor-of-radix-seven-pair
                             (a (f7x2-constant-coefficient x))
                             (b (f7x2-linear-coefficient x))))
            :in-theory (e/d (f7x2-rank)
                            (f7x2-unrank f7x2-constant-coefficient
                             f7x2-linear-coefficient mod floor))))))

(defthm f7x2-unrank-of-f7x2-rank
  (equal (f7x2-unrank (f7x2-rank x))
         (f7x2-fix x))
  :hints (("Goal"
           :use ((:instance f7x2-fix-coefficient-extensionality
                            (first (f7x2-unrank (f7x2-rank x)))
                            (second x))
                 (:instance f7x2-fix-of-f7x2-unrank
                            (k (f7x2-rank x))))
           :in-theory (disable f7x2-fix f7x2-unrank f7x2-rank
                            f7x2-constant-coefficient
                            f7x2-linear-coefficient))))

(defthm f7x2-rank-of-f7x2-unrank
  (equal (f7x2-rank (f7x2-unrank k))
         (mod (nfix k) 49))
  :hints (("Goal"
           :use ((:instance f7x2-constant-coefficient-of-f7x2-unrank)
                 (:instance f7x2-linear-coefficient-of-f7x2-unrank)
                 (:instance acl2::+-of-mod-and-*-of-floor-same
                            (x (mod (nfix k) 49)) (y 7)))
           :in-theory (e/d (f7x2-rank)
                           (f7x2-unrank f7x2-constant-coefficient
                            f7x2-linear-coefficient mod floor
                            f7x2-unrank-is-normalized-two-digits
                            f7-fix-of-small-natural)))))

(defthm f7x2-rank-of-f7x2-unrank-when-below-49
  (implies (and (natp k) (< k 49))
           (equal (f7x2-rank (f7x2-unrank k)) k))
  :hints (("Goal"
           :use ((:instance f7x2-rank-of-f7x2-unrank)
                 (:instance acl2::mod-when-< (x k) (y 49)))
           :in-theory (disable f7x2-rank f7x2-unrank mod))))

(defthm equal-of-f7x2-unrank-when-below-49
  (implies (and (natp i) (< i 49)
                (natp j) (< j 49))
           (equal (equal (f7x2-unrank i) (f7x2-unrank j))
                  (equal i j)))
  :hints (("Goal" :use ((:instance f7x2-rank-of-f7x2-unrank-when-below-49
                                   (k i))
                         (:instance f7x2-rank-of-f7x2-unrank-when-below-49
                                   (k j))))))

(defthm true-listp-of-f7x2-unrank-list
  (true-listp (f7x2-unrank-list indices))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (f7x2-unrank-list indices)
           :in-theory (e/d (f7x2-unrank-list)
                           (f7x2-unrank f7x2-unrank-is-normalized-two-digits)))))

(defthm len-of-f7x2-unrank-list
  (equal (len (f7x2-unrank-list indices)) (len indices))
  :hints (("Goal" :induct (f7x2-unrank-list indices)
           :in-theory (e/d (f7x2-unrank-list)
                           (f7x2-unrank f7x2-unrank-is-normalized-two-digits)))))

(defthm member-equal-of-f7x2-unrank-list
  (implies (member-equal index indices)
           (member-equal (f7x2-unrank index)
                         (f7x2-unrank-list indices)))
  :hints (("Goal" :induct (f7x2-unrank-list indices)
           :in-theory (e/d (f7x2-unrank-list)
                           (f7x2-unrank f7x2-unrank-is-normalized-two-digits)))))

(defthm f7x2-element-p-of-member-equal-of-f7x2-unrank-list
  (implies (member-equal value (f7x2-unrank-list indices))
           (f7x2-element-p value))
  :hints (("Goal"
           :use ((:instance f7x2-element-p-of-f7x2-unrank
                            (k (car indices))))
           :in-theory (e/d (f7x2-unrank-list)
                           (f7x2-unrank f7x2-element-p f7x2-fix
                            f7x2-unrank-is-normalized-two-digits)))))

(local
 (defun f7x2-bounded-index-list-p (indices)
   (if (endp indices)
       t
     (and (natp (car indices))
          (< (car indices) 49)
          (f7x2-bounded-index-list-p (cdr indices))))))

(local
 (defthm f7x2-bounded-index-list-p-of-range
   (f7x2-bounded-index-list-p
    (gfield::pfield-natural-range-from-count 0 49))
   :hints (("Goal"
            :in-theory (enable f7x2-bounded-index-list-p
                               gfield::pfield-natural-range-from-count)))))

(local
 (defthm member-index-when-member-unrank
   (implies (and (natp index)
                 (< index 49)
                 (f7x2-bounded-index-list-p indices)
                 (member-equal (f7x2-unrank index)
                               (f7x2-unrank-list indices)))
            (member-equal index indices))
   :hints (("Goal" :induct (f7x2-unrank-list indices)
            :in-theory (e/d (f7x2-unrank-list
                             f7x2-bounded-index-list-p)
                            (f7x2-unrank
                             f7x2-unrank-is-normalized-two-digits))))))

(local
 (defthm no-duplicatesp-equal-of-f7x2-unrank-list
   (implies (and (no-duplicatesp-equal indices)
                 (f7x2-bounded-index-list-p indices))
            (no-duplicatesp-equal (f7x2-unrank-list indices)))
   :hints (("Goal" :induct (f7x2-unrank-list indices)
            :in-theory (e/d (f7x2-unrank-list
                             f7x2-bounded-index-list-p)
                            (f7x2-unrank
                             f7x2-unrank-is-normalized-two-digits))))))

(defthm true-listp-of-f7x2-elements
  (true-listp (f7x2-elements))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable f7x2-elements))))

(defthm no-duplicatesp-equal-of-f7x2-elements
  (no-duplicatesp-equal (f7x2-elements))
  :hints (("Goal" :in-theory (enable f7x2-elements))))

(defthm f7x2-element-p-of-member-equal-of-f7x2-elements
  (implies (member-equal x (f7x2-elements))
           (f7x2-element-p x))
  :hints (("Goal" :in-theory (enable f7x2-elements))))

(defthm f7x2-fix-when-member-equal-of-f7x2-elements
  (implies (member-equal x (f7x2-elements))
           (equal (f7x2-fix x) x))
  :hints (("Goal" :use f7x2-element-p-of-member-equal-of-f7x2-elements
           :in-theory (disable f7x2-elements))))

(defthm member-equal-of-f7x2-fix-and-f7x2-elements
  (member-equal (f7x2-fix x) (f7x2-elements))
  :hints (("Goal"
           :use ((:instance
                  gfield::member-equal-of-pfield-natural-range-from-count
                  (x (f7x2-rank x)) (start 0) (count 49))
                 (:instance member-equal-of-f7x2-unrank-list
                            (index (f7x2-rank x))
                            (indices (gfield::pfield-natural-range-from-count
                                      0 49))))
           :in-theory (enable f7x2-elements))))

(defthm len-of-f7x2-elements
  (equal (len (f7x2-elements)) 49)
  :hints (("Goal" :in-theory (enable f7x2-elements))))

(defthm f7x2-cardinality-equals-len-of-f7x2-elements
  (equal (f7x2-cardinality) (len (f7x2-elements)))
  :hints (("Goal" :in-theory (enable f7x2-cardinality))))

(defthm f7x2-cardinality-equals-49
  (equal (f7x2-cardinality) 49)
  :hints (("Goal" :use len-of-f7x2-elements
           :in-theory (enable f7x2-cardinality))))

(defthm posp-of-f7x2-cardinality
  (posp (f7x2-cardinality))
  :hints (("Goal" :use f7x2-cardinality-equals-49)))

(verify-guards f7x2-unrank-list)
(verify-guards f7x2-elements)
(verify-guards f7x2-cardinality)
