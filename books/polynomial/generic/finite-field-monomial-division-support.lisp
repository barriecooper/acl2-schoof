(in-package "GPOLY")

; Temporary staged development book for the finite-field division bridge.
; It certifies the monomial and scalar-division support boundary only;
; recursive divmod, quotient, and remainder targets remain intentionally open.

(include-book "finite-field-instance")
(include-book "division")

(set-default-hints nil)

(defun finite-field-div (x y)
  (gfield::finite-field-mul x (gfield::finite-field-inv y)))

(defthm finite-field-element-p-of-div
  (gfield::finite-field-element-p (finite-field-div x y))
  :hints (("Goal" :in-theory (enable finite-field-div))))
(defthm finite-field-fix-of-div
  (equal (gfield::finite-field-fix (finite-field-div x y))
         (finite-field-div x y))
  :hints (("Goal" :in-theory (enable finite-field-div))))
(defthm finite-field-div-of-fixes
  (equal (finite-field-div (gfield::finite-field-fix x)
                           (gfield::finite-field-fix y))
         (finite-field-div x y))
  :hints (("Goal" :in-theory (enable finite-field-div))))
(defthm finite-field-inv-fixed-congruence-for-div
  (implies (equal (gfield::finite-field-fix x1)
                  (gfield::finite-field-fix x2))
           (equal (gfield::finite-field-inv x1)
                  (gfield::finite-field-inv x2)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance gfield::finite-field-inv-of-fix (x x1))
                        (:instance gfield::finite-field-inv-of-fix (x x2)))
           :in-theory (disable gfield::finite-field-inv-of-fix))))
(defthm finite-field-div-fixed-congruence
  (implies (and (equal (gfield::finite-field-fix x1)
                       (gfield::finite-field-fix x2))
                (equal (gfield::finite-field-fix y1)
                       (gfield::finite-field-fix y2)))
           (equal (finite-field-div x1 y1)
                  (finite-field-div x2 y2)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance gfield::finite-field-mul-fixed-congruence
                                   (x1 x1) (x2 x2)
                                   (y1 (gfield::finite-field-inv y1))
                                   (y2 (gfield::finite-field-inv y2)))
                        (:instance finite-field-inv-fixed-congruence-for-div
                                   (x1 y1) (x2 y2)))
           :in-theory (enable finite-field-div))))
(verify-guards finite-field-div)

(def-monomial-instance
  finite-field-poly-zero-prefix finite-field-poly-shift
  finite-field-poly-monomial finite-field-poly-normalize
  gfield::finite-field-fix gfield::finite-field-zero)

(defthm finite-field-coefficient-list-p-of-poly-zero-prefix
  (implies (finite-field-coefficient-list-p xs)
           (finite-field-coefficient-list-p
            (finite-field-poly-zero-prefix n xs)))
  :hints (("Goal" :in-theory (enable finite-field-poly-zero-prefix))))
(defthm finite-field-true-listp-of-poly-zero-prefix
  (equal (true-listp (finite-field-poly-zero-prefix n xs))
         (true-listp xs))
  :hints (("Goal" :in-theory (enable finite-field-poly-zero-prefix))))
(defthm finite-field-last-of-poly-zero-prefix-when-consp
  (implies (consp xs)
           (equal (last (finite-field-poly-zero-prefix n xs))
                  (last xs)))
  :hints (("Goal" :in-theory (enable finite-field-poly-zero-prefix))))
(defthm finite-field-canonical-polynomial-p-of-poly-zero-prefix
  (implies (and (finite-field-canonical-polynomial-p p) (consp p))
           (finite-field-canonical-polynomial-p
            (finite-field-poly-zero-prefix n p)))
  :hints (("Goal" :use ((:instance finite-field-coefficient-list-p-of-poly-zero-prefix
                                   (xs p))
                        (:instance finite-field-last-of-poly-zero-prefix-when-consp
                                   (xs p)))
           :in-theory (enable finite-field-canonical-polynomial-p))))
(defthm finite-field-len-of-poly-zero-prefix
  (equal (len (finite-field-poly-zero-prefix n xs))
         (+ (nfix n) (len xs)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable finite-field-poly-zero-prefix))))
(verify-guards finite-field-poly-zero-prefix)

(defthm finite-field-coefficient-list-p-of-poly-shift
  (finite-field-coefficient-list-p (finite-field-poly-shift p n))
  :hints (("Goal" :in-theory (enable finite-field-poly-shift
                                      finite-field-canonical-polynomial-p)
           :use ((:instance finite-field-canonical-polynomial-p-of-poly-normalize
                            (xs p))
                 (:instance finite-field-coefficient-list-p-of-poly-zero-prefix
                            (xs (finite-field-poly-normalize p)))))))
(defthm finite-field-canonical-polynomial-p-of-poly-shift
  (finite-field-canonical-polynomial-p (finite-field-poly-shift p n))
  :hints (("Goal" :in-theory (enable finite-field-poly-shift)
           :use ((:instance finite-field-canonical-polynomial-p-of-poly-normalize
                            (xs p))
                 (:instance finite-field-canonical-polynomial-p-of-poly-zero-prefix
                            (p (finite-field-poly-normalize p)))))))
(defthm finite-field-poly-shift-of-nil
  (equal (finite-field-poly-shift nil n) nil)
  :hints (("Goal" :in-theory (enable finite-field-poly-shift))))
(defthm finite-field-consp-of-poly-shift
  (equal (consp (finite-field-poly-shift p n))
         (consp (finite-field-poly-normalize p)))
  :hints (("Goal" :in-theory (enable finite-field-poly-shift finite-field-poly-zero-prefix))))
(defthm finite-field-len-of-poly-shift-when-normalize-nonzero
  (implies (consp (finite-field-poly-normalize p))
           (equal (len (finite-field-poly-shift p n))
                  (+ (nfix n) (len (finite-field-poly-normalize p)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable finite-field-poly-shift)
           :use ((:instance finite-field-len-of-poly-zero-prefix
                            (xs (finite-field-poly-normalize p)))))))
(verify-guards finite-field-poly-shift)


(defthm finite-field-poly-degree-of-poly-shift
  (implies (and (finite-field-canonical-polynomial-p p) (consp p))
           (equal (finite-field-poly-degree (finite-field-poly-shift p n))
                  (+ (finite-field-poly-degree p) (nfix n))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-len-of-poly-shift-when-normalize-nonzero)
                 (:instance finite-field-poly-normalize-when-canonical
                            (xs p))
                 (:instance finite-field-poly-degree-when-canonical-nonzero)
                 (:instance finite-field-poly-degree-when-canonical-nonzero
                            (p (finite-field-poly-shift p n))))
           :in-theory (disable finite-field-poly-shift finite-field-poly-normalize
                               finite-field-poly-degree finite-field-canonical-polynomial-p))))

(defthm finite-field-poly-leading-coefficient-of-poly-shift
  (implies (and (finite-field-canonical-polynomial-p p) (consp p))
           (equal (finite-field-poly-leading-coefficient
                   (finite-field-poly-shift p n))
                  (finite-field-poly-leading-coefficient p)))
  :hints (("Goal"
           :use ((:instance finite-field-poly-normalize-when-canonical (xs p))
                 (:instance finite-field-poly-leading-coefficient-when-canonical-nonzero)
                 (:instance finite-field-poly-leading-coefficient-when-canonical-nonzero
                            (p (finite-field-poly-shift p n)))
                 (:instance finite-field-last-of-poly-zero-prefix-when-consp
                            (xs p)))
           :in-theory (e/d (finite-field-poly-shift)
                           (finite-field-poly-normalize finite-field-poly-leading-coefficient
                            finite-field-canonical-polynomial-p)))))

(defthm finite-field-poly-monomial-is-poly-shift-of-singleton
  (equal (finite-field-poly-monomial a n)
         (finite-field-poly-shift (list (gfield::finite-field-fix a)) n))
  :hints (("Goal" :in-theory (enable finite-field-poly-monomial finite-field-poly-shift
                                      finite-field-poly-normalize
                                      finite-field-poly-fix-coefficients
                                      finite-field-poly-trim-trailing-zeros))))

(defthm finite-field-canonical-polynomial-p-of-monomial
  (finite-field-canonical-polynomial-p (finite-field-poly-monomial a n))
  :hints (("Goal" :use ((:instance finite-field-canonical-polynomial-p-of-poly-shift
                                   (p (list (gfield::finite-field-fix a)))))
           :in-theory (disable finite-field-poly-monomial finite-field-poly-shift))))

(defthm finite-field-poly-monomial-nonzero-iff
  (equal (consp (finite-field-poly-monomial a n))
         (not (equal (gfield::finite-field-fix a) (gfield::finite-field-zero))))
  :hints (("Goal" :in-theory (enable finite-field-poly-monomial finite-field-poly-zero-prefix))))

(defthm finite-field-poly-degree-of-monomial
  (implies (not (equal (gfield::finite-field-fix a) (gfield::finite-field-zero)))
           (equal (finite-field-poly-degree (finite-field-poly-monomial a n))
                  (nfix n)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance finite-field-poly-degree-of-poly-shift
                                   (p (list (gfield::finite-field-fix a))))
                        (:instance finite-field-poly-monomial-is-poly-shift-of-singleton))
           :in-theory (e/d (finite-field-canonical-polynomial-p
                            finite-field-poly-normalize finite-field-poly-fix-coefficients
                            finite-field-poly-trim-trailing-zeros)
                           (finite-field-poly-monomial finite-field-poly-shift
                            finite-field-poly-degree)))))

(defthm finite-field-poly-leading-coefficient-of-monomial
  (implies (not (equal (gfield::finite-field-fix a) (gfield::finite-field-zero)))
           (equal (finite-field-poly-leading-coefficient
                   (finite-field-poly-monomial a n))
                  (gfield::finite-field-fix a)))
  :hints (("Goal" :use ((:instance finite-field-poly-leading-coefficient-of-poly-shift
                                   (p (list (gfield::finite-field-fix a))))
                        (:instance finite-field-poly-monomial-is-poly-shift-of-singleton))
           :in-theory (e/d (finite-field-canonical-polynomial-p
                            finite-field-poly-normalize finite-field-poly-fix-coefficients
                            finite-field-poly-trim-trailing-zeros)
                           (finite-field-poly-monomial finite-field-poly-shift
                            finite-field-poly-leading-coefficient)))))

(verify-guards finite-field-poly-monomial)

(defthm finite-field-mul-zero-left
  (equal (gfield::finite-field-mul (gfield::finite-field-zero) x)
         (gfield::finite-field-zero))
  :hints (("Goal" :by (:functional-instance gfield::field-mul-zero-left
                    (gfield::field-element-p gfield::finite-field-element-p)
                    (gfield::field-fix gfield::finite-field-fix)
                    (gfield::field-zero gfield::finite-field-zero)
                    (gfield::field-one gfield::finite-field-one)
                    (gfield::field-add gfield::finite-field-add)
                    (gfield::field-mul gfield::finite-field-mul)
                    (gfield::field-neg gfield::finite-field-neg)
                    (gfield::field-inv gfield::finite-field-inv))
           :in-theory (theory 'minimal-theory))
          (and stable-under-simplificationp
               (list :use (theory 'gfield::finite-field-context-instance-theory)
                     :in-theory (list 'quote (theory 'minimal-theory))))))

(defthm finite-field-mul-left-cancel
  (implies (not (equal (gfield::finite-field-fix common)
                       (gfield::finite-field-zero)))
           (equal (equal (gfield::finite-field-mul common first)
                         (gfield::finite-field-mul common second))
                  (equal (gfield::finite-field-fix first)
                         (gfield::finite-field-fix second))))
  :hints (("Goal" :by (:functional-instance gfield::field-mul-left-cancel
                    (gfield::field-element-p gfield::finite-field-element-p)
                    (gfield::field-fix gfield::finite-field-fix)
                    (gfield::field-zero gfield::finite-field-zero)
                    (gfield::field-one gfield::finite-field-one)
                    (gfield::field-add gfield::finite-field-add)
                    (gfield::field-mul gfield::finite-field-mul)
                    (gfield::field-neg gfield::finite-field-neg)
                    (gfield::field-inv gfield::finite-field-inv))
           :in-theory (theory 'minimal-theory))
          (and stable-under-simplificationp
               (list :use (theory 'gfield::finite-field-context-instance-theory)
                     :in-theory (list 'quote (theory 'minimal-theory))))))

(defthm finite-field-mul-nonzero
  (implies (and (not (equal (gfield::finite-field-fix x)
                            (gfield::finite-field-zero)))
                (not (equal (gfield::finite-field-fix y)
                            (gfield::finite-field-zero))))
           (not (equal (gfield::finite-field-mul x y)
                       (gfield::finite-field-zero))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance finite-field-mul-left-cancel
                                   (common x) (first y)
                                   (second (gfield::finite-field-zero)))
                        (:instance finite-field-mul-zero-left
                                   (x (gfield::finite-field-zero))))
           :in-theory (e/d (gfield::finite-field-mul-commutative)
                           (finite-field-mul-left-cancel)))))

(defthm finite-field-inv-nonzero
  (implies (not (equal (gfield::finite-field-fix y)
                       (gfield::finite-field-zero)))
           (not (equal (gfield::finite-field-inv y)
                       (gfield::finite-field-zero))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance gfield::finite-field-mul-inverse-left
                                   (x y))
                        (:instance finite-field-mul-zero-left
                                   (x y)))
           :in-theory (disable finite-field-mul-zero-left))))

(defthm finite-field-div-nonzero
  (implies (and (not (equal (gfield::finite-field-fix x)
                            (gfield::finite-field-zero)))
                (not (equal (gfield::finite-field-fix y)
                            (gfield::finite-field-zero))))
           (not (equal (finite-field-div x y)
                       (gfield::finite-field-zero))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance finite-field-mul-nonzero
                                   (x x) (y (gfield::finite-field-inv y)))
                        (:instance finite-field-inv-nonzero))
           :in-theory (enable finite-field-div))))

(defthm finite-field-div-mul-denominator
  (implies (not (equal (gfield::finite-field-fix y)
                       (gfield::finite-field-zero)))
           (equal (gfield::finite-field-mul (finite-field-div x y) y)
                  (gfield::finite-field-fix x)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance gfield::finite-field-mul-inverse-left
                                   (x y)))
           :in-theory (enable finite-field-div
                              gfield::finite-field-mul-associative))))
