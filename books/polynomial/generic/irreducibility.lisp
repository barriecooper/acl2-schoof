(in-package "GPOLY")
(include-book "euclidean")

; A polynomial unit is exactly a nonzero constant after the repository's
; total coefficient fixing and trailing-zero normalization.
(defun poly-unit-p (poly)
  (declare (xargs :guard t))
  (equal (poly-degree poly) 0))

; Generic factor quantification is deliberately logical.  It is not a factor
; search and does not claim to be executable over an abstract coefficient
; field.
(defun-sk poly-reducible-p (poly)
  (exists (left right)
          (and (equal (poly-mul left right) (normalize poly))
               (not (poly-unit-p left))
               (not (poly-unit-p right)))))

(defun poly-irreducible-p (poly)
  (declare (xargs :guard t :verify-guards nil))
  (and (< 0 (poly-degree poly))
       (not (poly-reducible-p poly))))

(defthm poly-irreducible-p-definition
  (equal (poly-irreducible-p poly)
         (and (< 0 (poly-degree poly))
              (not (poly-reducible-p poly))))
  :rule-classes nil)

(defthm poly-reducible-p-normalize-forward
  (implies (poly-reducible-p poly)
           (poly-reducible-p (normalize poly)))
  :hints (("Goal"
           :use ((:instance poly-reducible-p-suff
                            (poly (normalize poly))
                            (left (mv-nth 0 (poly-reducible-p-witness poly)))
                            (right (mv-nth 1 (poly-reducible-p-witness poly))))))))

(defthm poly-reducible-p-normalize-reverse
  (implies (poly-reducible-p (normalize poly))
           (poly-reducible-p poly))
  :hints (("Goal"
           :use ((:instance poly-reducible-p-suff
                            (poly poly)
                            (left (mv-nth 0 (poly-reducible-p-witness
                                             (normalize poly))))
                            (right (mv-nth 1 (poly-reducible-p-witness
                                              (normalize poly)))))))))

(defthm poly-reducible-p-of-normalize
  (equal (poly-reducible-p (normalize poly))
         (poly-reducible-p poly))
  :hints (("Goal"
           :use ((:instance poly-reducible-p-normalize-forward)
                 (:instance poly-reducible-p-normalize-reverse)))))

(defthm poly-irreducible-p-of-normalize
  (equal (poly-irreducible-p (normalize poly))
         (poly-irreducible-p poly))
  :hints (("Goal"
           :use ((:instance poly-degree-of-normalize (p poly))
                 (:instance poly-reducible-p-of-normalize))
           :in-theory (e/d (poly-irreducible-p)
                           (poly-degree-of-normalize
                            poly-reducible-p-of-normalize
                            poly-reducible-p)))))

(defthm poly-irreducible-p-implies-positive-degree
  (implies (poly-irreducible-p poly)
           (< 0 (poly-degree poly)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable poly-irreducible-p))))

(defthm poly-irreducible-p-implies-normalize-nonzero
  (implies (poly-irreducible-p poly)
           (consp (normalize poly)))
  :rule-classes (:forward-chaining)
  :hints (("Goal"
           :use ((:instance poly-degree-equal-minus-one (p poly)))
           :in-theory (enable poly-irreducible-p))))

(defthm poly-irreducible-p-factor-characterization
  (implies (and (poly-irreducible-p poly)
                (equal (poly-mul left right) (normalize poly)))
           (or (poly-unit-p left)
               (poly-unit-p right)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-reducible-p-suff
                            (poly poly) (left left) (right right)))
           :in-theory (enable poly-irreducible-p))))

(defthm poly-unit-p-of-normalize
  (equal (poly-unit-p (normalize poly))
         (poly-unit-p poly)))

(defthm poly-unit-p-of-const
  (equal (poly-unit-p (const scalar))
         (not (equal (gfield::field-fix scalar)
                     (gfield::field-zero))))
  :hints (("Goal" :in-theory (enable poly-unit-p))))

(defthm poly-irreducible-p-of-nil
  (not (poly-irreducible-p nil))
  :hints (("Goal" :in-theory (enable poly-irreducible-p))))

(defthm poly-irreducible-p-of-polynomial-one
  (not (poly-irreducible-p (polynomial-one)))
  :hints (("Goal" :in-theory (enable poly-irreducible-p))))

(defthm poly-irreducible-p-of-const
  (not (poly-irreducible-p (const scalar)))
  :hints (("Goal" :in-theory (enable poly-irreducible-p))))
