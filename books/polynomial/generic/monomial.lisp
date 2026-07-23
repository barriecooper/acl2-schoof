(in-package "GPOLY")
(include-book "degree")

; Structural zero prefix shared by shifts and monomials.  Its index is total:
; NFIX makes every non-natural input, including a negative integer, mean zero.
(defun zero-prefix (n xs)
  (if (zp (nfix n))
      xs
    (cons (gfield::field-zero)
          (zero-prefix (1- (nfix n)) xs))))

; Multiplication of a canonical dense polynomial by X^N.  Normalize once at
; this public boundary; canonical zero stays NIL instead of becoming zeros.
(defun poly-shift (p n)
  (let ((p (normalize p)))
    (if (consp p)
        (zero-prefix (nfix n) p)
      nil)))

; The canonical dense polynomial A*X^N.
(defun monomial (a n)
  (let ((a (gfield::field-fix a)))
    (if (equal a (gfield::field-zero))
        nil
      (zero-prefix (nfix n) (list a)))))

(defthm coefficient-list-p-of-zero-prefix
  (implies (coefficient-list-p xs)
           (coefficient-list-p (zero-prefix n xs))))

(defthm true-listp-of-zero-prefix
  (equal (true-listp (zero-prefix n xs))
         (true-listp xs)))

(defthm zero-prefix-when-zp
  (implies (zp (nfix n))
           (equal (zero-prefix n xs) xs)))

(defthm zero-prefix-of-nfix
  (equal (zero-prefix (nfix n) xs) (zero-prefix n xs)))

(defthm zero-prefix-composition
  (equal (zero-prefix m (zero-prefix n xs))
         (zero-prefix (+ (nfix m) (nfix n)) xs))
  :rule-classes nil
  :hints (("Goal" :induct (zero-prefix m xs))))

(defthm len-of-zero-prefix
  (equal (len (zero-prefix n xs))
         (+ (nfix n) (len xs)))
  :rule-classes nil)

(defthm last-of-zero-prefix-when-consp
  (implies (consp xs)
           (equal (last (zero-prefix n xs)) (last xs))))

(defthm canonical-polynomial-p-of-zero-prefix
  (implies (and (canonical-polynomial-p p) (consp p))
           (canonical-polynomial-p (zero-prefix n p)))
  :hints (("Goal" :in-theory (enable canonical-polynomial-p))))

(defthm coefficient-list-p-of-poly-shift
  (coefficient-list-p (poly-shift p n))
  :hints (("Goal" :in-theory (enable poly-shift))))

(defthm true-listp-of-poly-shift
  (true-listp (poly-shift p n)))

(defthm canonical-polynomial-p-of-poly-shift
  (canonical-polynomial-p (poly-shift p n))
  :hints (("Goal" :in-theory (enable poly-shift))))

(defthm poly-shift-of-nil
  (equal (poly-shift nil n) nil)
  :hints (("Goal" :in-theory (enable poly-shift))))

(defthm poly-shift-when-zp
  (implies (zp (nfix n))
           (equal (poly-shift p n) (normalize p)))
  :hints (("Goal" :in-theory (enable poly-shift))))

(defthm poly-shift-of-nfix
  (equal (poly-shift p (nfix n)) (poly-shift p n))
  :hints (("Goal" :in-theory (enable poly-shift))))

(defthm poly-shift-composition
  (equal (poly-shift (poly-shift p n) m)
         (poly-shift p (+ (nfix m) (nfix n))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable poly-shift)
           :use ((:instance zero-prefix-composition
                            (xs (normalize p)))))))

(defthm consp-of-poly-shift
  (equal (consp (poly-shift p n))
         (consp (normalize p)))
  :hints (("Goal" :in-theory (enable poly-shift))))

(defthm len-of-poly-shift-when-normalize-nonzero
  (implies (consp (normalize p))
           (equal (len (poly-shift p n))
                  (+ (nfix n) (len (normalize p)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable poly-shift)
           :use ((:instance len-of-zero-prefix
                            (xs (normalize p)))))))

(defthm poly-degree-of-poly-shift
  (implies (and (canonical-polynomial-p p) (consp p))
           (equal (poly-degree (poly-shift p n))
                  (+ (poly-degree p) (nfix n))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance len-of-poly-shift-when-normalize-nonzero)
                 (:instance poly-degree-when-canonical-nonzero)
                 (:instance poly-degree-when-canonical-nonzero
                            (p (poly-shift p n)))))))

(defthm poly-leading-coefficient-of-poly-shift
  (implies (and (canonical-polynomial-p p) (consp p))
           (equal (poly-leading-coefficient (poly-shift p n))
                  (poly-leading-coefficient p)))
  :hints (("Goal"
           :use ((:instance poly-leading-coefficient-when-canonical-nonzero)
                 (:instance poly-leading-coefficient-when-canonical-nonzero
                            (p (poly-shift p n)))))))

(defthm coefficient-list-p-of-monomial
  (coefficient-list-p (monomial a n))
  :hints (("Goal" :in-theory (enable monomial))))

(defthm true-listp-of-monomial
  (true-listp (monomial a n)))

(defthm canonical-polynomial-p-of-monomial
  (canonical-polynomial-p (monomial a n))
  :hints (("Goal" :in-theory (enable monomial))))

(defthm monomial-when-fixed-zero
  (implies (equal (gfield::field-fix a) (gfield::field-zero))
           (equal (monomial a n) nil))
  :hints (("Goal" :in-theory (enable monomial))))

(defthm monomial-when-zp
  (implies (zp (nfix n))
           (equal (monomial a n) (const a)))
  :hints (("Goal" :in-theory (enable monomial const))))

(defthm monomial-of-nfix
  (equal (monomial a (nfix n)) (monomial a n))
  :hints (("Goal" :in-theory (enable monomial))))

(defthm monomial-is-poly-shift-of-const
  (equal (monomial a n) (poly-shift (const a) n))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable monomial poly-shift const))))

(defthm monomial-nonzero-iff
  (equal (consp (monomial a n))
         (not (equal (gfield::field-fix a) (gfield::field-zero))))
  :hints (("Goal" :in-theory (enable monomial))))

(defthm poly-degree-of-monomial
  (implies (not (equal (gfield::field-fix a) (gfield::field-zero)))
           (equal (poly-degree (monomial a n)) (nfix n)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance monomial-is-poly-shift-of-const)
                 (:instance poly-degree-of-poly-shift (p (const a)))))))

(defthm poly-leading-coefficient-of-monomial
  (implies (not (equal (gfield::field-fix a) (gfield::field-zero)))
           (equal (poly-leading-coefficient (monomial a n))
                  (gfield::field-fix a)))
  :hints (("Goal"
           :use ((:instance monomial-is-poly-shift-of-const)
                 (:instance poly-leading-coefficient-of-poly-shift
                            (p (const a)))))))

; Focused symbolic regressions are used because the constrained generic field
; operations intentionally have no evaluator.  Concrete generated copies are
; deferred to the eventual division instance.
(defthm poly-shift-regression-zero
  (equal (poly-shift nil 0) nil))
(defthm poly-shift-regression-one
  (equal (poly-shift (const (gfield::field-one)) 1)
         (list (gfield::field-zero) (gfield::field-one)))
  :hints (("Goal" :in-theory (e/d (poly-shift const zero-prefix)
                                    (zero-prefix-of-nfix)))))
(defthm poly-shift-regression-four
  (equal (len (poly-shift (const (gfield::field-one)) 4)) 5)
  :hints (("Goal"
           :use ((:instance len-of-poly-shift-when-normalize-nonzero
                            (p (const (gfield::field-one))) (n 4))))))
(defthm monomial-regression-zero
  (equal (monomial (gfield::field-zero) 2) nil))
(defthm monomial-regression-constant
  (equal (monomial (gfield::field-one) 0)
         (list (gfield::field-one))))
(defthm monomial-regression-degree-two
  (equal (poly-degree (monomial (gfield::field-one) 2)) 2)
  :hints (("Goal" :use ((:instance poly-degree-of-monomial
                                   (a (gfield::field-one)) (n 2))))))
(defthm monomial-regression-negative-index
  (equal (monomial (gfield::field-one) -3)
         (list (gfield::field-one))))

(verify-guards zero-prefix)
(verify-guards poly-shift)
(verify-guards monomial)

; Expansionary structural facts above have :RULE-CLASSES NIL and are opt-in
; for later division proofs.
