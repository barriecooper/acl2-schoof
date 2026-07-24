(in-package "GPOLY")
(include-book "package")
(include-book "instantiate")
(include-book "../../field/kernel")

; Dense coefficients are in ascending-degree order.  POLYNOMIAL-P is the
; structural (not necessarily canonical) recognizer.
(defun coefficient-list-p (xs)
  (if (atom xs)
      (null xs)
    (and (gfield::field-element-p (car xs))
         (coefficient-list-p (cdr xs)))))

(defun polynomial-p (xs) (coefficient-list-p xs))
(defun poly-zerop (xs) (not (consp xs)))

(defun canonical-polynomial-p (xs)
  (and (coefficient-list-p xs)
       (or (not (consp xs))
           (not (equal (car (last xs)) (gfield::field-zero))))))

; On an atom, all list-processing functions stop and discard that malformed
; tail.  Thus these definitions are total without relying on guards.
; Constant-first normalization and Horner evaluation.  This invocation and
; concrete invocations expand to the same four ordinary DEFUN templates.
(def-normalize-eval-instance
  fix-coefficients trim-trailing-zeros normalize eval
  gfield::field-fix gfield::field-zero gfield::field-add gfield::field-mul)

(defthm coefficient-list-p-implies-true-listp
  (implies (coefficient-list-p xs) (true-listp xs)))

(defthm coefficient-list-p-of-fix-coefficients
  (coefficient-list-p (fix-coefficients xs)))

(defthm fix-coefficients-when-coefficient-list-p
  (implies (coefficient-list-p xs)
           (equal (fix-coefficients xs) xs)))

(defthm fix-coefficients-idempotent
  (equal (fix-coefficients (fix-coefficients xs))
         (fix-coefficients xs)))

(defthm coefficient-list-p-of-trim-trailing-zeros
  (implies (coefficient-list-p xs)
           (coefficient-list-p (trim-trailing-zeros xs))))

(defthm consp-of-trim-implies-last-nonzero
  (implies (consp (trim-trailing-zeros xs))
           (not (equal (car (last (trim-trailing-zeros xs)))
                       (gfield::field-zero)))))

(defthm canonical-polynomial-p-of-normalize
  (canonical-polynomial-p (normalize xs)))

(defthm trim-trailing-zeros-when-canonical
  (implies (canonical-polynomial-p xs)
           (equal (trim-trailing-zeros xs) xs)))

(defthm normalize-when-canonical
  (implies (canonical-polynomial-p xs)
           (equal (normalize xs) xs)))

(defthm normalize-idempotent
  (equal (normalize (normalize xs)) (normalize xs)))

(defthm canonical-polynomial-p-of-nil
  (canonical-polynomial-p nil))

(defthm canonical-polynomial-p-implies-polynomial-p
  (implies (canonical-polynomial-p xs) (polynomial-p xs)))

(defthm canonical-zero-polynomial-is-nil
  (implies (and (canonical-polynomial-p xs) (poly-zerop xs))
           (equal xs nil))
  :rule-classes nil)

(defthm normalize-equal-nil-when-not-consp
  (implies (not (consp (normalize xs)))
           (equal (normalize xs) nil))
  :hints
  (("Goal"
    :use ((:instance canonical-zero-polynomial-is-nil
                     (xs (normalize xs)))))))

(defthm canonical-nonzero-iff-consp
  (implies (canonical-polynomial-p xs)
           (equal (not (poly-zerop xs)) (consp xs))))

(defthm len-of-fix-coefficients
  (equal (len (fix-coefficients xs)) (len xs)))

(defthm len-of-trim-trailing-zeros
  (<= (len (trim-trailing-zeros xs)) (len xs))
  :rule-classes :linear)

(defthm len-of-normalize
  (<= (len (normalize xs)) (len xs))
  :rule-classes :linear)

(defthm field-element-p-of-eval
  (gfield::field-element-p (eval poly x)))

(defthm eval-of-nil
  (equal (eval nil x) (gfield::field-zero)))

(defthm eval-of-field-fix
  (equal (eval poly (gfield::field-fix x)) (eval poly x)))

(defthm eval-of-fix-coefficients
  (equal (eval (fix-coefficients poly) x) (eval poly x)))

(defthm eval-of-trim-trailing-zeros
  (equal (eval (trim-trailing-zeros poly) x) (eval poly x)))

(defthm eval-of-normalize
  (equal (eval (normalize poly) x) (eval poly x)))

(defthm eval-of-constant
  (equal (eval (list c) x) (gfield::field-fix c)))

(defthm eval-at-zero
  (equal (eval poly (gfield::field-zero))
         (if (consp poly)
             (gfield::field-fix (car poly))
           (gfield::field-zero))))
