(in-package "GPOLY")
(include-book "f7x2-representation")

; This presentation-specific operation is only an executable inverse candidate.
; Its zero branch implements the total GFIELD convention explicitly; the
; nonzero branch delegates once to the existing reduced F7 modular inverse.
(defun f7x2-inv (value)
  (declare (xargs :guard t))
  (let ((fixed-value (f7x2-fix value)))
    (if (equal fixed-value (f7x2-zero))
        (f7x2-zero)
      (f7-poly-modular-inverse fixed-value '(1 0 1)))))

(verify-guards f7x2-inv)

; These ground evaluations are execution evidence only.  Universal closure,
; fixing, zero, and nonzero inverse laws remain separate proof obligations.
(defthm f7x2-inv-execution-regressions
  (and
   (equal (f7x2-inv (f7x2-zero)) (f7x2-zero))
   (equal (f7x2-inv nil) nil)
   (equal (f7x2-inv '(1)) '(1))
   (equal (f7x2-inv '(3)) '(5))
   (equal (f7x2-inv '(0 1)) '(0 6))
   (equal (f7x2-inv '(1 1)) '(4 3))
   (equal (f7x2-inv '(1 1 0)) '(4 3))
   (equal (f7x2-inv '(8 1)) '(4 3))
   (equal (f7x2-inv '(1 1 . malformed-tail)) '(4 3)))
  :rule-classes nil)
