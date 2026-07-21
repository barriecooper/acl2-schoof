(in-package "GPOLY")
(include-book "base")
(include-book "../../field/pfield-adapter")

; Copies at the exact-arity PFIELD adapter boundary make functional
; instantiation explicit and keep GPOLY independent of a modulus.
(defun pfield-fix-coefficients (xs)
  (if (atom xs) nil
    (cons (gfield::pfield-fix (car xs))
          (pfield-fix-coefficients (cdr xs)))))

(defun pfield-trim-trailing-zeros (xs)
  (if (atom xs) nil
    (let ((tail (pfield-trim-trailing-zeros (cdr xs))))
      (if (and (equal (gfield::pfield-fix (car xs))
                      (gfield::pfield-zero))
               (endp tail))
          nil
        (cons (car xs) tail)))))

(defun pfield-normalize (xs)
  (pfield-trim-trailing-zeros (pfield-fix-coefficients xs)))

(defun pfield-eval (poly x)
  (if (atom poly)
      (gfield::pfield-zero)
    (gfield::pfield-add
     (gfield::pfield-fix (car poly))
     (gfield::pfield-mul (gfield::pfield-fix x)
                         (pfield-eval (cdr poly) x)))))

(defthm pfield-normalize-preserves-eval-from-generic
  (equal (pfield-eval (pfield-normalize poly) x)
         (pfield-eval poly x))
  :hints (("Goal" :by (:functional-instance
                        eval-of-normalize
                        (gfield::field-element-p gfield::pfield-element-p)
                        (gfield::field-fix gfield::pfield-fix)
                        (gfield::field-zero gfield::pfield-zero)
                        (gfield::field-one gfield::pfield-one)
                        (gfield::field-add gfield::pfield-add)
                        (gfield::field-mul gfield::pfield-mul)
                        (gfield::field-neg gfield::pfield-neg)
                        (gfield::field-inv gfield::pfield-inv)
                        (fix-coefficients pfield-fix-coefficients)
                        (trim-trailing-zeros pfield-trim-trailing-zeros)
                        (normalize pfield-normalize)
                        (eval pfield-eval)))))

; Executable copies for the concrete F_7 adapter instance.
(defun f7-fix-coefficients (xs)
  (if (atom xs) nil
    (cons (gfield::f7-fix (car xs))
          (f7-fix-coefficients (cdr xs)))))
(defun f7-trim-trailing-zeros (xs)
  (if (atom xs) nil
    (let ((tail (f7-trim-trailing-zeros (cdr xs))))
      (if (and (equal (gfield::f7-fix (car xs)) (gfield::f7-zero))
               (endp tail))
          nil
        (cons (car xs) tail)))))
(defun f7-normalize (xs)
  (f7-trim-trailing-zeros (f7-fix-coefficients xs)))
(defun f7-eval (poly x)
  (if (atom poly) (gfield::f7-zero)
    (gfield::f7-add (gfield::f7-fix (car poly))
                    (gfield::f7-mul (gfield::f7-fix x)
                                    (f7-eval (cdr poly) x)))))

(assert-event (equal (f7-normalize '(1 2 0 0)) '(1 2)))
(assert-event (equal (f7-normalize '(0 0 0)) nil))
(assert-event (equal (f7-eval '(1 2 3) 2) 3))
(assert-event (equal (f7-eval '(6 6) 6) 0))
(assert-event (equal (f7-eval (f7-normalize '(1 2 3 0 0)) 2)
                     (f7-eval '(1 2 3 0 0) 2)))
