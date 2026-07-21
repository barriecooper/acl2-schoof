(in-package "GPOLY")

; Generate the ordinary executable definitions shared by the abstract theory
; and its concrete instances.  The expansion is deliberately just a PROGN of
; four DEFUN events: :TRANS1 makes every generated definition inspectable.
(defmacro def-normalize-eval-instance
  (fix-coefficients trim-trailing-zeros normalize eval
                    field-fix field-zero field-add field-mul)
  `(progn
     (defun ,fix-coefficients (xs)
       (if (atom xs) nil
         (cons (,field-fix (car xs))
               (,fix-coefficients (cdr xs)))))
     (defun ,trim-trailing-zeros (xs)
       (if (atom xs) nil
         (let ((tail (,trim-trailing-zeros (cdr xs))))
           (if (and (equal (,field-fix (car xs)) (,field-zero))
                    (endp tail))
               nil
             (cons (car xs) tail)))))
     (defun ,normalize (xs)
       (,trim-trailing-zeros (,fix-coefficients xs)))
     (defun ,eval (poly x)
       (if (atom poly)
           (,field-zero)
         (,field-add
          (,field-fix (car poly))
          (,field-mul (,field-fix x)
                      (,eval (cdr poly) x)))))))
