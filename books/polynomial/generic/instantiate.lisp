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

; Addition is separate from negation/subtraction because an adapter may expose
; only the former.  Both macros expand solely to ordinary DEFUN events.
(defmacro def-add-instance
  (raw-add poly-add fix-coefficients normalize field-add)
  `(progn
     (defun ,raw-add (x y)
       (cond ((atom x) (,fix-coefficients y))
             ((atom y) (,fix-coefficients x))
             (t (cons (,field-add (car x) (car y))
                      (,raw-add (cdr x) (cdr y))))))
     (defun ,poly-add (x y)
       (,normalize
        (,raw-add (,normalize x) (,normalize y))))))

(defmacro def-neg-sub-instance
  (raw-neg poly-neg poly-sub poly-add normalize field-neg)
  `(progn
     (defun ,raw-neg (x)
       (if (atom x) nil
         (cons (,field-neg (car x)) (,raw-neg (cdr x)))))
     (defun ,poly-neg (x)
       (,normalize (,raw-neg (,normalize x))))
     (defun ,poly-sub (x y)
       (,poly-add x (,poly-neg y)))))

; Scalar multiplication has its own deliberately small generator.  Like the
; other generators above, its expansion contains ordinary DEFUN events only.
(defmacro def-scale-instance
  (raw-scale poly-scale normalize field-fix field-mul)
  `(progn
     (defun ,raw-scale (a x)
       (if (atom x) nil
         (cons (,field-mul (,field-fix a) (,field-fix (car x)))
               (,raw-scale a (cdr x)))))
     (defun ,poly-scale (a x)
       (,normalize (,raw-scale (,field-fix a) (,normalize x))))))

; Dense multiplication uses the constant-first Horner decomposition
; (a . f)g = a*g + X(f*g).  Only raw operations occur in the recursion;
; normalization is performed once, by the public operation.
(defmacro def-mul-instance
  (raw-mul poly-mul raw-add raw-scale normalize field-zero)
  `(progn
     (defun ,raw-mul (x y)
       (if (or (atom x) (atom y))
           nil
         (,raw-add (,raw-scale (car x) y)
                   (cons (,field-zero) (,raw-mul (cdr x) y)))))
     (defun ,poly-mul (x y)
       (,normalize (,raw-mul (,normalize x) (,normalize y))))))

; The coefficient-field embedding is intentionally its own tiny generator.
; Its expansion is one ordinary DEFUN, not a general algebra-instance layer.
(defmacro def-const-instance (const field-fix field-zero)
  `(defun ,const (a)
     (let ((fixed-a (,field-fix a)))
       (if (equal fixed-a (,field-zero))
           nil
         (list fixed-a)))))
