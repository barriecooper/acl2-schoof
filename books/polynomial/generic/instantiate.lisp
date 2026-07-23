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

; Degree and leading coefficient share one deliberately narrow, transparent
; generator.  Its expansion is exactly two ordinary DEFUN events.  Each
; public operation normalizes its arbitrary input once before inspecting the
; resulting canonical coefficient list.
(defmacro def-degree-instance (degree leading-coefficient normalize field-zero)
  `(progn
     (defun ,degree (poly)
       (let ((p (,normalize poly)))
         (if (consp p) (1- (len p)) -1)))
     (defun ,leading-coefficient (poly)
       (let ((p (,normalize poly)))
         (if (consp p) (car (last p)) (,field-zero))))))


; Monomial/shift construction is shared by the generic theory and instances.
; The expansion contains exactly three ordinary DEFUN events.
(defmacro def-monomial-instance
  (zero-prefix poly-shift monomial normalize field-fix field-zero)
  `(progn
     (defun ,zero-prefix (n xs)
       (if (zp (nfix n)) xs
         (cons (,field-zero) (,zero-prefix (1- (nfix n)) xs))))
     (defun ,poly-shift (p n)
       (let ((p (,normalize p)))
         (if (consp p) (,zero-prefix (nfix n) p) nil)))
     (defun ,monomial (a n)
       (let ((a (,field-fix a)))
         (if (equal a (,field-zero)) nil
           (,zero-prefix (nfix n) (list a)))))))

; One leading-term cancellation, including its public normalization boundary
; and transparent result accessors.  The expansion is four ordinary DEFUNs:
; the core, public wrapper, term accessor, and next accessor.
(defmacro def-division-step-instance
  (core step term next degree leading monomial poly-sub poly-mul normalize
        field-div)
  `(progn
     (defun ,core (remainder divisor)
       (if (and (consp remainder) (consp divisor)
                (<= (,degree divisor) (,degree remainder)))
           (let* ((k (- (,degree remainder) (,degree divisor)))
                  (c (,field-div (,leading remainder) (,leading divisor)))
                  (term (,monomial c k)))
             (cons term (,poly-sub remainder (,poly-mul term divisor))))
         (cons nil remainder)))
     (defun ,step (remainder divisor)
       (let ((remainder (,normalize remainder))
             (divisor (,normalize divisor)))
         (,core remainder divisor)))
     (defun ,term (remainder divisor) (car (,step remainder divisor)))
     (defun ,next (remainder divisor) (cdr (,step remainder divisor)))))

; Canonical-state recursive division.  The length of the canonical remainder
; is the measure; each active iteration computes and reuses exactly one step.
(defmacro def-divmod-instance
  (core divmod canonical degree step-core poly-add normalize termination-theorem)
  `(progn
     (defun ,core (quotient remainder divisor)
       (declare
        (xargs :measure (len remainder)
               :hints (("Goal" :use ((:instance ,termination-theorem))
                        :in-theory (disable ,step-core)))))
       (if (and (,canonical quotient) (,canonical remainder)
                (,canonical divisor) (consp remainder) (consp divisor)
                (<= (,degree divisor) (,degree remainder)))
           (let* ((step (,step-core remainder divisor))
                  (term (car step))
                  (next (cdr step)))
             (,core (,poly-add quotient term) next divisor))
         (cons quotient remainder)))
     (defun ,divmod (f g)
       (let ((f (,normalize f)) (g (,normalize g)))
         (let ((result (,core nil f g)))
           (mv (car result) (cdr result)))))))
