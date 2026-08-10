(in-package "GPOLY")

(include-book "quotient-coordinate")
(include-book "f11-division-polynomial-correspondence")

; Independent concrete F11 execution witness.  These functions use the same
; dense representation and mathematical formulas as the generic production
; boundary, but this book does not instantiate or execute QUOTIENT-COORDINATE-*
; and proves no correspondence to those generic functions.  A correspondence
; would require a substantial concrete F11 divmod/reduced-ring instantiation
; that is intentionally outside this focused boundary.
;
; Fuel is the dividend length; an active leading-term cancellation strictly
; lowers that length for the canonical nonzero modulus used below.
(defun f11-quotient-zero-prefix (n tail)
  (if (zp (nfix n)) tail
    (cons 0 (f11-quotient-zero-prefix (1- (nfix n)) tail))))

(defun f11-quotient-remainder-fuel (fuel dividend modulus)
  (declare (xargs :measure (nfix fuel)))
  (let ((dividend (f11-normalize dividend))
        (modulus (f11-normalize modulus)))
    (if (or (zp (nfix fuel)) (not (consp modulus))
            (not (consp dividend))
            (< (f11-poly-degree dividend) (f11-poly-degree modulus)))
        dividend
      (let* ((difference (- (f11-poly-degree dividend)
                            (f11-poly-degree modulus)))
             (coefficient
              (gfield::f11-div (f11-poly-leading-coefficient dividend)
                               (f11-poly-leading-coefficient modulus)))
             (term (f11-quotient-zero-prefix difference (list coefficient))))
        (f11-quotient-remainder-fuel
         (1- (nfix fuel))
         (f11-poly-sub dividend (f11-poly-mul term modulus)) modulus)))))

(defun f11-quotient-remainder (dividend modulus)
  (f11-quotient-remainder-fuel (len (f11-normalize dividend))
                               dividend modulus))

(defun f11-quotient-fix (coordinate modulus)
  (cons (f11-quotient-remainder
         (if (consp coordinate) (car coordinate) nil) modulus)
        (f11-quotient-remainder
         (if (consp coordinate) (cdr coordinate) nil) modulus)))

(defun f11-quotient-add (left right modulus)
  (let ((left (f11-quotient-fix left modulus))
        (right (f11-quotient-fix right modulus)))
    (f11-quotient-fix
     (cons (f11-poly-add (car left) (car right))
           (f11-poly-add (cdr left) (cdr right))) modulus)))

(defun f11-quotient-mul (left right a b modulus)
  (let* ((left (f11-quotient-fix left modulus))
         (right (f11-quotient-fix right modulus))
         (cubic (list (gfield::f11-fix b) (gfield::f11-fix a) 0 1)))
    (f11-quotient-fix
     (cons (f11-poly-add
            (f11-poly-mul (car left) (car right))
            (f11-poly-mul cubic (f11-poly-mul (cdr left) (cdr right))))
           (f11-poly-add (f11-poly-mul (car left) (cdr right))
                         (f11-poly-mul (cdr left) (car right))))
     modulus)))

(defun f11-quotient-regression-modulus ()
  (f11-division-polynomial 3 1 6))

(defun f11-quotient-regression-y ()
  (f11-quotient-fix (cons nil '(1)) (f11-quotient-regression-modulus)))

(assert-event
 (equal (f11-quotient-regression-modulus)
        (f11-division-polynomial-base 3 1 6)))

(assert-event
 (let* ((modulus (f11-quotient-regression-modulus))
        (fixed (f11-quotient-fix (cons '(1 2 3 4 5) '(6 7 8 9 10)) modulus)))
   (and (< (f11-poly-degree (car fixed)) (f11-poly-degree modulus))
        (< (f11-poly-degree (cdr fixed)) (f11-poly-degree modulus)))))

(assert-event
 (let* ((modulus (f11-quotient-regression-modulus))
        (left (cons '(1 0 2 0 3) '(4 1)))
        (right (cons '(2 1) '(3 0 1)))
        (sum (f11-quotient-add left right modulus))
        (product (f11-quotient-mul left right 1 6 modulus)))
   (and (consp (car sum)) (consp (cdr sum))
        (< (f11-poly-degree (car product)) (f11-poly-degree modulus))
        (< (f11-poly-degree (cdr product)) (f11-poly-degree modulus)))))

(assert-event
 (let* ((modulus (f11-quotient-regression-modulus))
        (square (f11-quotient-mul (f11-quotient-regression-y)
                                  (f11-quotient-regression-y)
                                  1 6 modulus)))
   (equal square (f11-quotient-fix (cons '(6 1 0 1) nil) modulus))))

(assert-event
 (equal (f11-quotient-fix 'malformed (f11-quotient-regression-modulus))
        (cons nil nil)))

(verify-guards f11-quotient-zero-prefix)
(verify-guards f11-quotient-remainder-fuel)
(verify-guards f11-quotient-remainder)
(verify-guards f11-quotient-fix)
(verify-guards f11-quotient-add)
(verify-guards f11-quotient-mul)
(verify-guards f11-quotient-regression-modulus)
(verify-guards f11-quotient-regression-y)
