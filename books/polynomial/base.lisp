(in-package "HS")

; Coefficients are low-to-high.  NIL is the unique zero polynomial.
(defun poly-normalize (xs)
  (if (atom xs) nil
    (let ((tail (poly-normalize (cdr xs))))
      (if (and (equal (car xs) 0) (endp tail)) nil
        (cons (car xs) tail)))))

(defun field-poly-p (xs p)
  (if (atom xs) (null xs)
    (and (pfield::fep (car xs) p)
         (field-poly-p (cdr xs) p)
         (or (consp (cdr xs)) (not (equal (car xs) 0))))))

(defun poly-add (x y p)
  (declare (xargs :measure (+ (len x) (len y))
                  :ruler-extenders :all))
  (poly-normalize
   (cond ((endp x) y) ((endp y) x)
         (t (cons (pfield::add (car x) (car y) p)
                  (poly-add (cdr x) (cdr y) p))))))

(defun scale-poly (a x p)
  (if (endp x) nil
    (cons (pfield::mul a (car x) p) (scale-poly a (cdr x) p))))

(defun poly-mul (x y p)
  (if (or (endp x) (endp y)) nil
    (poly-add (scale-poly (car x) y p)
              (cons 0 (poly-mul (cdr x) y p)) p)))

(defthm normalize-idempotent
  (equal (poly-normalize (poly-normalize x)) (poly-normalize x)))
