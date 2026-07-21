(in-package "HS")

; A list (c0 ... cn) represents c0 + c1*x + ... + cn*x^n.
; Thus the constant coefficient comes first.  NIL is the unique canonical
; representation of the zero polynomial.
(defun poly-normalize (xs)
  (if (atom xs) nil
    (let ((tail (poly-normalize (cdr xs))))
      (if (and (equal (car xs) 0) (endp tail)) nil
        (cons (car xs) tail)))))

(defun field-polynomial-p (xs p)
  (if (atom xs) (null xs)
    (and (pfield::fep (car xs) p)
         (field-polynomial-p (cdr xs) p))))

(defun canonical-polynomial-p (xs p)
  (if (atom xs) (null xs)
    (and (pfield::fep (car xs) p)
         (canonical-polynomial-p (cdr xs) p)
         (or (consp (cdr xs)) (not (equal (car xs) 0))))))

; Compatibility name for the canonical field-polynomial recognizer.
(defun field-poly-p (xs p)
  (canonical-polynomial-p xs p))

(defthm poly-normalize-preserves-field-polynomial-p
  (implies (field-polynomial-p xs p)
           (field-polynomial-p (poly-normalize xs) p)))

(defthm poly-normalize-is-canonical
  (implies (field-polynomial-p xs p)
           (canonical-polynomial-p (poly-normalize xs) p)))

(defthm canonical-polynomial-is-normalized
  (implies (canonical-polynomial-p xs p)
           (equal (poly-normalize xs) xs)))

(defthm poly-normalize-of-zero
  (equal (poly-normalize nil) nil))

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
