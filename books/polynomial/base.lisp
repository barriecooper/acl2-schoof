(in-package "HS")
(include-book "kestrel/arithmetic-light/mod" :dir :system)

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

(defthm field-polynomial-p-implies-true-listp
  (implies (field-polynomial-p xs p)
           (true-listp xs)))

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

(defthm normalize-idempotent
  (equal (poly-normalize (poly-normalize x)) (poly-normalize x)))

; Raw addition exposes the coefficientwise computation.  A missing coefficient
; is zero, so when either list ends its remaining counterpart is copied.
(defun poly-add-raw (x y p)
  (cond ((endp x) y)
        ((endp y) x)
        (t (cons (pfield::add (car x) (car y) p)
                 (poly-add-raw (cdr x) (cdr y) p)))))

; Coefficient cancellation can leave high-degree zeroes in the raw result.
; Public addition therefore restores the unique canonical representation.
(defun poly-add (x y p)
  (poly-normalize (poly-add-raw x y p)))

(defthm poly-add-raw-preserves-field-polynomial-p
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (posp p))
           (field-polynomial-p (poly-add-raw x y p) p)))

(defthm poly-add-is-canonical
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (posp p))
           (canonical-polynomial-p (poly-add x y p) p)))

(defthm poly-add-of-nil-left
  (equal (poly-add nil x p) (poly-normalize x)))

(defthm poly-add-of-nil-right
  (equal (poly-add x nil p) (poly-normalize x)))

(defthm poly-add-nil-left-identity
  (implies (canonical-polynomial-p x p)
           (equal (poly-add nil x p) x)))

(defthm poly-add-nil-right-identity
  (implies (canonical-polynomial-p x p)
           (equal (poly-add x nil p) x)))

(defthm poly-add-raw-commutative
  (implies (and (true-listp x) (true-listp y))
           (equal (poly-add-raw x y p)
                  (poly-add-raw y x p)))
  :hints (("Goal" :in-theory (enable pfield::add-commutative))))

(defthm poly-add-commutative
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p))
           (equal (poly-add x y p) (poly-add y x p))))

(defthm poly-add-raw-associative
  (implies (and (true-listp x) (true-listp y) (true-listp z))
           (equal (poly-add-raw (poly-add-raw x y p) z p)
                  (poly-add-raw x (poly-add-raw y z p) p)))
  :hints (("Goal" :in-theory (enable pfield::add-associative))))

(defthm poly-add-normalize-left
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (posp p))
           (equal (poly-add (poly-normalize x) y p)
                  (poly-add x y p)))
  :hints (("Goal" :in-theory
           (disable pfield::add-of-0-arg1-gen
                    pfield::add-of-0-arg2-gen
                    poly-add-raw-commutative))))

(defthm poly-add-normalize-right
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (posp p))
           (equal (poly-add x (poly-normalize y) p)
                  (poly-add x y p)))
  :hints (("Goal" :in-theory
           (disable pfield::add-of-0-arg1-gen
                    pfield::add-of-0-arg2-gen
                    poly-add-raw-commutative))))

(defthm poly-add-normalization-compatible
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (posp p))
           (equal (poly-add (poly-normalize x) (poly-normalize y) p)
                  (poly-add x y p))))

(defthm poly-add-associative
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (field-polynomial-p z p)
                (posp p))
           (equal (poly-add (poly-add x y p) z p)
                  (poly-add x (poly-add y z p) p)))
  :hints (("Goal"
           :use ((:instance poly-add-normalize-left
                            (x (poly-add-raw x y p)) (y z))
                 (:instance poly-add-normalize-right
                            (x x) (y (poly-add-raw y z p)))
                 (:instance poly-add-raw-associative)))))

(defun scale-poly (a x p)
  (if (endp x) nil
    (cons (pfield::mul a (car x) p) (scale-poly a (cdr x) p))))

(defun poly-mul (x y p)
  (if (or (endp x) (endp y)) nil
    (poly-add (scale-poly (car x) y p)
              (cons 0 (poly-mul (cdr x) y p)) p)))
