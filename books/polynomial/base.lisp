(in-package "HS")
(include-book "kestrel/arithmetic-light/mod" :dir :system)
(include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)

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

(defthm field-polynomial-p-when-atom
  (implies (not (consp x))
           (equal (field-polynomial-p x p) (null x))))

(defthm field-polynomial-p-implies-true-listp
  (implies (field-polynomial-p xs p)
           (true-listp xs)))

(defthm canonical-polynomial-p-implies-field-polynomial-p
  (implies (canonical-polynomial-p xs p)
           (field-polynomial-p xs p)))

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

; Raw scalar multiplication multiplies every coefficient by A.  It is one
; ingredient of convolution and intentionally does not normalize its result.
(defun poly-scale-raw (a x p)
  (if (endp x) nil
    (cons (pfield::mul a (car x) p)
          (poly-scale-raw a (cdr x) p))))

; Prepending zero multiplies a coefficient list by the indeterminate.  With the
; constant coefficient first, convolution by (a . rest) is a*y plus x*(rest*y).
(defun poly-mul-raw (x y p)
  (if (or (endp x) (endp y)) nil
    (poly-add-raw (poly-scale-raw (car x) y p)
                  (cons 0 (poly-mul-raw (cdr x) y p)) p)))

; The public operation removes high-degree zeroes produced by field arithmetic.
(defun poly-mul (x y p)
  (poly-normalize (poly-mul-raw x y p)))

; The canonical constant polynomial one.
(defun poly-one ()
  '(1))

(defthm true-listp-of-poly-scale-raw
  (true-listp (poly-scale-raw a x p)))

(defthm true-listp-of-poly-mul-raw
  (implies (and (true-listp x) (true-listp y))
           (true-listp (poly-mul-raw x y p))))

(defthm poly-scale-raw-preserves-field-polynomial-p
  (implies (and (pfield::fep a p)
                (field-polynomial-p x p)
                (posp p))
           (field-polynomial-p (poly-scale-raw a x p) p)))

(defthm poly-mul-raw-preserves-field-polynomial-p
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (posp p))
           (field-polynomial-p (poly-mul-raw x y p) p)))

(defthm poly-mul-is-canonical
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (posp p))
           (canonical-polynomial-p (poly-mul x y p) p)))

(defthm poly-mul-of-nil-left
  (equal (poly-mul nil x p) nil))

(defthm poly-mul-of-nil-right
  (equal (poly-mul x nil p) nil))

(defthm poly-scale-raw-by-one
  (implies (and (field-polynomial-p x p)
                (posp p))
           (equal (poly-scale-raw 1 x p) x)))

(defthm poly-mul-raw-by-one-left
  (implies (and (field-polynomial-p x p)
                (posp p))
           (equal (poly-mul-raw (poly-one) x p) x)))

(defthm poly-mul-by-one-left
  (implies (and (field-polynomial-p x p)
                (posp p))
           (equal (poly-mul (poly-one) x p)
                  (poly-normalize x))))

(defthm poly-mul-one-left-identity
  (implies (and (canonical-polynomial-p x p)
                (posp p))
           (equal (poly-mul (poly-one) x p) x))
  :hints (("Goal" :use ((:instance poly-mul-by-one-left)
                         (:instance canonical-polynomial-is-normalized))
                    :in-theory (disable poly-mul poly-one))))

(defthm poly-scale-raw-of-poly-add-raw
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (pfield::fep a p)
                (posp p))
           (equal (poly-scale-raw a (poly-add-raw x y p) p)
                  (poly-add-raw (poly-scale-raw a x p)
                                (poly-scale-raw a y p) p))))

(defthm poly-scale-raw-scalars-commute
  (implies (and (field-polynomial-p x p)
                (pfield::fep a p)
                (pfield::fep b p)
                (posp p))
           (equal (poly-scale-raw a (poly-scale-raw b x p) p)
                  (poly-scale-raw b (poly-scale-raw a x p) p)))
  :hints (("Goal" :in-theory (enable pfield::mul-commutative
                                      pfield::mul-associative))))

(defthm poly-add-raw-interchange
  (implies (and (true-listp a) (true-listp b)
                (true-listp c) (true-listp d))
           (equal (poly-add-raw (poly-add-raw a b p)
                                (poly-add-raw c d p) p)
                  (poly-add-raw (poly-add-raw a c p)
                                (poly-add-raw b d p) p)))
  :hints (("Goal" :in-theory (enable pfield::add-associative
                                      pfield::add-commutative))))

(defthm poly-add-raw-commutative-2
  (implies (and (true-listp a) (true-listp b) (true-listp c))
           (equal (poly-add-raw a (poly-add-raw b c p) p)
                  (poly-add-raw b (poly-add-raw a c p) p)))
  :hints (("Goal" :in-theory (enable pfield::add-associative
                                      pfield::add-commutative))))

(defthm poly-mul-raw-by-singleton-right
  (implies (and (field-polynomial-p x p)
                (pfield::fep a p)
                (posp p))
           (equal (poly-mul-raw x (list a) p)
                  (poly-scale-raw a x p)))
  :hints (("Goal" :induct (field-polynomial-p x p)
                    :in-theory (e/d (pfield::mul-commutative)
                                    (pfield::add-of-0-arg1
                                     pfield::add-of-0-arg2
                                     pfield::add-of-0-arg1-gen
                                     pfield::add-of-0-arg2-gen)))))

(defthm poly-mul-raw-right-recursion
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (pfield::fep a p)
                (posp p))
           (equal (poly-mul-raw x (cons a y) p)
                  (if (endp x) nil
                    (poly-add-raw (poly-scale-raw a x p)
                                  (cons 0 (poly-mul-raw x y p)) p))))
  :hints (("Goal" :induct (field-polynomial-p x p)
                    :do-not '(generalize)
                    :in-theory (e/d (pfield::add-associative
                                        pfield::add-commutative
                                        pfield::mul-commutative)
                                       (pfield::add-of-0-arg1
                                        pfield::add-of-0-arg2
                                        pfield::add-of-0-arg1-gen
                                        pfield::add-of-0-arg2-gen
                                        pfield::fep-holds)))))

(defthm poly-mul-raw-commutative
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (posp p))
           (equal (poly-mul-raw x y p)
                  (poly-mul-raw y x p)))
  :hints (("Goal" :induct (poly-mul-raw x y p))))

(defthm poly-mul-commutative
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (posp p))
           (equal (poly-mul x y p)
                  (poly-mul y x p))))

(defthm poly-mul-by-one-right
  (implies (and (field-polynomial-p x p)
                (posp p))
           (equal (poly-mul x (poly-one) p)
                  (poly-normalize x)))
  :hints (("Goal" :use ((:instance poly-mul-commutative
                                   (y (poly-one)))))))

(defthm poly-mul-one-right-identity
  (implies (and (canonical-polynomial-p x p)
                (posp p))
           (equal (poly-mul x (poly-one) p) x)))

(defthm poly-mul-raw-right-distributive
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (field-polynomial-p z p)
                (posp p))
           (equal (poly-mul-raw x (poly-add-raw y z p) p)
                  (poly-add-raw (poly-mul-raw x y p)
                                (poly-mul-raw x z p) p)))
  :hints (("Goal" :induct (field-polynomial-p x p)
                    :in-theory (disable pfield::add-of-0-arg1-gen
                                        pfield::add-of-0-arg2-gen))))

(defthm poly-mul-raw-left-distributive
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (field-polynomial-p z p)
                (posp p))
           (equal (poly-mul-raw (poly-add-raw x y p) z p)
                  (poly-add-raw (poly-mul-raw x z p)
                                (poly-mul-raw y z p) p)))
  :hints (("Goal" :use ((:instance poly-mul-raw-commutative
                                   (x (poly-add-raw x y p)) (y z))
                         (:instance poly-mul-raw-commutative (x x) (y z))
                         (:instance poly-mul-raw-commutative (x y) (y z))
                         (:instance poly-mul-raw-right-distributive
                                    (x z) (y x) (z y))))))

(defthm field-polynomial-p-of-zero-cons
  (implies (posp p)
           (equal (field-polynomial-p (cons 0 x) p)
                  (field-polynomial-p x p))))

(defthm poly-normalize-of-poly-scale-raw-zero
  (implies (and (field-polynomial-p x p)
                (posp p))
           (equal (poly-normalize (poly-scale-raw 0 x p)) nil)))

(defthm poly-normalize-of-zero-cons
  (equal (poly-normalize (cons 0 x))
         (if (poly-normalize x)
             (cons 0 (poly-normalize x))
           nil)))

(defthm poly-normalize-add-raw-congruence-right
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p a p)
                (field-polynomial-p b p)
                (posp p)
                (equal (poly-normalize a) (poly-normalize b)))
           (equal (poly-normalize (poly-add-raw x a p))
                  (poly-normalize (poly-add-raw x b p))))
  :hints (("Goal" :use ((:instance poly-add-normalize-right (y a))
                         (:instance poly-add-normalize-right (y b)))))
  :rule-classes nil)

(defthm poly-add-is-normalized
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (posp p))
           (equal (poly-normalize (poly-add x y p))
                  (poly-add x y p))))

(defthm poly-normalize-of-poly-add-raw
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (posp p))
           (equal (poly-normalize (poly-add-raw x y p))
                  (poly-add (poly-normalize x) (poly-normalize y) p)))
  :hints (("Goal" :use ((:instance poly-add-normalization-compatible))))
  :rule-classes nil)

(defthm poly-scale-raw-associative
  (implies (and (field-polynomial-p x p)
                (pfield::fep a p)
                (pfield::fep b p)
                (posp p))
           (equal (poly-scale-raw (pfield::mul a b p) x p)
                  (poly-scale-raw a (poly-scale-raw b x p) p)))
  :hints (("Goal" :in-theory (enable pfield::mul-associative))))

(defthm poly-mul-raw-of-poly-scale-raw-left
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (pfield::fep a p)
                (posp p))
           (equal (poly-mul-raw (poly-scale-raw a x p) y p)
                  (poly-scale-raw a (poly-mul-raw x y p) p)))
  :hints (("Goal" :induct (field-polynomial-p x p)
                    :in-theory (enable pfield::mul-associative))))

(defthm len-of-poly-scale-raw
  (equal (len (poly-scale-raw a x p))
         (len x)))

(defthm len-of-poly-add-raw
  (implies (and (true-listp x) (true-listp y))
           (equal (len (poly-add-raw x y p))
                  (max (len x) (len y)))))

(defthm len-of-poly-mul-raw
  (implies (and (true-listp x) (true-listp y))
           (equal (len (poly-mul-raw x y p))
                  (if (or (endp x) (endp y))
                      0
                    (+ -1 (len x) (len y))))))

(defthm len-poly-add-raw-lower-bound-left
  (implies (and (true-listp x) (true-listp y))
           (<= (len x) (len (poly-add-raw x y p))))
  :rule-classes :linear)

(defthm len-poly-add-raw-lower-bound-right
  (implies (and (true-listp x) (true-listp y))
           (<= (len y) (len (poly-add-raw x y p))))
  :rule-classes :linear)

(defthm len-poly-mul-raw-lower-bound-right
  (implies (and (true-listp x) (true-listp y)
                (consp x) (consp y))
           (<= (len y) (len (poly-mul-raw x y p))))
  :rule-classes :linear)

(defthm poly-add-raw-of-zero-scale-left
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (posp p)
                (<= (len x) (len y)))
           (equal (poly-add-raw (poly-scale-raw 0 x p) y p)
                  y))
  :hints (("Goal" :induct (poly-add-raw x y p)
                    :in-theory (disable poly-add-raw-commutative))))

(defthm poly-add-raw-zero-scale-before-product
  (implies (and (field-polynomial-p y p)
                (field-polynomial-p z p)
                (field-polynomial-p rest p)
                (pfield::fep a p)
                (posp p)
                (consp y) (consp z))
           (equal (poly-add-raw
                   (poly-scale-raw 0 z p)
                   (poly-add-raw (poly-scale-raw a (poly-mul-raw y z p) p)
                                 rest p) p)
                  (poly-add-raw (poly-scale-raw a (poly-mul-raw y z p) p)
                                rest p)))
  :hints (("Goal"
           :use ((:instance poly-add-raw-of-zero-scale-left
                            (x z)
                            (y (poly-add-raw
                                (poly-scale-raw a (poly-mul-raw y z p) p)
                                rest p)))
                 (:instance len-poly-mul-raw-lower-bound-right
                            (x y) (y z))
                 (:instance len-poly-add-raw-lower-bound-left
                            (x (poly-scale-raw a (poly-mul-raw y z p) p))
                            (y rest)))
           :in-theory (disable poly-add-raw
                               poly-scale-raw
                               poly-mul-raw
                               poly-add-raw-commutative))))

(defthm poly-mul-raw-associative
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (field-polynomial-p z p)
                (posp p))
           (equal (poly-mul-raw (poly-mul-raw x y p) z p)
                  (poly-mul-raw x (poly-mul-raw y z p) p)))
  :hints (("Goal" :induct (field-polynomial-p x p)
                    :in-theory (disable pfield::add-of-0-arg1-gen
                                        pfield::add-of-0-arg2-gen))))

(defthm poly-mul-associative-raw-operands
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (field-polynomial-p z p)
                (posp p))
           (equal (poly-mul (poly-mul-raw x y p) z p)
                  (poly-mul x (poly-mul-raw y z p) p)))
  :hints (("Goal" :use ((:instance poly-mul-raw-associative)))))

(defthm poly-mul-right-distributive-raw-add
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (field-polynomial-p z p)
                (posp p))
           (equal (poly-mul x (poly-add-raw y z p) p)
                  (poly-add (poly-mul-raw x y p)
                            (poly-mul-raw x z p) p)))
  :hints (("Goal" :use ((:instance poly-mul-raw-right-distributive)))))

(defthm poly-normalize-add-raw-zero-scale-left
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (posp p))
           (equal (poly-normalize
                   (poly-add-raw (poly-scale-raw 0 x p) y p))
                  (poly-normalize y)))
  :hints (("Goal" :use ((:instance poly-add-normalize-left
                                   (x (poly-scale-raw 0 x p)))
                         (:instance poly-normalize-of-poly-scale-raw-zero)))))

(defthm poly-mul-normalize-left
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (posp p))
           (equal (poly-mul (poly-normalize x) y p)
                  (poly-mul x y p)))
  :hints (("Goal" :induct (field-polynomial-p x p)
                    :in-theory (disable poly-mul-raw-commutative
                                        pfield::add-of-0-arg1-gen
                                        pfield::add-of-0-arg2-gen))
           ("Subgoal *1/2.6'"
            :use ((:instance poly-normalize-add-raw-congruence-right
                             (x (poly-scale-raw (car x) y p))
                             (a (cons 0 (poly-mul-raw (poly-normalize (cdr x)) y p)))
                             (b (cons 0 (poly-mul-raw (cdr x) y p)))))
)
           ("Subgoal *1/2.4'"
            :use ((:instance poly-normalize-add-raw-congruence-right
                             (x (poly-scale-raw (car x) y p))
                             (a (cons 0 (poly-mul-raw (poly-normalize (cdr x)) y p)))
                             (b (cons 0 (poly-mul-raw (cdr x) y p)))))
)))

(defthm poly-mul-normalize-right
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (posp p))
           (equal (poly-mul x (poly-normalize y) p)
                  (poly-mul x y p)))
  :hints (("Goal" :use ((:instance poly-mul-commutative
                                   (x (poly-normalize y)) (y x))
                         (:instance poly-mul-commutative (x y) (y x))
                         (:instance poly-mul-normalize-left (x y) (y x))))))

(defthm poly-mul-normalization-compatible
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (posp p))
           (equal (poly-mul (poly-normalize x) (poly-normalize y) p)
                  (poly-mul x y p)))
  :hints (("Goal" :use ((:instance poly-mul-normalize-left
                                   (y (poly-normalize y)))
                         (:instance poly-mul-normalize-right))
                    :in-theory (disable poly-mul-normalize-left
                                        poly-mul-normalize-right))))

(defthm poly-mul-associative
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (field-polynomial-p z p)
                (posp p))
           (equal (poly-mul (poly-mul x y p) z p)
                  (poly-mul x (poly-mul y z p) p)))
  :hints (("Goal" :use ((:instance poly-mul-associative-raw-operands)
                         (:instance poly-mul-normalize-left
                                    (x (poly-mul-raw x y p)) (y z))
                         (:instance poly-mul-normalize-right
                                    (x x) (y (poly-mul-raw y z p)))))))

(defthm poly-mul-right-distributive
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (field-polynomial-p z p)
                (posp p))
           (equal (poly-mul x (poly-add y z p) p)
                  (poly-add (poly-mul x y p)
                            (poly-mul x z p) p)))
  :hints (("Goal" :use ((:instance poly-mul-right-distributive-raw-add)
                         (:instance poly-mul-normalize-right
                                    (y (poly-add-raw y z p)))
                         (:instance poly-add-normalize-left
                                    (x (poly-mul-raw x y p))
                                    (y (poly-mul-raw x z p)))
                         (:instance poly-add-normalize-right
                                    (x (poly-mul x y p))
                                    (y (poly-mul-raw x z p)))))))

(defthm poly-mul-left-distributive
  (implies (and (field-polynomial-p x p)
                (field-polynomial-p y p)
                (field-polynomial-p z p)
                (posp p))
           (equal (poly-mul (poly-add x y p) z p)
                  (poly-add (poly-mul x z p)
                            (poly-mul y z p) p)))
  :hints (("Goal" :use ((:instance poly-mul-commutative
                                   (x (poly-add x y p)) (y z))
                         (:instance poly-mul-commutative (x x) (y z))
                         (:instance poly-mul-commutative (x y) (y z))
                         (:instance poly-mul-right-distributive
                                    (x z) (y x) (z y))))))
