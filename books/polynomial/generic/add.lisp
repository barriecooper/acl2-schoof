(in-package "GPOLY")
(include-book "base")

; Missing coefficients are field zero.  Atomic tails terminate recursion and
; are discarded by FIX-COEFFICIENTS, consistently with the foundation.
(def-add-instance raw-add poly-add fix-coefficients normalize
                  gfield::field-add)
(def-neg-sub-instance raw-neg poly-neg poly-sub poly-add normalize
                      gfield::field-neg)

(defthm true-listp-of-raw-add
  (true-listp (raw-add x y)))

(defthm coefficient-list-p-of-raw-add
  (coefficient-list-p (raw-add x y)))

(defthm len-of-raw-add
  (equal (len (raw-add x y))
         (max (len x) (len y))))

(defthm raw-add-of-nil-left
  (equal (raw-add nil x) (fix-coefficients x)))

(defthm raw-add-of-nil-right
  (equal (raw-add x nil) (fix-coefficients x)))

(defthm raw-add-of-fix-coefficients
  (equal (raw-add (fix-coefficients x) (fix-coefficients y))
         (raw-add x y)))

(defthm true-listp-of-raw-neg
  (true-listp (raw-neg x)))

(defthm coefficient-list-p-of-raw-neg
  (coefficient-list-p (raw-neg x)))

(defthm len-of-raw-neg
  (equal (len (raw-neg x)) (len x)))

(defthm raw-neg-of-nil
  (equal (raw-neg nil) nil))

(defthm raw-neg-of-fix-coefficients
  (equal (raw-neg (fix-coefficients x)) (raw-neg x)))

(defthm canonical-polynomial-p-of-poly-add
  (canonical-polynomial-p (poly-add x y)))

(defthm canonical-polynomial-p-of-poly-neg
  (canonical-polynomial-p (poly-neg x)))

(defthm canonical-polynomial-p-of-poly-sub
  (canonical-polynomial-p (poly-sub x y)))

(defthm polynomial-p-of-poly-add
  (polynomial-p (poly-add x y)))

(defthm polynomial-p-of-poly-neg
  (polynomial-p (poly-neg x)))

(defthm polynomial-p-of-poly-sub
  (polynomial-p (poly-sub x y)))

(defthm field-add-interchange
  (equal (gfield::field-add x (gfield::field-add y z))
         (gfield::field-add y (gfield::field-add x z)))
  :hints (("Goal"
           :use ((:instance gfield::field-add-associative (x x) (y y) (z z))
                 (:instance gfield::field-add-associative (x y) (y x) (z z))
                 (:instance gfield::field-add-commutative (x x) (y y)))
           :in-theory (disable gfield::field-add-associative
                               gfield::field-add-commutative))))

(defthm field-neg-of-add
  (equal (gfield::field-neg (gfield::field-add x y))
         (gfield::field-add (gfield::field-neg x)
                            (gfield::field-neg y)))
  :hints (("Goal"
           :use ((:instance gfield::field-additive-inverse-unique
                            (x (gfield::field-add x y))
                            (y (gfield::field-add (gfield::field-neg x)
                                                 (gfield::field-neg y))))
                 (:instance field-add-interchange
                            (x y) (y (gfield::field-neg x))
                            (z (gfield::field-neg y))))
           :in-theory (enable gfield::field-add-associative
                              field-add-interchange))))

(defthm field-mul-of-neg-right
  (equal (gfield::field-mul x (gfield::field-neg y))
         (gfield::field-neg (gfield::field-mul x y)))
  :hints (("Goal"
           :use ((:instance gfield::field-additive-inverse-unique
                            (x (gfield::field-mul x y))
                            (y (gfield::field-mul x (gfield::field-neg y))))
                 (:instance gfield::field-mul-left-distributive
                            (x x) (y y) (z (gfield::field-neg y))))
           :in-theory (disable gfield::field-mul-left-distributive))))

(defthm equal-field-neg-zero
  (equal (equal (gfield::field-neg x) (gfield::field-zero))
         (equal (gfield::field-fix x) (gfield::field-zero)))
  :hints (("Goal" :use ((:instance gfield::field-add-left-cancel
                          (x (gfield::field-neg x))
                          (y x) (z (gfield::field-zero)))))))

(defthm eval-of-raw-add
  (equal (eval (raw-add x y) a)
         (gfield::field-add (eval x a) (eval y a)))
  :hints (("Goal" :induct (raw-add x y)
           :in-theory (enable gfield::field-mul-left-distributive
                              gfield::field-add-associative
                              field-add-interchange))))

(defthm eval-of-poly-add
  (equal (eval (poly-add x y) a)
         (gfield::field-add (eval x a) (eval y a))))

(defthm eval-of-raw-neg
  (equal (eval (raw-neg x) a)
         (gfield::field-neg (eval x a))))

(defthm eval-of-poly-neg
  (equal (eval (poly-neg x) a)
         (gfield::field-neg (eval x a))))

(defthm eval-of-poly-sub
  (equal (eval (poly-sub x y) a)
         (gfield::field-sub (eval x a) (eval y a))))

(defthm raw-add-commutative
  (equal (raw-add x y) (raw-add y x))
  :hints (("Goal" :induct (raw-add x y)
           :in-theory (enable gfield::field-add-commutative))))

(defun raw-add-induct3 (x y z)
  (declare (xargs :measure (+ (len x) (len y) (len z))))
  (if (or (consp x) (consp y) (consp z))
      (raw-add-induct3 (if (consp x) (cdr x) nil)
                       (if (consp y) (cdr y) nil)
                       (if (consp z) (cdr z) nil))
    nil))

(defthm raw-add-associative
  (implies (and (coefficient-list-p x)
                (coefficient-list-p y)
                (coefficient-list-p z))
           (equal (raw-add (raw-add x y) z)
                  (raw-add x (raw-add y z))))
  :hints (("Goal" :induct (raw-add-induct3 x y z)
           :in-theory (e/d (raw-add gfield::field-add-associative)
                             (raw-add-commutative)))))

(defthm poly-add-of-nil-left
  (equal (poly-add nil x) (normalize x)))

(defthm poly-add-of-nil-right
  (equal (poly-add x nil) (normalize x)))

(defthm poly-add-zero-left
  (implies (canonical-polynomial-p x)
           (equal (poly-add nil x) x)))

(defthm poly-add-zero-right
  (implies (canonical-polynomial-p x)
           (equal (poly-add x nil) x)))

(defthm poly-add-commutative
  (equal (poly-add x y) (poly-add y x)))

; Normalizing either operand cannot change canonical coefficientwise addition.
(defthm trim-not-consp-when-coefficient-list-p
  (implies (and (coefficient-list-p x)
                (not (consp (trim-trailing-zeros x))))
           (equal (trim-trailing-zeros x) nil)))

(defthm normalize-raw-add-zero-left
  (implies (and (polynomial-p x)
                (polynomial-p y)
                (equal (normalize x) nil))
           (equal (normalize (raw-add x y)) (normalize y)))
  :hints (("Goal" :induct (raw-add x y)
           :in-theory (disable raw-add-commutative))))

(defthm normalize-raw-add-normalize-left
  (implies (and (polynomial-p x) (polynomial-p y))
           (equal (normalize (raw-add (normalize x) y))
                  (normalize (raw-add x y))))
  :hints (("Goal" :induct (raw-add x y)
           :in-theory (disable raw-add-commutative))))

(defthm normalize-raw-add-normalize-right
  (implies (and (polynomial-p x) (polynomial-p y))
           (equal (normalize (raw-add x (normalize y)))
                  (normalize (raw-add x y))))
  :hints (("Goal" :use ((:instance normalize-raw-add-normalize-left
                          (x y) (y x)))
           :in-theory (disable normalize-raw-add-normalize-left))))

(defthm poly-add-normalize-left
  (equal (poly-add (normalize x) y) (poly-add x y))
  :hints (("Goal" :in-theory (enable poly-add))))

(defthm poly-add-normalize-right
  (equal (poly-add x (normalize y)) (poly-add x y))
  :hints (("Goal" :in-theory (enable poly-add))))

(defthm poly-add-associative
  (implies (and (polynomial-p x) (polynomial-p y) (polynomial-p z))
           (equal (poly-add (poly-add x y) z)
                  (poly-add x (poly-add y z))))
  :hints (("Goal" :use ((:instance normalize-raw-add-normalize-left
                          (x (raw-add (normalize x) (normalize y)))
                          (y (normalize z)))
                         (:instance normalize-raw-add-normalize-right
                          (x (normalize x))
                          (y (raw-add (normalize y) (normalize z))))
                         (:instance raw-add-associative
                          (x (normalize x)) (y (normalize y))
                          (z (normalize z))))
           :in-theory (disable raw-add-commutative))))

(defthm poly-add-inverse-right
  (implies (polynomial-p x)
           (equal (poly-add x (poly-neg x)) nil)))

(defthm poly-neg-of-nil
  (equal (poly-neg nil) nil))

(defthm poly-neg-of-normalize
  (equal (poly-neg (normalize x)) (poly-neg x))
  :hints (("Goal" :in-theory (enable poly-neg))))

(defthm poly-neg-of-poly-neg
  (implies (polynomial-p x)
           (equal (poly-neg (poly-neg x)) (normalize x))))

(defthm poly-neg-double-canonical
  (implies (canonical-polynomial-p x)
           (equal (poly-neg (poly-neg x)) x)))

(defthm poly-sub-definition
  (equal (poly-sub x y) (poly-add x (poly-neg y))))

(defthm poly-sub-zero
  (implies (canonical-polynomial-p x)
           (equal (poly-sub x nil) x)))

(defthm poly-sub-self
  (implies (polynomial-p x)
           (equal (poly-sub x x) nil)))
