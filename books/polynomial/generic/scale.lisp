(in-package "GPOLY")
(include-book "add")

; Coefficientwise scalar multiplication is raw; the public boundary fixes and
; canonicalizes both inputs according to the existing GPOLY policy.
(def-scale-instance raw-scale poly-scale normalize
                    gfield::field-fix gfield::field-mul)

(defthm raw-scale-when-atom
  (implies (atom x) (equal (raw-scale a x) nil)))

(defthm raw-scale-of-cons
  (equal (raw-scale a (cons c x))
         (cons (gfield::field-mul (gfield::field-fix a)
                                  (gfield::field-fix c))
               (raw-scale a x))))

(defthm true-listp-of-raw-scale
  (true-listp (raw-scale a x)))

(defthm coefficient-list-p-of-raw-scale
  (coefficient-list-p (raw-scale a x)))

(defthm raw-scale-of-field-fix
  (equal (raw-scale (gfield::field-fix a) x) (raw-scale a x)))

(defthm raw-scale-of-fix-coefficients
  (equal (raw-scale a (fix-coefficients x)) (raw-scale a x)))

(defthm canonical-polynomial-p-of-poly-scale
  (canonical-polynomial-p (poly-scale a x)))

(defthm polynomial-p-of-poly-scale
  (polynomial-p (poly-scale a x)))

(defthm poly-scale-of-field-fix
  (equal (poly-scale (gfield::field-fix a) x) (poly-scale a x)))

(defthm poly-scale-of-normalize
  (equal (poly-scale a (normalize x)) (poly-scale a x)))

(defthm poly-scale-of-fix-coefficients
  (equal (poly-scale a (fix-coefficients x)) (poly-scale a x)))

(defthm field-mul-interchange
  (equal (gfield::field-mul x (gfield::field-mul a y))
         (gfield::field-mul a (gfield::field-mul x y)))
  :hints (("Goal"
           :use ((:instance gfield::field-mul-associative
                            (x x) (y a) (z y))
                 (:instance gfield::field-mul-associative
                            (x a) (y x) (z y))
                 (:instance gfield::field-mul-commutative (x x) (y a)))
           :in-theory (disable gfield::field-mul-associative
                               gfield::field-mul-commutative))))

(defthm eval-of-raw-scale
  (equal (eval (raw-scale a poly) x)
         (gfield::field-mul a (eval poly x)))
  :hints (("Goal" :induct (raw-scale a poly)
           :in-theory (enable gfield::field-mul-left-distributive
                              field-mul-interchange))))

(defthm eval-of-poly-scale
  (equal (eval (poly-scale a poly) x)
         (gfield::field-mul a (eval poly x))))

(defthm raw-scale-by-zero
  (equal (raw-scale (gfield::field-zero) x)
         (if (consp x)
             (cons (gfield::field-zero)
                   (raw-scale (gfield::field-zero) (cdr x)))
           nil)))

(defthm normalize-of-raw-scale-by-zero
  (equal (normalize (raw-scale (gfield::field-zero) x)) nil)
  :hints (("Goal" :induct (raw-scale (gfield::field-zero) x)
           :in-theory (e/d (normalize trim-trailing-zeros fix-coefficients)
                           (raw-scale-by-zero)))))

(defthm poly-scale-by-zero
  (equal (poly-scale (gfield::field-zero) x) nil)
  :hints (("Goal" :in-theory (disable raw-scale-by-zero))))

(defthm poly-scale-of-nil
  (equal (poly-scale a nil) nil))

(defthm raw-scale-by-one
  (equal (raw-scale (gfield::field-one) x) (fix-coefficients x)))

(defthm poly-scale-by-one
  (equal (poly-scale (gfield::field-one) x) (normalize x)))

(defthm poly-scale-by-one-when-canonical
  (implies (canonical-polynomial-p x)
           (equal (poly-scale (gfield::field-one) x) x)))

(defthm raw-scale-nested
  (equal (raw-scale a (raw-scale b x))
         (raw-scale (gfield::field-mul a b) x))
  :hints (("Goal" :induct (raw-scale b x)
           :in-theory (enable gfield::field-mul-associative))))

(defthm equal-field-mul-zero
  (equal (equal (gfield::field-mul a x) (gfield::field-zero))
         (or (equal (gfield::field-fix a) (gfield::field-zero))
             (equal (gfield::field-fix x) (gfield::field-zero))))
  :hints (("Goal"
           :cases ((equal (gfield::field-fix a) (gfield::field-zero)))
           :use ((:instance gfield::field-mul-left-cancel
                            (x a) (y x) (z (gfield::field-zero)))
                 (:instance gfield::field-mul-fixed-congruence
                            (x1 a) (x2 (gfield::field-zero))
                            (y1 x) (y2 x))))))

(defthm normalize-raw-scale-of-normalize
  (equal (normalize (raw-scale a (normalize x)))
         (normalize (raw-scale a x)))
  :hints (("Goal" :induct (raw-scale a x))))

(defthm poly-scale-nested
  (equal (poly-scale a (poly-scale b x))
         (poly-scale (gfield::field-mul a b) x))
  :rule-classes nil)

(defthm raw-scale-of-raw-add
  (equal (raw-scale a (raw-add x y))
         (raw-add (raw-scale a x) (raw-scale a y)))
  :hints (("Goal" :induct (raw-add x y)
           :in-theory (enable gfield::field-mul-left-distributive))))

(defthm poly-scale-of-poly-add
  (equal (poly-scale a (poly-add x y))
         (poly-add (poly-scale a x) (poly-scale a y)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance normalize-raw-scale-of-normalize
                            (x (raw-add (normalize x) (normalize y))))
                 (:instance raw-scale-of-raw-add
                            (x (normalize x)) (y (normalize y)))
                 (:instance normalize-raw-add-normalize-left
                            (x (raw-scale a (normalize x)))
                            (y (normalize (raw-scale a (normalize y)))))
                 (:instance normalize-raw-add-normalize-right
                            (x (raw-scale a (normalize x)))
                            (y (raw-scale a (normalize y)))))
           :in-theory (e/d (poly-scale poly-add)
                           (normalize-raw-scale-of-normalize
                            raw-scale-of-raw-add
                            normalize-raw-add-normalize-left
                            normalize-raw-add-normalize-right)))))

(defthm raw-scale-of-field-add
  (equal (raw-scale (gfield::field-add a b) x)
         (raw-add (raw-scale a x) (raw-scale b x)))
  :hints (("Goal" :induct (raw-scale a x)
           :in-theory (enable gfield::field-mul-right-distributive))))

(defthm poly-scale-of-field-add
  (equal (poly-scale (gfield::field-add a b) x)
         (poly-add (poly-scale a x) (poly-scale b x)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance raw-scale-of-field-add (x (normalize x)))
                 (:instance normalize-raw-add-normalize-left
                            (x (raw-scale a (normalize x)))
                            (y (normalize (raw-scale b (normalize x)))))
                 (:instance normalize-raw-add-normalize-right
                            (x (raw-scale a (normalize x)))
                            (y (raw-scale b (normalize x)))))
           :in-theory (e/d (poly-scale poly-add)
                           (raw-scale-of-field-add
                            normalize-raw-add-normalize-left
                            normalize-raw-add-normalize-right)))))
