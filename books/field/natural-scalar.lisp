(in-package "GFIELD")

(include-book "kernel")

; Additive natural scaling inside the generic field.  This is distinct from
; curve-point scalar multiplication: it supplies the coefficient n*a needed
; by generic formal differentiation.  Arbitrary counts have NFIX semantics.
(defun field-nat-mul (n x)
  (declare (xargs :measure (nfix n)))
  (let ((n (nfix n)))
    (if (zp n)
        (field-zero)
      (field-add (field-fix x)
                 (field-nat-mul (1- n) x)))))

(defthm field-nat-mul-of-nfix
  (equal (field-nat-mul (nfix n) x)
         (field-nat-mul n x)))

(defthm field-nat-mul-of-field-fix
  (equal (field-nat-mul n (field-fix x))
         (field-nat-mul n x)))

(defthm field-nat-mul-zero
  (equal (field-nat-mul 0 x) (field-zero)))

(defthm field-nat-mul-of-zero
  (equal (field-nat-mul n (field-zero)) (field-zero))
  :hints (("Goal" :induct (field-nat-mul n (field-zero))
           :in-theory (enable field-nat-mul))))

(defthm field-nat-mul-when-fixed-zero
  (implies (equal (field-fix x) (field-zero))
           (equal (field-nat-mul n x) (field-zero)))
  :hints (("Goal"
           :use ((:instance field-nat-mul-of-field-fix (x x))
                 (:instance field-nat-mul-of-zero)))))

(defthm field-nat-mul-successor-total
  (equal (field-nat-mul (+ 1 (nfix n)) x)
         (field-add x (field-nat-mul n x))))

(defthm field-nat-mul-successor
  (implies (natp n)
           (equal (field-nat-mul (+ 1 n) x)
                  (field-add x (field-nat-mul n x)))))

(defthm field-element-p-of-field-nat-mul
  (field-element-p (field-nat-mul n x)))

(defthm field-add-swap-first-two
  (equal (field-add x (field-add y z))
         (field-add y (field-add x z)))
  :hints (("Goal"
           :use ((:instance field-add-associative (x x) (y y) (z z))
                 (:instance field-add-associative (x y) (y x) (z z))
                 (:instance field-add-commutative (x x) (y y)))
           :in-theory (disable field-add-associative
                               field-add-commutative))))

(defthm field-nat-mul-of-sum
  (equal (field-nat-mul (+ (nfix m) (nfix n)) x)
         (field-add (field-nat-mul m x)
                    (field-nat-mul n x)))
  :hints (("Goal" :induct (field-nat-mul m x)
           :in-theory (enable field-nat-mul field-add-swap-first-two))))

(defthm field-nat-mul-of-add
  (equal (field-nat-mul n (field-add x y))
         (field-add (field-nat-mul n x)
                    (field-nat-mul n y)))
  :hints (("Goal" :induct (field-nat-mul n x)
           :in-theory (enable field-nat-mul field-add-associative
                              field-add-commutative))))

(defthm field-neg-of-add
  (equal (field-neg (field-add x y))
         (field-add (field-neg x) (field-neg y)))
  :hints (("Goal"
           :use ((:instance field-additive-inverse-unique
                            (x (field-add x y))
                            (y (field-add (field-neg x) (field-neg y))))
                 (:instance field-add-swap-first-two
                            (x y) (y (field-neg x))
                            (z (field-neg y))))
           :in-theory (enable field-add-associative))))

(defthm field-nat-mul-of-neg
  (equal (field-nat-mul n (field-neg x))
         (field-neg (field-nat-mul n x)))
  :hints (("Goal" :induct (field-nat-mul n x)
           :in-theory (enable field-nat-mul field-neg-of-add))))

(defthm field-nat-mul-of-mul-right
  (equal (field-nat-mul n (field-mul x y))
         (field-mul x (field-nat-mul n y)))
  :hints (("Goal" :induct (field-nat-mul n y)
           :in-theory (enable field-nat-mul
                              field-mul-left-distributive))))

(defthm field-nat-mul-of-mul-left
  (equal (field-nat-mul n (field-mul x y))
         (field-mul (field-nat-mul n x) y))
  :hints (("Goal" :use (field-nat-mul-of-mul-right
                          (:instance field-mul-commutative (x x) (y y))
                          (:instance field-mul-commutative
                           (x y) (y (field-nat-mul n x)))))))

(verify-guards field-nat-mul)
