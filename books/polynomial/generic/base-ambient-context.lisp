(in-package "GFIELD")

(include-book "add")

; A narrow downstream scalar seam: the base is the existing GFIELD interface.
; The ambient side is only a fixed commutative ring, with no inverse, size,
; injectivity, fixed-subfield, Frobenius, or root-existence assumptions.
(encapsulate
 (((ambient-fix *) => *)
  ((ambient-zero) => *) ((ambient-one) => *)
  ((ambient-add * *) => *) ((ambient-neg *) => *)
  ((ambient-mul * *) => *) ((base-to-ambient *) => *))
 (local (defun ambient-fix (x) (field-fix x)))
 (local (defun ambient-zero () (field-zero)))
 (local (defun ambient-one () (field-one)))
 (local (defun ambient-add (x y) (field-add x y)))
 (local (defun ambient-neg (x) (field-neg x)))
 (local (defun ambient-mul (x y) (field-mul x y)))
 (local (defun base-to-ambient (x) (field-fix x)))

 (defthm ambient-fix-idempotent
   (equal (ambient-fix (ambient-fix x)) (ambient-fix x)))
 (defthm ambient-fix-zero (equal (ambient-fix (ambient-zero)) (ambient-zero)))
 (defthm ambient-fix-one (equal (ambient-fix (ambient-one)) (ambient-one)))
 (defthm ambient-fix-add
   (equal (ambient-fix (ambient-add x y)) (ambient-add x y)))
 (defthm ambient-fix-neg
   (equal (ambient-fix (ambient-neg x)) (ambient-neg x)))
 (defthm ambient-fix-mul
   (equal (ambient-fix (ambient-mul x y)) (ambient-mul x y)))
 (defthm ambient-add-of-fixes
   (equal (ambient-add (ambient-fix x) (ambient-fix y)) (ambient-add x y)))
 (defthm ambient-add-fix-left
   (equal (ambient-add (ambient-fix x) y) (ambient-add x y)))
 (defthm ambient-add-fix-right
   (equal (ambient-add x (ambient-fix y)) (ambient-add x y)))
 (defthm ambient-mul-fix-left
   (equal (ambient-mul (ambient-fix x) y) (ambient-mul x y)))
 (defthm ambient-mul-fix-right
   (equal (ambient-mul x (ambient-fix y)) (ambient-mul x y)))
 (defthm ambient-neg-of-fix
   (equal (ambient-neg (ambient-fix x)) (ambient-neg x)))
 (defthm ambient-mul-of-fixes
   (equal (ambient-mul (ambient-fix x) (ambient-fix y)) (ambient-mul x y)))
 (defthm ambient-add-associative
   (equal (ambient-add (ambient-add x y) z)
          (ambient-add x (ambient-add y z))))
 (defthm ambient-add-commutative
   (equal (ambient-add x y) (ambient-add y x)))
 (defthm ambient-add-zero-left
   (equal (ambient-add (ambient-zero) x) (ambient-fix x)))
 (defthm ambient-add-inverse-left
   (equal (ambient-add (ambient-neg x) x) (ambient-zero)))
 (defthm ambient-mul-associative
   (equal (ambient-mul (ambient-mul x y) z)
          (ambient-mul x (ambient-mul y z))))
 (defthm ambient-mul-commutative
   (equal (ambient-mul x y) (ambient-mul y x)))
 (defthm ambient-mul-one-left
   (equal (ambient-mul (ambient-one) x) (ambient-fix x)))
 (defthm ambient-mul-left-distributive
   (equal (ambient-mul x (ambient-add y z))
          (ambient-add (ambient-mul x y) (ambient-mul x z))))
 (defthm base-to-ambient-of-field-fix
   (equal (base-to-ambient (field-fix x)) (base-to-ambient x)))
 (defthm base-to-ambient-fixed-congruence
   (implies (equal (field-fix x) (field-fix y))
            (equal (base-to-ambient x) (base-to-ambient y))))
 (defthm ambient-fix-of-base-to-ambient
   (equal (ambient-fix (base-to-ambient x)) (base-to-ambient x)))
 (defthm base-to-ambient-zero
   (equal (base-to-ambient (field-zero)) (ambient-zero)))
 (defthm base-to-ambient-one
   (equal (base-to-ambient (field-one)) (ambient-one)))
 (defthm base-to-ambient-add
   (equal (base-to-ambient (field-add x y))
          (ambient-add (base-to-ambient x) (base-to-ambient y))))
 (defthm base-to-ambient-neg
   (equal (base-to-ambient (field-neg x))
          (ambient-neg (base-to-ambient x))))
 (defthm base-to-ambient-mul
   (equal (base-to-ambient (field-mul x y))
          (ambient-mul (base-to-ambient x) (base-to-ambient y))))
 (defthm ambient-add-interchange
   (equal (ambient-add x (ambient-add y z))
          (ambient-add y (ambient-add x z))))
 (defthm ambient-add-zero-right
   (equal (ambient-add x (ambient-zero)) (ambient-fix x)))
 (defthm ambient-mul-interchange
   (equal (ambient-mul x (ambient-mul y z))
          (ambient-mul y (ambient-mul x z))))
 (defthm ambient-mul-one-right
   (equal (ambient-mul x (ambient-one)) (ambient-fix x)))
 (defthm ambient-mul-right-distributive
   (equal (ambient-mul (ambient-add x y) z)
          (ambient-add (ambient-mul x z) (ambient-mul y z))))
 (defthm ambient-mul-zero-left
   (equal (ambient-mul (ambient-zero) x) (ambient-zero)))
 (defthm ambient-mul-zero-right
   (equal (ambient-mul x (ambient-zero)) (ambient-zero)))
 (defthm ambient-neg-zero
   (equal (ambient-neg (ambient-zero)) (ambient-zero)))
 (defthm ambient-neg-of-neg
   (equal (ambient-neg (ambient-neg x)) (ambient-fix x)))
 (defthm ambient-neg-of-add
   (equal (ambient-neg (ambient-add x y))
          (ambient-add (ambient-neg x) (ambient-neg y)))
   :hints (("Goal" :use gpoly::field-neg-of-add)))
 (defthm ambient-mul-of-neg-right
   (equal (ambient-mul x (ambient-neg y))
          (ambient-neg (ambient-mul x y)))
   :hints (("Goal" :use gpoly::field-mul-of-neg-right))))

(defun ambient-sub (x y) (ambient-add x (ambient-neg y)))

(defun ambient-pow (x n)
  (declare (xargs :measure (nfix n)))
  (if (zp (nfix n))
      (ambient-one)
    (ambient-mul (ambient-fix x) (ambient-pow x (1- (nfix n))))))

(defthm ambient-pow-of-nfix
  (equal (ambient-pow x (nfix n)) (ambient-pow x n)))
(defthm ambient-pow-zero
  (equal (ambient-pow x 0) (ambient-one)))
(defthm ambient-pow-successor-total
  (equal (ambient-pow x (+ 1 (nfix n)))
         (ambient-mul x (ambient-pow x n)))
  :hints (("Goal" :in-theory (enable ambient-pow))))
