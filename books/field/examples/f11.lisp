(in-package "GFIELD")

(include-book "../pfield-adapter")

; The deliberately small named F_11 runtime used by the golden curve fixture.
; All public arithmetic fixes arbitrary ACL2 inputs before calling PFIELD.
(defun f11-element-p (x) (pfield::fep x 11))
(defun f11-fix (x) (pfield::fep-fix x 11))
(defun f11-zero () 0)
(defun f11-one () 1)
(defun f11-add (x y) (pfield::add (f11-fix x) (f11-fix y) 11))
(defun f11-mul (x y) (pfield::mul (f11-fix x) (f11-fix y) 11))
(defun f11-neg (x) (pfield::neg (f11-fix x) 11))

; These are specializations of the PFIELD adapter, not new modular proofs.
(defthm f11-element-p-of-f11-fix
  (f11-element-p (f11-fix x)))
(defthm f11-fix-when-f11-element-p
  (implies (f11-element-p x) (equal (f11-fix x) x)))
(defthm f11-element-p-of-f11-zero (f11-element-p (f11-zero)))
(defthm f11-element-p-of-f11-one (f11-element-p (f11-one)))
(defthm f11-element-p-of-f11-add (f11-element-p (f11-add x y)))
(defthm f11-element-p-of-f11-mul (f11-element-p (f11-mul x y)))
(defthm f11-element-p-of-f11-neg (f11-element-p (f11-neg x)))

(defthm f11-add-zero-left
  (equal (f11-add (f11-zero) x) (f11-fix x)))
(defthm f11-mul-one-left
  (equal (f11-mul (f11-one) x) (f11-fix x)))
(defthm f11-add-associative
  (equal (f11-add (f11-add x y) z) (f11-add x (f11-add y z))))
(defthm f11-mul-associative
  (equal (f11-mul (f11-mul x y) z) (f11-mul x (f11-mul y z))))
(defthm f11-mul-left-distributive
  (equal (f11-mul x (f11-add y z))
         (f11-add (f11-mul x y) (f11-mul x z))))

; The reusable semantic fact is transported through modulus specialization.
(defthm f11-double-negation-from-pfield
  (equal (f11-neg (f11-neg x)) (f11-fix x))
  :hints (("Goal" :by (:functional-instance
                        pfield-double-negation-from-generic-kernel
                        (pfield-modulus (lambda () 11))
                        (pfield-element-p f11-element-p)
                        (pfield-fix f11-fix)
                        (pfield-zero f11-zero)
                        (pfield-one f11-one)
                        (pfield-add f11-add)
                        (pfield-mul f11-mul)
                        (pfield-neg f11-neg))
           :in-theory (enable dm::primep))))

(verify-guards f11-element-p)
(verify-guards f11-fix)
(verify-guards f11-zero)
(verify-guards f11-one)
(verify-guards f11-add)
(verify-guards f11-mul)
(verify-guards f11-neg)

