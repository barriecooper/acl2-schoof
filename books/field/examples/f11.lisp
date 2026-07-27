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
(defun f11-inv (x)
  (let ((x (f11-fix x)))
    (if (equal x (f11-zero))
        (f11-zero)
      (pfield::inv x 11))))
(defun f11-div (x y) (f11-mul x (f11-inv y)))

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
(defthm f11-element-p-of-f11-inv (f11-element-p (f11-inv x)))
(defthm f11-element-p-of-f11-div (f11-element-p (f11-div x y)))

(defthm f11-fix-idempotent
  (equal (f11-fix (f11-fix x)) (f11-fix x))
  :hints (("Goal" :use ((:instance f11-fix-when-f11-element-p
                          (x (f11-fix x)))))))

(defthm f11-inv-of-fix
  (equal (f11-inv (f11-fix x)) (f11-inv x))
  :hints (("Goal" :in-theory (e/d (f11-inv f11-fix-idempotent)
                                    (f11-fix)))))

(defthm f11-fix-of-inv
  (equal (f11-fix (f11-inv x)) (f11-inv x))
  :hints (("Goal" :use ((:instance f11-fix-when-f11-element-p
                          (x (f11-inv x)))))))

(defthm f11-div-of-fixes
  (equal (f11-div (f11-fix x) (f11-fix y))
         (f11-div x y))
  :hints (("Goal" :in-theory (e/d (f11-div f11-mul f11-inv
                                             f11-fix-idempotent)
                                    (f11-fix)))))

(defthm f11-fix-of-div
  (equal (f11-fix (f11-div x y)) (f11-div x y))
  :hints (("Goal" :use ((:instance f11-fix-when-f11-element-p
                          (x (f11-div x y)))))))

(defthm f11-inv-of-zero
  (equal (f11-inv (f11-zero)) (f11-zero))
  :hints (("Goal" :in-theory (enable f11-inv f11-fix f11-zero))))

(defthm f11-mul-inverse-left
  (implies (not (equal (f11-fix x) (f11-zero)))
           (equal (f11-mul (f11-inv x) x) (f11-one)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance pfield::mul-of-inv-arg1
                            (x (f11-fix x)) (p 11)))
           :do-not '(preprocess)
           :in-theory (e/d (f11-fix f11-mul f11-inv f11-zero f11-one
                                    dm::primep)
                            (pfield::mul-of-inv-arg1)))))

; Exact executable checks, including every canonical inverse and the total
; fixing boundary used by future concrete clients.
(assert-event (equal (list (f11-inv 0) (f11-inv 1) (f11-inv 2)
                           (f11-inv 3) (f11-inv 4) (f11-inv 5)
                           (f11-inv 6) (f11-inv 7) (f11-inv 8)
                           (f11-inv 9) (f11-inv 10))
                     '(0 1 6 4 3 9 2 8 7 5 10)))
(assert-event
 (and (equal (f11-inv 13) 6)
      (equal (f11-inv 22) 0)
      (equal (f11-inv -1) 10)
      (equal (f11-inv 'malformed) 0)
      (equal (f11-inv '(1 . 2)) 0)))
(assert-event
 (and (equal (f11-div 1 1) 1)
      (equal (f11-div 1 2) 6)
      (equal (f11-div 2 2) 1)
      (equal (f11-div 5 3) 9)
      (equal (f11-div 0 3) 0)
      (equal (f11-div 5 0) 0)
      (equal (f11-div 1 13) 6)
      (equal (f11-div 16 3) 9)
      (equal (f11-div 5 22) 0)))

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
                        (pfield-neg f11-neg)
                        (pfield-inv f11-inv))
           :in-theory (enable dm::primep))))

(verify-guards f11-element-p)
(verify-guards f11-fix)
(verify-guards f11-zero)
(verify-guards f11-one)
(verify-guards f11-add)
(verify-guards f11-mul)
(verify-guards f11-neg)
(verify-guards f11-inv)
(verify-guards f11-div)
