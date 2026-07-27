(in-package "GFIELD")

(include-book "pfield-adapter")

; Additive-only client boundary for the initial short-Weierstrass scope.  The
; operations are constrained jointly with the two exclusions because neither
; exclusion follows from the unconstrained generic field kernel.
(encapsulate
 (((additive-field-fix *) => *)
  ((additive-field-zero) => *)
  ((additive-field-one) => *)
  ((additive-field-add * *) => *))
 (local (defun additive-field-fix (x)
          (if (integerp x) (mod x 7) 0)))
 (local (defun additive-field-zero () 0))
 (local (defun additive-field-one () 1))
 (local (defun additive-field-add (x y)
          (mod (+ (additive-field-fix x) (additive-field-fix y)) 7)))

 ; Total natural repeated addition: arbitrary counts have NFIX semantics, and
 ; every positive copy is taken through the constrained fixer.
 (defun field-nat-sum (x n)
   (declare (xargs :measure (nfix n)))
   (let ((n (nfix n)))
     (if (zp n)
         (additive-field-zero)
       (additive-field-add (additive-field-fix x)
                           (field-nat-sum x (1- n))))))

 (defthm field-nat-sum-two-of-field-one-nonzero
   (not (equal (field-nat-sum (additive-field-one) 2)
               (additive-field-zero)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable field-nat-sum
                                       additive-field-fix
                                       additive-field-zero
                                       additive-field-one
                                       additive-field-add))))

 (defthm field-nat-sum-three-of-field-one-nonzero
   (not (equal (field-nat-sum (additive-field-one) 3)
               (additive-field-zero)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable field-nat-sum
                                       additive-field-fix
                                       additive-field-zero
                                       additive-field-one
                                       additive-field-add)))))
