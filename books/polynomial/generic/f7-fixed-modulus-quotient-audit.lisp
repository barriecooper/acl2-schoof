(in-package "GPOLY")
(include-book "fixed-modulus-quotient-audit")
(include-book "f7-irreducible-modular-inverse")

; Concrete degree-one modulus for the second staged audit checkpoint.
(defun audit-f7-modulus ()
  (f7-monomial (gfield::f7-one) 1))

(local (defthm audit-f7-modulus-canonical
         (f7-canonical-polynomial-p (audit-f7-modulus))
         :hints (("Goal" :in-theory (enable audit-f7-modulus)))))
(local (defthm audit-f7-modulus-degree
         (equal (f7-poly-degree (audit-f7-modulus)) 1)
         :hints (("Goal" :in-theory (enable audit-f7-modulus)))))

(local (defthm audit-f7-canonical-degree-one-poly-irreducible
  (implies (and (f7-canonical-polynomial-p poly)
                (equal (f7-poly-degree poly) 1))
           (f7-poly-irreducible-p poly))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:functional-instance
      canonical-degree-one-poly-irreducible
      (gfield::field-element-p gfield::f7-element-p)
      (gfield::field-fix gfield::f7-fix)
      (gfield::field-zero gfield::f7-zero)
      (gfield::field-one gfield::f7-one)
      (gfield::field-add gfield::f7-add)
      (gfield::field-mul gfield::f7-mul)
      (gfield::field-neg gfield::f7-neg)
      (gfield::field-inv gfield::f7-inv)
      (fix-coefficients f7-fix-coefficients)
      (trim-trailing-zeros f7-trim-trailing-zeros)
      (normalize f7-normalize)
      (coefficient-list-p f7-coefficient-list-p)
      (polynomial-p f7-polynomial-p)
      (canonical-polynomial-p f7-canonical-polynomial-p)
      (raw-add f7-raw-add) (poly-add f7-poly-add)
      (raw-neg f7-raw-neg) (poly-neg f7-poly-neg)
      (poly-sub f7-poly-sub)
      (raw-scale f7-raw-scale) (poly-scale f7-poly-scale)
      (raw-mul f7-raw-mul) (poly-mul f7-poly-mul)
      (zero-prefix f7-zero-prefix) (poly-shift f7-poly-shift)
      (monomial f7-monomial) (poly-degree f7-poly-degree)
      (poly-leading-coefficient f7-poly-leading-coefficient)
      (poly-unit-p f7-poly-unit-p)
      (poly-reducible-p f7-poly-reducible-p)
      (poly-reducible-p-witness f7-poly-reducible-p-witness)
      (poly-irreducible-p f7-poly-irreducible-p)))
    :in-theory (disable f7-poly-irreducible-p audit-f7-modulus))
   ("Subgoal 29" :use (f7-poly-reducible-p-full-witness-constraint-for-instantiation
          (:instance f7-poly-irreducible-p-definition)
          (:instance f7-poly-degree-semantics-from-pfield))
    :in-theory (e/d (f7-normalize) nil))
   ("Subgoal 28" :use f7-poly-reducible-p-full-witness-constraint-for-instantiation)
   ("Subgoal 25.2" :use gfield::f7-mul-inverse-right)
   ("Subgoal 22.4" :use ((:instance f7-mul-fixed-congruence-for-divmod-instantiation
                                    (x1 gfield::x1) (x2 gfield::x2)
                                    (y1 gfield::y1) (y2 gfield::y2))))
   ("Subgoal 21.11" :use ((:instance f7-add-fixed-congruence-for-divmod-instantiation
                                     (x1 gfield::x1) (x2 gfield::x2)
                                     (y1 gfield::y1) (y2 gfield::y2))))
   ("Subgoal 19.2.1'" :in-theory (enable mod))
   ("Subgoal 18.2.1''" :in-theory (enable mod))
   ("Subgoal 18.2.1'" :in-theory (enable mod))
   ("Subgoal 17.2.1''" :in-theory (enable mod))
   ("Subgoal 2.1" :use ((:instance f7-canonical-polynomial-p-implies-last-nonzero (p xs))))))
)

(defthm audit-f7-modulus-irreducible
  (f7-poly-irreducible-p (audit-f7-modulus))
  :rule-classes nil
  :hints (("Goal" :use ((:instance audit-f7-canonical-degree-one-poly-irreducible
                                   (poly (audit-f7-modulus)))
                         audit-f7-modulus-canonical
                         audit-f7-modulus-degree)
            :in-theory (disable audit-f7-modulus
                                f7-poly-irreducible-p))))

(defun audit-f7-carrier (x) (equal (f7-poly-remainder x (audit-f7-modulus)) x))
(defun audit-f7-fix (x) (f7-poly-remainder x (audit-f7-modulus)))
(defun audit-f7-zero () nil)
(defun audit-f7-one () (f7-poly-reduced-one (audit-f7-modulus)))
(defun audit-f7-add (x y) (f7-poly-reduced-add x y (audit-f7-modulus)))
(defun audit-f7-neg (x) (f7-poly-reduced-neg x (audit-f7-modulus)))
(defun audit-f7-sub (x y) (f7-poly-reduced-sub x y (audit-f7-modulus)))
(defun audit-f7-mul (x y) (f7-poly-reduced-mul x y (audit-f7-modulus)))
(defun audit-f7-inv (x)
  (let ((fixed-x (audit-f7-fix x)))
    (if (equal fixed-x (audit-f7-zero))
        (audit-f7-zero)
      (f7-poly-modular-inverse fixed-x (audit-f7-modulus)))))
