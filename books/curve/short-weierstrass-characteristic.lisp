(in-package "GFIELD")

(include-book "../field/kernel")

; The short equation y^2=x^3+a*x+b and the existing tangent formulas are the
; initial characteristic-greater-than-three curve model.  Keep GFIELD itself
; unrestricted: generic field and polynomial clients include characteristic
; two.  Curve theorems which need this scope use this single explicit premise.
(defun short-weierstrass-characteristic-p ()
  (let* ((two (field-add (field-one) (field-one)))
         (three (field-add two (field-one))))
    (and (not (equal two (field-zero)))
         (not (equal three (field-zero))))))

(defthm short-weierstrass-characteristic-implies-two-nonzero
  (implies
   (short-weierstrass-characteristic-p)
   (not (equal (field-add (field-one) (field-one))
               (field-zero)))))

(defthm short-weierstrass-characteristic-implies-three-nonzero
  (implies
   (short-weierstrass-characteristic-p)
   (not
    (equal
     (field-add (field-add (field-one) (field-one)) (field-one))
     (field-zero)))))

(local
 (defthm field-two-times-local
   (equal
    (field-mul (field-add (field-one) (field-one)) x)
    (field-add (field-fix x) (field-fix x)))
   :hints
   (("Goal"
     :use ((:instance field-mul-right-distributive
                      (x (field-one)) (y (field-one)) (z x))
           (:instance field-mul-one-left (x x)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm self-inverse-gives-double-zero-local
   (implies
    (and (field-element-p x)
         (equal x (field-neg x)))
    (equal (field-add x x) (field-zero)))
   :hints
   (("Goal"
     :use ((:instance field-add-inverse-right (x x)))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-fix-when-field-element-p))))))

; This is the stable curve-level consequence needed to exclude the
; characteristic-two self-inverse degeneration.  It performs no division.
(defthm short-weierstrass-self-inverse-field-element-is-zero
  (implies
   (and (short-weierstrass-characteristic-p)
        (field-element-p x)
        (equal x (field-neg x)))
   (equal x (field-zero)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (self-inverse-gives-double-zero-local
     (:instance field-mul-left-cancel-forward
                (x (field-add (field-one) (field-one)))
                (y x) (z (field-zero))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(short-weierstrass-characteristic-p field-two-times-local
       field-mul-zero-right field-fix-of-add
       field-fix-when-field-element-p)))))

(verify-guards short-weierstrass-characteristic-p)
