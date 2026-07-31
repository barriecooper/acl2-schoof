(in-package "GFIELD")

(include-book "short-weierstrass-characteristic")
(include-book "../field/examples/f11")
(include-book "../field/examples/f2")
(include-book "../polynomial/generic/f7x2-arithmetic")

; Concrete clients state the same boundary directly in their own operations.
; These executions are evidence that the intended prime-field clients satisfy
; it; the generic theorem above remains the logical curve interface.
(defun f7-short-weierstrass-characteristic-p ()
  (and (not (equal (f7-add (f7-one) (f7-one)) (f7-zero)))
       (not (equal (f7-add (f7-add (f7-one) (f7-one)) (f7-one))
                   (f7-zero)))))

(defun f2-short-weierstrass-characteristic-p ()
  (and (not (equal (f2-add (f2-one) (f2-one)) (f2-zero)))
       (not (equal (f2-add (f2-add (f2-one) (f2-one)) (f2-one))
                   (f2-zero)))))

(defun f11-short-weierstrass-characteristic-p ()
  (and (not (equal (f11-add (f11-one) (f11-one)) (f11-zero)))
       (not (equal (f11-add (f11-add (f11-one) (f11-one)) (f11-one))
                   (f11-zero)))))

(defun f7x2-short-weierstrass-characteristic-p ()
  (and
   (not
    (equal (gpoly::f7x2-add (gpoly::f7x2-one) (gpoly::f7x2-one))
           (gpoly::f7x2-zero)))
   (not
    (equal
     (gpoly::f7x2-add
      (gpoly::f7x2-add (gpoly::f7x2-one) (gpoly::f7x2-one))
      (gpoly::f7x2-one))
     (gpoly::f7x2-zero)))))

(defthm f7-satisfies-short-weierstrass-characteristic
  (f7-short-weierstrass-characteristic-p)
  :rule-classes nil
  :hints (("Goal" :in-theory
           (enable f7-short-weierstrass-characteristic-p
                   f7-add f7-one f7-zero f7-fix
                   pfield::add pfield::fep-fix))))

(defthm f11-satisfies-short-weierstrass-characteristic
  (f11-short-weierstrass-characteristic-p)
  :rule-classes nil
  :hints (("Goal" :in-theory
           (enable f11-short-weierstrass-characteristic-p
                   f11-add f11-one f11-zero f11-fix
                   pfield::add pfield::fep-fix))))

(defthm f7x2-satisfies-short-weierstrass-characteristic
  (f7x2-short-weierstrass-characteristic-p)
  :rule-classes nil
  :hints (("Goal" :in-theory
           (enable f7x2-short-weierstrass-characteristic-p
                   gpoly::f7x2-add gpoly::f7x2-one gpoly::f7x2-zero))))

(assert-event (f7-short-weierstrass-characteristic-p))
(assert-event (not (f2-short-weierstrass-characteristic-p)))
(assert-event (f11-short-weierstrass-characteristic-p))
(assert-event (f7x2-short-weierstrass-characteristic-p))
