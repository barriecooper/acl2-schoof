(in-package "GFIELD")

(include-book "short-weierstrass")
(include-book "../field/examples/f11")

(defun f11-short-weierstrass-a () 1)
(defun f11-short-weierstrass-b () 6)

(defun f11-short-weierstrass-rhs (x)
  (f11-add
   (f11-mul (f11-mul (f11-fix x) (f11-fix x)) (f11-fix x))
   (f11-add (f11-mul (f11-fix (f11-short-weierstrass-a)) (f11-fix x))
            (f11-fix (f11-short-weierstrass-b)))))

(defun f11-short-weierstrass-equation-p (x y)
  (equal (f11-mul (f11-fix y) (f11-fix y))
         (f11-short-weierstrass-rhs x)))

(defun f11-short-weierstrass-discriminant-expression ()
  (let* ((two (f11-add (f11-one) (f11-one)))
         (three (f11-add two (f11-one)))
         (a (f11-fix (f11-short-weierstrass-a)))
         (b (f11-fix (f11-short-weierstrass-b))))
    (f11-add
     (f11-mul (f11-mul two two) (f11-mul (f11-mul a a) a))
     (f11-mul (f11-mul (f11-mul three three) three)
              (f11-mul b b)))))

(local (defthm f11-short-weierstrass-discriminant-computation
         (not (equal (f11-short-weierstrass-discriminant-expression)
                     (f11-zero)))
         :hints (("Goal" :in-theory
                  (enable f11-short-weierstrass-discriminant-expression
                          f11-short-weierstrass-a f11-short-weierstrass-b
                          f11-one f11-zero f11-add f11-mul f11-fix
                          pfield::add pfield::mul pfield::fep-fix)))))

(defthm f11-short-weierstrass-discriminant-expression-nonzero
  (not (equal (f11-short-weierstrass-discriminant-expression)
              (f11-zero)))
  :rule-classes nil
  :hints (("Goal" :use f11-short-weierstrass-discriminant-computation)))

; Focused total execution checks for the existing golden coefficients.
(assert-event (equal (f11-fix (f11-short-weierstrass-a)) 1))
(assert-event (equal (f11-fix (f11-short-weierstrass-b)) 6))
(assert-event (f11-short-weierstrass-equation-p 2 4))
(assert-event (not (f11-short-weierstrass-equation-p 2 5)))
(assert-event (f11-short-weierstrass-equation-p 13 15))
(assert-event (not (f11-short-weierstrass-equation-p 'bad 'bad)))
(assert-event (not (equal (f11-short-weierstrass-discriminant-expression)
                          (f11-zero))))

(verify-guards f11-short-weierstrass-a)
(verify-guards f11-short-weierstrass-b)
(verify-guards f11-short-weierstrass-rhs)
(verify-guards f11-short-weierstrass-equation-p)
(verify-guards f11-short-weierstrass-discriminant-expression)
