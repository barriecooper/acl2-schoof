(in-package "GPOLY")

(include-book "division-polynomial-base")
(include-book "../curve/f11-golden")

(defun f11-natural-coefficient (n)
  (declare (xargs :measure (nfix n)))
  (if (zp (nfix n))
      (gfield::f11-zero)
    (gfield::f11-add (gfield::f11-one)
                     (f11-natural-coefficient (1- (nfix n))))))

(defun f11-division-polynomial-base (n a b)
  (let* ((n (nfix n))
         (a (gfield::f11-fix a))
         (b (gfield::f11-fix b))
         (a2 (gfield::f11-mul a a))
         (a3 (gfield::f11-mul a2 a))
         (b2 (gfield::f11-mul b b))
         (ab (gfield::f11-mul a b)))
    (cond ((equal n 0) nil)
          ((or (equal n 1) (equal n 2)) (list (gfield::f11-one)))
          ((equal n 3)
           (f11-normalize
            (list (gfield::f11-neg a2)
                  (gfield::f11-mul (f11-natural-coefficient 12) b)
                  (gfield::f11-mul (f11-natural-coefficient 6) a)
                  (gfield::f11-zero) (f11-natural-coefficient 3))))
          ((equal n 4)
           (f11-normalize
            (list
             (gfield::f11-neg
              (gfield::f11-add
               (gfield::f11-mul (f11-natural-coefficient 2) a3)
               (gfield::f11-mul (f11-natural-coefficient 16) b2)))
             (gfield::f11-neg
              (gfield::f11-mul (f11-natural-coefficient 8) ab))
             (gfield::f11-neg
              (gfield::f11-mul (f11-natural-coefficient 10) a2))
             (gfield::f11-mul (f11-natural-coefficient 40) b)
             (gfield::f11-mul (f11-natural-coefficient 10) a)
             (gfield::f11-zero) (f11-natural-coefficient 2))))
          (t nil))))

; The public closure and correspondence results are usable without opening the
; polynomial implementation or the finite-field theory.
(defthm division-polynomial-base-minimal-theory-client
  (and (finite-field-canonical-polynomial-p
        (finite-field-division-polynomial-base n a b))
       (finite-field-polynomial-p
        (finite-field-division-polynomial-base n a b))
       (equal (finite-field-division-polynomial-base n a b)
              (finite-field-division-polynomial-base-spec n a b)))
  :rule-classes nil
  :hints (("Goal"
           :use (finite-field-canonical-polynomial-p-of-division-polynomial-base
                 finite-field-polynomial-p-of-division-polynomial-base
                 finite-field-division-polynomial-base-correct)
           :in-theory (theory 'minimal-theory))))

; E: y^2 = x^3 + x + 6 over F11 is the repository's nonsingular golden curve.
(assert-event (equal (f11-division-polynomial-base 0 1 6) nil))
(assert-event (equal (f11-division-polynomial-base 1 1 6) '(1)))
(assert-event (equal (f11-division-polynomial-base 2 1 6) '(1)))
(assert-event (equal (f11-division-polynomial-base 3 1 6) '(10 6 6 0 3)))
(assert-event (equal (f11-division-polynomial-base 4 1 6) '(5 7 1 9 10 0 2)))
(assert-event (equal (f11-division-polynomial-base 4 12 17)
                     (f11-division-polynomial-base 4 1 6)))
(assert-event (equal (f11-division-polynomial-base 'malformed 1 6) nil))
(assert-event (equal (f11-division-polynomial-base 9 1 6) nil))
(assert-event (f11-golden-nonsingular-check))

(verify-guards f11-natural-coefficient)
(verify-guards f11-division-polynomial-base)
