(in-package "GFIELD")

(include-book "short-weierstrass-characteristic")

; The parameters are deliberately not required to be canonical.  Every use is
; fixed, which gives arbitrary ACL2 witnesses the same total semantics as
; coordinates and keeps the constrained boundary to two nullary symbols and
; the standard certificate.
(encapsulate
 (((short-weierstrass-a) => *)
  ((short-weierstrass-b) => *))
 (local (defun short-weierstrass-a ()
          (let* ((two (field-add (field-one) (field-one)))
                 (four (field-mul two two)))
            (if (equal four (field-zero))
                (field-zero)
              (field-one)))))
 (local (defun short-weierstrass-b ()
          (let* ((two (field-add (field-one) (field-one)))
                 (four (field-mul two two)))
            (if (equal four (field-zero))
                (field-one)
              (field-zero)))))
 (local (defthm field-neg-one-nonzero-for-curve-witness
          (not (equal (field-neg (field-one)) (field-zero)))
          :hints (("Goal"
                   :use ((:instance field-add-fixed-congruence
                          (x1 (field-neg (field-one)))
                          (x2 (field-zero))
                          (y1 (field-one))
                          (y2 (field-one))))))))

 (defun short-weierstrass-rhs (x)
   (field-add
    (field-mul (field-mul (field-fix x) (field-fix x)) (field-fix x))
    (field-add (field-mul (field-fix (short-weierstrass-a))
                          (field-fix x))
               (field-fix (short-weierstrass-b)))))

 (defun short-weierstrass-equation-p (x y)
   (equal (field-mul (field-fix y) (field-fix y))
          (short-weierstrass-rhs x)))

 ; 4 = (1+1)^2 and 27 = (1+1+1)^3 in the existing field arithmetic.
 (defun short-weierstrass-discriminant-expression ()
   (let* ((two (field-add (field-one) (field-one)))
          (three (field-add two (field-one)))
          (a (field-fix (short-weierstrass-a)))
          (b (field-fix (short-weierstrass-b))))
     (field-add
      (field-mul (field-mul two two)
                 (field-mul (field-mul a a) a))
      (field-mul (field-mul (field-mul three three) three)
                 (field-mul b b)))))

 (defthm short-weierstrass-discriminant-expression-nonzero
   (not (equal (short-weierstrass-discriminant-expression)
               (field-zero)))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :cases ((equal (field-mul
                            (field-add (field-one) (field-one))
                            (field-add (field-one) (field-one)))
                           (field-zero)))
            :in-theory
            (enable short-weierstrass-discriminant-expression
                    short-weierstrass-a short-weierstrass-b)
            :use field-neg-one-nonzero-for-curve-witness)))
 )

(defthm field-element-p-of-short-weierstrass-rhs
  (field-element-p (short-weierstrass-rhs x)))

(verify-guards short-weierstrass-rhs)
(verify-guards short-weierstrass-equation-p)
(verify-guards short-weierstrass-discriminant-expression)
