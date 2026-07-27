(in-package "GFIELD")

(include-book "kernel")

; This is the reusable no-zero-divisors consequence of the existing inverse
; law.  It is deliberately non-rewriting: clients should request the case
; split rather than making every zero product split automatically.
(defthm field-mul-equal-zero-implies-equal-zero
  (implies (equal (field-mul first second) (field-zero))
           (or (equal (field-fix first) (field-zero))
               (equal (field-fix second) (field-zero))))
  :rule-classes nil
  :hints
  (("Goal"
    :cases ((equal (field-fix first) (field-zero)))
    :use ((:instance field-mul-left-cancel-forward
                     (x first) (y second) (z (field-zero)))))))

(local
 (defthm field-mul-right-neg-for-equal-squares
   (equal (field-mul x (field-neg y))
          (field-neg (field-mul x y)))
   :hints
   (("Goal"
     :use ((:instance field-additive-inverse-unique
                      (x (field-mul x y))
                      (y (field-mul x (field-neg y))))
           (:instance field-mul-left-distributive
                      (x x) (y y) (z (field-neg y))))))))

(local
 (defthm field-difference-of-squares-for-equal-squares
   (equal (field-mul (field-add first (field-neg second))
                     (field-add first second))
          (field-sub (field-mul first first)
                     (field-mul second second)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-add-associative
                      (x (field-mul first second))
                      (y (field-neg (field-mul first second)))
                      (z (field-neg (field-mul second second)))))
     :in-theory (enable field-sub field-mul-right-distributive
                        field-mul-left-distributive)))))

(local
 (defthm field-equal-squares-implies-factor-product-zero
   (implies (equal (field-mul first first)
                   (field-mul second second))
            (equal (field-mul (field-add first (field-neg second))
                              (field-add first second))
                   (field-zero)))
   :hints
   (("Goal"
     :use field-difference-of-squares-for-equal-squares))))

(local
 (defthm field-difference-zero-implies-fixed-equal
   (implies (equal (field-add first (field-neg second)) (field-zero))
            (equal (field-fix first) (field-fix second)))
   :hints
   (("Goal"
     :use ((:instance field-additive-inverse-unique
                      (x (field-neg second)) (y first)))))))

; Arbitrary ACL2 inputs are interpreted through the field operations' existing
; fixing semantics.  The orientation of the second alternative matches the
; affine exceptional-case classifier.
(defthm field-equal-squares-implies-equal-or-neg
  (implies (equal (field-mul first first)
                  (field-mul second second))
           (or (equal (field-fix first) (field-fix second))
               (equal (field-fix second) (field-neg first))))
  :rule-classes nil
  :hints
  (("Goal"
    :use (field-equal-squares-implies-factor-product-zero
          (:instance field-mul-equal-zero-implies-equal-zero
                     (first (field-add first (field-neg second)))
                     (second (field-add first second)))
          field-difference-zero-implies-fixed-equal
          (:instance field-additive-inverse-unique
                     (x first) (y second))))))
