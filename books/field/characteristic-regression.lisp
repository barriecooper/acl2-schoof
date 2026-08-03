(in-package "GFIELD")

(include-book "characteristic-pfield")
(include-book "examples/f11")

(defun f7-nat-mul (n x)
  (f7-fix (* (nfix n) (f7-fix x))))

(defthm f7-characteristic-annihilates-one
  (equal (f7-nat-mul 7 (f7-one)) (f7-zero))
  :hints (("Goal"
           :by (:functional-instance
                pfield-modulus-annihilates-one
                (pfield-modulus (lambda () 7))
                (pfield-fix f7-fix) (pfield-zero f7-zero)
                (pfield-one f7-one) (pfield-nat-mul f7-nat-mul))
           :in-theory (enable dm::primep))))

(defthm f7-positive-below-seven-does-not-annihilate-one
  (implies (and (posp n) (< n 7))
           (not (equal (f7-nat-mul n (f7-one)) (f7-zero))))
  :hints (("Goal"
           :by (:functional-instance
                pfield-positive-below-modulus-does-not-annihilate-one
                (pfield-modulus (lambda () 7))
                (pfield-fix f7-fix) (pfield-zero f7-zero)
                (pfield-one f7-one) (pfield-nat-mul f7-nat-mul))
           :in-theory (enable dm::primep))))

(defthm f7-has-characteristic-seven
  (and (posp 7)
       (equal (f7-nat-mul 7 (f7-one)) (f7-zero))
       (implies (and (posp n) (< n 7))
                (not (equal (f7-nat-mul n (f7-one)) (f7-zero)))))
  :rule-classes nil
  :hints (("Goal" :use (f7-characteristic-annihilates-one
                          f7-positive-below-seven-does-not-annihilate-one)
           :in-theory (union-theories (theory 'minimal-theory) '(posp)))))

(defun f11-nat-mul (n x)
  (f11-fix (* (nfix n) (f11-fix x))))

(defthm f11-characteristic-annihilates-one
  (equal (f11-nat-mul 11 (f11-one)) (f11-zero))
  :hints (("Goal"
           :by (:functional-instance
                pfield-modulus-annihilates-one
                (pfield-modulus (lambda () 11))
                (pfield-fix f11-fix) (pfield-zero f11-zero)
                (pfield-one f11-one) (pfield-nat-mul f11-nat-mul))
           :in-theory (enable dm::primep))))

(defthm f11-positive-below-eleven-does-not-annihilate-one
  (implies (and (posp n) (< n 11))
           (not (equal (f11-nat-mul n (f11-one)) (f11-zero))))
  :hints (("Goal"
           :by (:functional-instance
                pfield-positive-below-modulus-does-not-annihilate-one
                (pfield-modulus (lambda () 11))
                (pfield-fix f11-fix) (pfield-zero f11-zero)
                (pfield-one f11-one) (pfield-nat-mul f11-nat-mul))
           :in-theory (enable dm::primep))))

(defthm f11-has-characteristic-eleven
  (and (posp 11)
       (equal (f11-nat-mul 11 (f11-one)) (f11-zero))
       (implies (and (posp n) (< n 11))
                (not (equal (f11-nat-mul n (f11-one)) (f11-zero)))))
  :rule-classes nil
  :hints (("Goal" :use (f11-characteristic-annihilates-one
                          f11-positive-below-eleven-does-not-annihilate-one)
           :in-theory (union-theories (theory 'minimal-theory) '(posp)))))

; Opaque-interface clients for downstream characteristic reasoning.
(defthm pfield-characteristic-annihilation-minimal-theory-client
  (implies (pfield-field-characteristic-p p)
           (equal (pfield-nat-mul p x) (pfield-zero)))
  :rule-classes nil
  :hints (("Goal" :use pfield-nat-mul-of-characteristic
           :in-theory (theory 'minimal-theory))))

(defthm f7-characteristic-minimal-theory-client
  (equal (f7-nat-mul 7 (f7-one)) (f7-zero))
  :rule-classes nil
  :hints (("Goal" :use f7-characteristic-annihilates-one
           :in-theory (theory 'minimal-theory))))

(assert-event
 (and (equal (f7-nat-mul 7 (f7-one)) (f7-zero))
      (not (equal (f7-nat-mul 1 (f7-one)) (f7-zero)))
      (not (equal (f7-nat-mul 6 (f7-one)) (f7-zero)))
      (equal (f11-nat-mul 11 (f11-one)) (f11-zero))
      (not (equal (f11-nat-mul 1 (f11-one)) (f11-zero)))
      (not (equal (f11-nat-mul 10 (f11-one)) (f11-zero)))))

(verify-guards f7-nat-mul)
(verify-guards f11-nat-mul)
