(in-package "GFIELD")

(include-book "characteristic-pfield")
(include-book "examples/f11")

(defun f7-nat-mul (n x)
  (f7-fix (* (nfix n) (f7-fix x))))

(defun-sk f7-characteristic-p (p)
  (forall n
    (and (posp p)
         (equal (f7-nat-mul p (f7-one)) (f7-zero))
         (implies (and (posp n) (< n p))
                  (not (equal (f7-nat-mul n (f7-one))
                              (f7-zero)))))))

(defthm f7-characteristic-is-seven
  (f7-characteristic-p 7)
  :hints (("Goal"
           :in-theory (enable f7-characteristic-p f7-nat-mul
                              f7-fix f7-one f7-zero
                              pfield::fep-fix mod))))

(defun f11-nat-mul (n x)
  (f11-fix (* (nfix n) (f11-fix x))))

(defun-sk f11-characteristic-p (p)
  (forall n
    (and (posp p)
         (equal (f11-nat-mul p (f11-one)) (f11-zero))
         (implies (and (posp n) (< n p))
                  (not (equal (f11-nat-mul n (f11-one))
                              (f11-zero)))))))

(defthm f11-characteristic-is-eleven
  (f11-characteristic-p 11)
  :hints (("Goal"
           :in-theory (enable f11-characteristic-p f11-nat-mul
                              f11-fix f11-one f11-zero
                              pfield::fep-fix mod))))

(assert-event
 (and (equal (f7-nat-mul 7 (f7-one)) (f7-zero))
      (not (equal (f7-nat-mul 1 (f7-one)) (f7-zero)))
      (not (equal (f7-nat-mul 6 (f7-one)) (f7-zero)))
      (equal (f11-nat-mul 11 (f11-one)) (f11-zero))
      (not (equal (f11-nat-mul 1 (f11-one)) (f11-zero)))
      (not (equal (f11-nat-mul 10 (f11-one)) (f11-zero)))))

(verify-guards f7-nat-mul)
(verify-guards f11-nat-mul)
