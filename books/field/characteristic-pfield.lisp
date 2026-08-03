(in-package "GFIELD")

(include-book "characteristic")
(include-book "pfield-adapter")

; Transparent closed-form natural scaling for the PFIELD adapter.  Its NFIX
; and field-fixing semantics match the generic natural-scalar boundary.
(defun pfield-nat-mul (n x)
  (pfield-fix (* (nfix n) (pfield-fix x))))

(defthm pfield-nat-mul-of-one
  (equal (pfield-nat-mul n (pfield-one))
         (pfield-fix (nfix n)))
  :hints (("Goal" :in-theory (enable pfield-nat-mul pfield-one))))

(defthm pfield-modulus-annihilates-one
  (equal (pfield-nat-mul (pfield-modulus) (pfield-one))
         (pfield-zero))
  :hints (("Goal" :in-theory (enable pfield-fix pfield-zero
                                      pfield::fep-fix mod))))

(defthm pfield-positive-below-modulus-does-not-annihilate-one
  (implies (and (posp n)
                (< n (pfield-modulus)))
           (not (equal (pfield-nat-mul n (pfield-one))
                       (pfield-zero))))
  :hints (("Goal" :in-theory (enable pfield-fix pfield-zero
                                      pfield::fep-fix))))

(defun-sk pfield-characteristic-p (p)
  (forall n
    (and (posp p)
         (equal (pfield-nat-mul p (pfield-one))
                (pfield-zero))
         (implies (and (posp n)
                       (< n p))
                  (not (equal (pfield-nat-mul n (pfield-one))
                              (pfield-zero)))))))

(defthm pfield-modulus-is-field-characteristic
  (pfield-characteristic-p (pfield-modulus))
  :hints (("Goal"
           :use (pfield-modulus-annihilates-one
                 (:instance pfield-positive-below-modulus-does-not-annihilate-one
                            (n (pfield-characteristic-p-witness
                                (pfield-modulus)))))
           :in-theory (enable pfield-characteristic-p))))

(verify-guards pfield-nat-mul)
