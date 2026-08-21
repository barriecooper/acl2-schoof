(in-package "GPOLY")

(include-book "runtime-p-algebra")
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

; PFIELD::INV is the existing, exponentiation-based modular inverse.  The
; explicit zero branch discharges its executable guard while preserving its
; established total convention.
(defun runtime-p-inv (x p)
  (declare (xargs :guard t))
  (let* ((modulus (runtime-p-effective-modulus p))
         (x (runtime-p-coefficient-fix x p)))
    (if (equal x 0)
        0
      (pfield::inv x modulus))))

(defthm runtime-p-inv-logical-definition
  (equal (runtime-p-inv x p)
         (pfield::inv (runtime-p-coefficient-fix x p)
                      (runtime-p-effective-modulus p)))
  :hints (("Goal" :in-theory (enable runtime-p-inv))))

(verify-guards runtime-p-inv)

(defthm runtime-p-coefficient-p-of-inv
  (runtime-p-coefficient-p (runtime-p-inv x p) p)
  :hints (("Goal" :in-theory (enable runtime-p-coefficient-p
                                     runtime-p-inv-logical-definition))))

(defthm runtime-p-inv-of-fix
  (equal (runtime-p-inv (runtime-p-coefficient-fix x p) p)
         (runtime-p-inv x p))
  :hints (("Goal" :in-theory (enable runtime-p-inv-logical-definition))))

(defthm runtime-p-inv-effective-modulus-congruence
  (implies (equal (runtime-p-effective-modulus p)
                  (runtime-p-effective-modulus q))
           (equal (runtime-p-inv x p) (runtime-p-inv x q)))
  :hints (("Goal" :in-theory (enable runtime-p-inv-logical-definition
                                     runtime-p-coefficient-fix))))

(defthm runtime-p-inv-of-zero
  (equal (runtime-p-inv (runtime-p-zero p) p) (runtime-p-zero p))
  :hints (("Goal" :in-theory (enable runtime-p-inv))))

(defthm runtime-p-inv-of-one
  (equal (runtime-p-inv (runtime-p-one p) p) (runtime-p-one p))
  :hints (("Goal" :in-theory (enable runtime-p-inv
                                     runtime-p-one
                                     runtime-p-coefficient-fix
                                     pfield::inv
                                     pfield::minus1))))

(defthm runtime-p-inv-malformed-modulus
  (implies (not (and (integerp p) (<= 2 p)))
           (equal (runtime-p-inv x p) (runtime-p-inv x 2)))
  :hints (("Goal" :use ((:instance runtime-p-inv-effective-modulus-congruence
                          (q 2)))
           :in-theory (enable runtime-p-effective-modulus))))

(defthm runtime-p-mul-inv-right
  (implies (and (dm::primep (runtime-p-effective-modulus p))
                (not (equal (runtime-p-coefficient-fix x p)
                            (runtime-p-zero p))))
           (equal (runtime-p-mul x (runtime-p-inv x p) p)
                  (runtime-p-one p)))
  :hints (("Goal" :use ((:instance pfield::mul-of-inv-arg2
                          (x (runtime-p-coefficient-fix x p))
                          (p (runtime-p-effective-modulus p))))
           :in-theory (enable runtime-p-mul runtime-p-inv-logical-definition))))

(defthm runtime-p-mul-inv-left
  (implies (and (dm::primep (runtime-p-effective-modulus p))
                (not (equal (runtime-p-coefficient-fix x p)
                            (runtime-p-zero p))))
           (equal (runtime-p-mul (runtime-p-inv x p) x p)
                  (runtime-p-one p)))
  :hints (("Goal" :use ((:instance pfield::mul-of-inv-arg1
                          (x (runtime-p-coefficient-fix x p))
                          (p (runtime-p-effective-modulus p))))
           :in-theory (enable runtime-p-mul runtime-p-inv-logical-definition))))

(defthm runtime-p-inv-involution
  (implies (dm::primep (runtime-p-effective-modulus p))
           (equal (runtime-p-inv (runtime-p-inv x p) p)
                  (runtime-p-coefficient-fix x p)))
  :hints (("Goal" :use ((:instance pfield::inv-of-inv
                          (a (runtime-p-coefficient-fix x p))
                          (p (runtime-p-effective-modulus p))))
           :in-theory (enable runtime-p-inv-logical-definition
                              runtime-p-coefficient-p))))

(defthm runtime-p-prime-coefficient-field-inverse-laws
  (implies (dm::primep (runtime-p-effective-modulus p))
           (and (runtime-p-coefficient-p (runtime-p-inv x p) p)
                (equal (runtime-p-inv (runtime-p-zero p) p)
                       (runtime-p-zero p))
                (implies (not (equal (runtime-p-coefficient-fix x p)
                                     (runtime-p-zero p)))
                         (and (equal (runtime-p-mul (runtime-p-inv x p) x p)
                                     (runtime-p-one p))
                              (equal (runtime-p-mul x (runtime-p-inv x p) p)
                                     (runtime-p-one p))))))
  :rule-classes nil
  :hints (("Goal" :use (runtime-p-coefficient-p-of-inv
                          runtime-p-inv-of-zero
                          runtime-p-mul-inv-left
                          runtime-p-mul-inv-right)
           :in-theory (theory 'minimal-theory))))

; Exact fixed-prime adapter correspondence.
(defthm runtime-p-inv-at-pfield-modulus
  (equal (runtime-p-inv x (gfield::pfield-modulus))
         (gfield::pfield-inv x))
  :hints (("Goal" :in-theory (enable runtime-p-inv
                                     runtime-p-effective-modulus
                                     runtime-p-coefficient-fix
                                     gfield::pfield-inv
                                     gfield::pfield-fix))))
