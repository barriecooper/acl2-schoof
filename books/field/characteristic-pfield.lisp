(in-package "GFIELD")

(include-book "characteristic")
(include-book "pfield-adapter")
(include-book "kestrel/arithmetic-light/mod" :dir :system)
(include-book "tools/def-functional-instance" :dir :system)

(defun pfield-nat-mul (n x)
  (pfield-fix (* (nfix n) (pfield-fix x))))

(defthm pfield-nat-mul-of-nfix
  (equal (pfield-nat-mul (nfix n) x) (pfield-nat-mul n x)))

(defthm pfield-nat-mul-of-fix
  (equal (pfield-nat-mul n (pfield-fix x)) (pfield-nat-mul n x))
  :hints (("Goal" :in-theory (enable pfield-nat-mul))))

(defthm pfield-nat-mul-zero
  (equal (pfield-nat-mul 0 x) (pfield-zero))
  :hints (("Goal" :in-theory (enable pfield-nat-mul pfield-zero
                                      pfield-fix pfield::fep-fix))))

(defthm pfield-nat-mul-when-zp
  (implies (zp (nfix n))
           (equal (pfield-nat-mul n x) (pfield-zero)))
  :hints (("Goal" :use ((:instance pfield-nat-mul-of-nfix)
                          (:instance pfield-nat-mul-zero)))))

(defthm pfield-nat-mul-of-zero
  (equal (pfield-nat-mul n (pfield-zero)) (pfield-zero))
  :hints (("Goal" :in-theory (enable pfield-nat-mul pfield-zero
                                      pfield-fix pfield::fep-fix))))

(defthm pfield-nat-mul-successor-total
  (equal (pfield-nat-mul (+ 1 (nfix n)) x)
         (pfield-add x (pfield-nat-mul n x)))
  :hints (("Goal"
           :use ((:instance acl2::mod-of-+-of-mod-arg2
                            (acl2::x1 (pfield-fix x))
                            (acl2::x2 (* (nfix n) (pfield-fix x)))
                            (acl2::y (pfield-modulus))))
           :in-theory (e/d (pfield-nat-mul pfield-add pfield-fix
                                           pfield::add pfield::fep-fix)
                           (acl2::mod-of-+-of-mod-arg2)))))

(defthm pfield-nat-mul-definition
  (equal (pfield-nat-mul n x)
         (if (zp (nfix n))
             (pfield-zero)
           (pfield-add (pfield-fix x)
                       (pfield-nat-mul (1- (nfix n)) x))))
  :rule-classes nil
  :hints (("Goal" :cases ((zp (nfix n)))
           :use ((:instance pfield-nat-mul-when-zp)
                 (:instance pfield-nat-mul-successor-total
                            (n (1- (nfix n)))))
           :in-theory (disable pfield-nat-mul pfield-add pfield-fix
                               pfield-nat-mul-when-zp
                               pfield-nat-mul-successor-total))))

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
  (implies (and (posp n) (< n (pfield-modulus)))
           (not (equal (pfield-nat-mul n (pfield-one))
                       (pfield-zero))))
  :hints (("Goal" :in-theory (enable pfield-fix pfield-zero
                                      pfield::fep-fix))))

(local
 (defthm pfield-mul-inverse-right-for-characteristic-instance
   (implies (not (equal (pfield-fix x) (pfield-zero)))
            (equal (pfield-mul x (pfield-inv x)) (pfield-one)))
   :hints (("Goal" :use (pfield-mul-inverse-left
                           (:instance pfield-mul-commutative
                            (x x) (y (pfield-inv x))))))))

(defun pfield-no-smaller-positive-annihilator-p (bound)
  (declare (xargs :measure (nfix bound)))
  (if (zp (nfix bound))
      t
    (and (not (equal (pfield-nat-mul (nfix bound) (pfield-one))
                     (pfield-zero)))
         (pfield-no-smaller-positive-annihilator-p
          (1- (nfix bound))))))

(defun pfield-field-characteristic-p (p)
  (and (posp p)
       (equal (pfield-nat-mul p (pfield-one)) (pfield-zero))
       (pfield-no-smaller-positive-annihilator-p (1- p))))

(defthm pfield-no-smaller-positive-annihilator-p-definition
  (equal
   (pfield-no-smaller-positive-annihilator-p bound)
   (if (zp (nfix bound))
       t
     (and (not (equal (pfield-nat-mul (nfix bound) (pfield-one))
                      (pfield-zero)))
          (pfield-no-smaller-positive-annihilator-p
           (1- (nfix bound))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable pfield-no-smaller-positive-annihilator-p))))

(defthm pfield-field-characteristic-p-definition
  (equal (pfield-field-characteristic-p p)
         (and (posp p)
              (equal (pfield-nat-mul p (pfield-one)) (pfield-zero))
              (pfield-no-smaller-positive-annihilator-p (1- p))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
                           '(pfield-field-characteristic-p
                             pfield-one pfield-zero)))))

(defthm pfield-no-smaller-positive-annihilator-p-of-nfix
  (equal (pfield-no-smaller-positive-annihilator-p (nfix bound))
         (pfield-no-smaller-positive-annihilator-p bound)))

(defthm pfield-no-smaller-positive-annihilator-p-of-zero
  (pfield-no-smaller-positive-annihilator-p 0))

(defthm pfield-no-smaller-positive-annihilator-p-of-successor
  (equal
   (pfield-no-smaller-positive-annihilator-p (+ 1 (nfix bound)))
   (and (not (equal (pfield-nat-mul (+ 1 (nfix bound)) (pfield-one))
                    (pfield-zero)))
        (pfield-no-smaller-positive-annihilator-p bound))))

(defthm pfield-no-smaller-positive-annihilator-p-below-modulus
  (implies (and (natp bound) (< bound (pfield-modulus)))
           (pfield-no-smaller-positive-annihilator-p bound))
  :hints (("Goal"
           :induct (pfield-no-smaller-positive-annihilator-p bound)
           :in-theory (enable pfield-no-smaller-positive-annihilator-p))))

(defthm pfield-modulus-is-field-characteristic
  (pfield-field-characteristic-p (pfield-modulus))
  :hints (("Goal"
           :use (pfield-modulus-annihilates-one
                 (:instance
                  pfield-no-smaller-positive-annihilator-p-below-modulus
                  (bound (1- (pfield-modulus)))))
           :in-theory (enable pfield-field-characteristic-p))))

(defmacro def-pfield-characteristic-instance (name generic-theorem)
  `(acl2::def-functional-instance
     ,name ,generic-theorem
     ((field-element-p pfield-element-p) (field-fix pfield-fix)
      (field-zero pfield-zero) (field-one pfield-one)
      (field-add pfield-add) (field-mul pfield-mul)
      (field-neg pfield-neg) (field-inv pfield-inv)
      (field-nat-mul pfield-nat-mul)
      (no-smaller-positive-annihilator-p
       pfield-no-smaller-positive-annihilator-p)
      (field-characteristic-p pfield-field-characteristic-p))
     :by-hint-p t
     :hints (("Goal" :do-not '(preprocess)
               :in-theory (theory 'minimal-theory))
              (and stable-under-simplificationp
                  '(:use (booleanp-of-pfield-element-p
                           pfield-element-p-of-pfield-fix
                           pfield-fix-when-pfield-element-p
                           pfield-fix-idempotent
                           pfield-element-p-of-pfield-zero
                           pfield-element-p-of-pfield-one
                           pfield-zero-not-equal-pfield-one
                           pfield-fix-of-zero pfield-fix-of-one
                           pfield-element-p-of-pfield-add
                           pfield-element-p-of-pfield-mul
                           pfield-element-p-of-pfield-neg
                           pfield-element-p-of-pfield-inv
                           pfield-fix-of-pfield-add pfield-fix-of-pfield-mul
                           pfield-fix-of-pfield-neg pfield-fix-of-pfield-inv
                           pfield-add-of-fixes pfield-add-fix-left
                           pfield-add-fix-right pfield-mul-of-fixes
                           pfield-mul-fix-left pfield-mul-fix-right
                           pfield-neg-of-fix pfield-inv-of-fix
                           pfield-add-associative pfield-add-commutative
                           pfield-add-zero-left pfield-add-inverse-left
                           pfield-add-fixed-congruence
                           pfield-mul-fixed-congruence
                           pfield-mul-associative pfield-mul-commutative
                           pfield-mul-one-left pfield-mul-left-distributive
                           pfield-inv-of-zero pfield-mul-inverse-left
                           pfield-mul-inverse-right-for-characteristic-instance
                           pfield-nat-mul-of-nfix pfield-nat-mul-of-fix
                           pfield-nat-mul-zero pfield-nat-mul-when-zp
                           pfield-nat-mul-of-zero
                           pfield-nat-mul-successor-total
                           pfield-nat-mul-definition
                           pfield-no-smaller-positive-annihilator-p-of-nfix
                           pfield-no-smaller-positive-annihilator-p-of-zero
                           pfield-no-smaller-positive-annihilator-p-of-successor
                           pfield-no-smaller-positive-annihilator-p-definition
                           pfield-field-characteristic-p-definition)
                    :in-theory (theory 'minimal-theory))))))

(def-pfield-characteristic-instance
  posp-when-pfield-field-characteristic-p
  posp-when-field-characteristic-p)
(def-pfield-characteristic-instance
  pfield-nat-mul-of-characteristic-and-one
  field-nat-mul-of-characteristic-and-one)
(def-pfield-characteristic-instance
  pfield-field-characteristic-is-least-positive-annihilator
  field-characteristic-is-least-positive-annihilator)
(def-pfield-characteristic-instance
  pfield-nat-mul-of-characteristic
  field-nat-mul-of-characteristic)
(def-pfield-characteristic-instance
  pfield-field-characteristic-unique
  field-characteristic-unique)

(verify-guards pfield-nat-mul)
(verify-guards pfield-zero)
(verify-guards pfield-add)
(verify-guards pfield-no-smaller-positive-annihilator-p)
(verify-guards pfield-field-characteristic-p)
