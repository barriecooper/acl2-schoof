(in-package "GFIELD")

(include-book "kestrel/arithmetic-light/floor" :dir :system)

; A canonical-representative field interface.  Local definitions are only
; consistency witnesses; clients replace the constrained symbols by functional
; instantiation.
(encapsulate
 (((field-element-p *) => *) ((field-fix *) => *)
  ((field-zero) => *) ((field-one) => *)
  ((field-add * *) => *) ((field-mul * *) => *)
  ((field-neg *) => *) ((field-inv *) => *))
 (local (defun field-element-p (x) (booleanp x)))
 (local (defun field-fix (x) (if x t nil)))
 (local (defun field-zero () nil))
 (local (defun field-one () t))
 (local (defun field-add (x y)
          (if (equal (field-fix x) (field-fix y)) nil t)))
 (local (defun field-mul (x y)
          (if (and (field-fix x) (field-fix y)) t nil)))
 (local (defun field-neg (x) (field-fix x)))
 (local (defun field-inv (x) (field-fix x)))

 (defthm booleanp-of-field-element-p
   (booleanp (field-element-p x)) :rule-classes :type-prescription)
 (defthm field-element-p-of-field-fix (field-element-p (field-fix x)))
 (defthm field-fix-when-field-element-p
   (implies (field-element-p x) (equal (field-fix x) x)))
 (defthm field-fix-idempotent
   (equal (field-fix (field-fix x)) (field-fix x)))
 (defthm field-element-p-of-zero (field-element-p (field-zero)))
 (defthm field-element-p-of-one (field-element-p (field-one)))
 (defthm field-zero-not-equal-field-one
   (not (equal (field-zero) (field-one))))
 (defthm field-fix-of-zero (equal (field-fix (field-zero)) (field-zero)))
 (defthm field-fix-of-one (equal (field-fix (field-one)) (field-one)))
 (defthm field-element-p-of-add (field-element-p (field-add x y)))
 (defthm field-element-p-of-mul (field-element-p (field-mul x y)))
 (defthm field-element-p-of-neg (field-element-p (field-neg x)))
 (defthm field-element-p-of-inv (field-element-p (field-inv x)))
 (defthm field-fix-of-add
   (equal (field-fix (field-add x y)) (field-add x y)))
 (defthm field-fix-of-mul
   (equal (field-fix (field-mul x y)) (field-mul x y)))
 (defthm field-fix-of-neg
   (equal (field-fix (field-neg x)) (field-neg x)))
 (defthm field-fix-of-inv
   (equal (field-fix (field-inv x)) (field-inv x)))
 (defthm field-add-of-fixes
   (equal (field-add (field-fix x) (field-fix y)) (field-add x y)))
 (defthm field-add-fix-left
   (equal (field-add (field-fix x) y) (field-add x y)))
 (defthm field-add-fix-right
   (equal (field-add x (field-fix y)) (field-add x y)))
 (defthm field-mul-fix-left
   (equal (field-mul (field-fix x) y) (field-mul x y)))
 (defthm field-mul-fix-right
   (equal (field-mul x (field-fix y)) (field-mul x y)))
 (defthm field-mul-of-fixes
   (equal (field-mul (field-fix x) (field-fix y)) (field-mul x y)))
 (defthm field-neg-of-fix
   (equal (field-neg (field-fix x)) (field-neg x)))
 (defthm field-inv-of-fix
   (equal (field-inv (field-fix x)) (field-inv x)))
 (defthm field-add-associative
   (equal (field-add (field-add x y) z)
          (field-add x (field-add y z))))
 (defthm field-add-commutative
   (equal (field-add x y) (field-add y x)))
 (defthm field-add-zero-left
   (equal (field-add (field-zero) x) (field-fix x)))
 (defthm field-add-inverse-left
   (equal (field-add (field-neg x) x) (field-zero)))
 (defthm field-add-fixed-congruence
   (implies (and (equal (field-fix x1) (field-fix x2))
                 (equal (field-fix y1) (field-fix y2)))
            (equal (field-add x1 y1) (field-add x2 y2))))
 (defthm field-mul-fixed-congruence
   (implies (and (equal (field-fix x1) (field-fix x2))
                 (equal (field-fix y1) (field-fix y2)))
            (equal (field-mul x1 y1) (field-mul x2 y2))))
 (defthm field-mul-associative
   (equal (field-mul (field-mul x y) z)
          (field-mul x (field-mul y z))))
 (defthm field-mul-commutative
   (equal (field-mul x y) (field-mul y x)))
 (defthm field-mul-one-left
   (equal (field-mul (field-one) x) (field-fix x)))
 (defthm field-mul-left-distributive
   (equal (field-mul x (field-add y z))
          (field-add (field-mul x y) (field-mul x z))))
 (defthm field-inv-of-zero
   (equal (field-inv (field-zero)) (field-zero)))
 (defthm field-mul-inverse-left
   (implies (not (equal (field-fix x) (field-zero)))
            (equal (field-mul (field-inv x) x) (field-one)))))

(defun field-equiv (x y) (equal (field-fix x) (field-fix y)))
(defequiv field-equiv)
(defun field-sub (x y) (field-add x (field-neg y)))
(defun field-div (x y) (field-mul x (field-inv y)))
; A deliberately narrow power-instance generator.  Every expansion is three
; ordinary DEFUN events: a linear logical specification, a binary accumulator,
; and the public MBE wrapper.  The logical branch makes proofs inspectable;
; compiled execution uses only the accumulator, whose exponent is shifted
; right once at every recursive call.
(defmacro def-pow-instance (spec fast pow one mul fix)
  `(progn
     (defun ,spec (x n)
       (declare (xargs :measure (nfix n)))
       (let ((n (nfix n)))
         (if (zp n)
             (,one)
           (,mul (,fix x) (,spec x (1- n))))))
     (defun ,fast (acc base n)
       (declare (xargs :guard (natp n)
                       :verify-guards nil
                       :measure (nfix n)
                       :hints (("Goal" :in-theory
                                (enable acl2::<-of-floor-arg1)))))
       (if (not (natp n))
           acc
         (if (zp n)
             acc
           (let ((half (floor n 2))
                 (square (,mul base base)))
             (if (oddp n)
                 (,fast (,mul acc base) square half)
               (,fast acc square half))))))
     (defun ,pow (x n)
       (declare (xargs :guard t :verify-guards nil))
       (mbe :logic (,spec (,fix x) (nfix n))
            :exec (,fast (,one) (,fix x) (nfix n))))))

(def-pow-instance field-pow-spec field-pow-fast field-pow
  field-one field-mul field-fix)

(defthm field-add-zero-right
  (equal (field-add x (field-zero)) (field-fix x)))
(defthm field-add-inverse-right
  (equal (field-add x (field-neg x)) (field-zero))
  :hints (("Goal" :use ((:instance field-add-commutative
                          (x x) (y (field-neg x)))))))

(defthm field-add-left-cancel-forward
  (implies (equal (field-add x y) (field-add x z))
           (equal (field-fix y) (field-fix z)))
  :hints (("Goal" :use ((:instance field-add-associative (x (field-neg x)) (y x) (z y))
                          (:instance field-add-associative (x (field-neg x)) (y x) (z z))))))
(defthm field-add-left-cancel
  (equal (equal (field-add x y) (field-add x z))
         (equal (field-fix y) (field-fix z)))
  :hints (("Goal" :use (field-add-left-cancel-forward
                              (:instance field-add-fixed-congruence
                               (x1 x) (x2 x) (y1 y) (y2 z)))
                  :in-theory (disable field-add-left-cancel-forward))))

(defthm field-additive-inverse-unique
  (implies (equal (field-add x y) (field-zero))
           (equal (field-fix y) (field-neg x)))
  :hints (("Goal" :use ((:instance field-add-left-cancel-forward
                          (x x) (y y) (z (field-neg x)))))))
(defthm field-neg-of-zero
  (equal (field-neg (field-zero)) (field-zero))
  :hints (("Goal" :use ((:instance field-additive-inverse-unique
                          (x (field-zero)) (y (field-zero)))))))
(defthm field-neg-of-neg
  (equal (field-neg (field-neg x)) (field-fix x))
  :hints (("Goal" :use ((:instance field-additive-inverse-unique
                          (x (field-neg x)) (y x))))))

(defthm field-mul-right-distributive
  (equal (field-mul (field-add x y) z)
         (field-add (field-mul x z) (field-mul y z)))
  :hints (("Goal" :use ((:instance field-mul-commutative
                          (x (field-add x y)) (y z))
                         (:instance field-mul-commutative (x z) (y x))
                         (:instance field-mul-commutative (x z) (y y))))))

(defthm field-mul-zero-left
  (equal (field-mul (field-zero) x) (field-zero))
  :hints (("Goal" :use ((:instance field-add-left-cancel-forward
                          (x (field-mul (field-zero) x))
                          (y (field-zero))
                          (z (field-mul (field-zero) x)))
                         (:instance field-mul-right-distributive
                          (x (field-zero)) (y (field-zero)) (z x))))))
(defthm field-mul-zero-right
  (equal (field-mul x (field-zero)) (field-zero)))
(defthm field-sub-self (equal (field-sub x x) (field-zero)))
(defthm field-sub-zero (equal (field-sub x (field-zero)) (field-fix x)))
(defthm field-mul-one-right
  (equal (field-mul x (field-one)) (field-fix x)))

(defthm field-mul-inv-cancel-left
  (implies (not (equal (field-fix x) (field-zero)))
           (equal (field-mul (field-inv x) (field-mul x y))
                  (field-fix y)))
  :hints (("Goal" :use ((:instance field-mul-inverse-left (x x))
                         (:instance field-mul-associative
                          (x (field-inv x)) (y x) (z y)))
                  :in-theory (disable field-mul-associative))))
(defthm field-mul-left-cancel-forward
  (implies (and (not (equal (field-fix x) (field-zero)))
                (equal (field-mul x y) (field-mul x z)))
           (equal (field-fix y) (field-fix z)))
  :hints (("Goal" :use ((:instance field-mul-inv-cancel-left (x x) (y y))
                         (:instance field-mul-inv-cancel-left (x x) (y z))))))
(defthm field-mul-left-cancel
  (implies (not (equal (field-fix x) (field-zero)))
           (equal (equal (field-mul x y) (field-mul x z))
                  (equal (field-fix y) (field-fix z))))
  :hints (("Goal" :use (field-mul-left-cancel-forward
                              (:instance field-mul-fixed-congruence
                               (x1 x) (x2 x) (y1 y) (y2 z)))
                  :in-theory (disable field-mul-left-cancel-forward))))
(defthm field-mul-inverse-right
  (implies (not (equal (field-fix x) (field-zero)))
           (equal (field-mul x (field-inv x)) (field-one)))
  :hints (("Goal" :use ((:instance field-mul-commutative
                          (x x) (y (field-inv x)))))))
(defthm field-multiplicative-inverse-unique
  (implies (and (not (equal (field-fix x) (field-zero)))
                (equal (field-mul x y) (field-one)))
           (equal (field-fix y) (field-inv x)))
  :hints (("Goal" :use ((:instance field-mul-left-cancel-forward
                          (x x) (y y) (z (field-inv x)))
                         (:instance field-mul-inverse-right (x x))))))
(defthm field-inv-of-one
  (equal (field-inv (field-one)) (field-one))
  :hints (("Goal" :use ((:instance field-multiplicative-inverse-unique
                          (x (field-one)) (y (field-one)))))))
(defthm field-inv-nonzero
  (implies (not (equal (field-fix x) (field-zero)))
           (not (equal (field-inv x) (field-zero))))
  :hints (("Goal" :use ((:instance field-mul-inverse-left (x x))))))
(defthm field-inv-of-inv
  (implies (not (equal (field-fix x) (field-zero)))
           (equal (field-inv (field-inv x)) (field-fix x)))
  :hints (("Goal" :use ((:instance field-multiplicative-inverse-unique
                          (x (field-inv x)) (y x))))))
(defthm field-div-by-one
  (equal (field-div x (field-one)) (field-fix x)))

(defthm field-pow-correct
  (equal (field-pow x n) (field-pow-spec (field-fix x) (nfix n)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable field-pow))))
(defthm field-pow-of-field-fix
  (equal (field-pow (field-fix x) n) (field-pow x n))
  :hints (("Goal" :in-theory (enable field-pow))))
(defthm field-pow-of-nfix
  (equal (field-pow x (nfix n)) (field-pow x n))
  :hints (("Goal" :in-theory (enable field-pow))))
(defthm field-pow-zero (equal (field-pow x 0) (field-one))
  :hints (("Goal" :in-theory (enable field-pow field-pow-spec))))
(defthm field-pow-successor-total
  (equal (field-pow x (+ 1 (nfix n)))
         (field-mul x (field-pow x n)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable field-pow field-pow-spec))))
(defthm field-pow-successor
  (implies (natp n)
           (equal (field-pow x (+ 1 n))
                  (field-mul x (field-pow x n))))
  :hints (("Goal" :use field-pow-successor-total)))
(defthm field-pow-one
  (equal (field-pow x 1) (field-fix x))
  :hints (("Goal" :use ((:instance field-pow-successor-total (n 0))))))
(defthm field-pow-of-one
  (equal (field-pow (field-one) n) (field-one))
  :hints (("Goal" :induct (field-pow-spec (field-one) n)
           :in-theory (enable field-pow field-pow-spec))))
(defthm field-element-p-of-pow (field-element-p (field-pow x n))
  :hints (("Goal" :in-theory (enable field-pow))))
(defthm field-element-p-of-pow-spec
  (field-element-p (field-pow-spec x n))
  :hints (("Goal" :induct (field-pow-spec x n)
           :in-theory (enable field-pow-spec))))
(defthm field-mul-power-interchange
  (equal (field-mul x (field-mul a (field-mul x b)))
         (field-mul x (field-mul x (field-mul a b))))
  :hints (("Goal" :use ((:instance field-mul-associative (x a) (y x) (z b))
                          (:instance field-mul-associative (x x) (y a)
                           (z (field-mul x b)))
                          (:instance field-mul-associative (x x) (y x)
                           (z (field-mul a b)))
                          (:instance field-mul-associative (x a) (y b) (z x))
                          (:instance field-mul-commutative
                           (x (field-mul a b)) (y x))
                          (:instance field-mul-commutative (x a) (y x))))))
(defthm field-mul-move-left
  (equal (field-mul x (field-mul a b))
         (field-mul a (field-mul x b)))
  :hints (("Goal" :use ((:instance field-mul-associative
                          (x x) (y a) (z b))
                          (:instance field-mul-associative
                           (x a) (y x) (z b))
                          (:instance field-mul-commutative (x x) (y b))
                          (:instance field-mul-commutative (x x) (y a)))
           :in-theory (disable field-mul-associative
                               field-mul-commutative))))
(defthm field-pow-of-zero
  (equal (field-pow (field-zero) n)
         (if (zp n) (field-one) (field-zero)))
  :hints (("Goal" :induct (field-pow-spec (field-zero) n)
           :in-theory (enable field-pow field-pow-spec))))

(defthm field-pow-add-reversed
  (equal (field-pow x (+ (nfix m) (nfix n)))
         (field-mul (field-pow x n) (field-pow x m)))
  :rule-classes nil
  :hints (("Goal" :induct (field-pow-spec x n)
           :in-theory (enable field-pow field-pow-spec
                              field-mul-associative
                              field-mul-commutative
                              field-mul-move-left
                              field-mul-power-interchange))))

(defthm field-pow-add
  (equal (field-pow x (+ (nfix m) (nfix n)))
         (field-mul (field-pow x m) (field-pow x n)))
  :hints (("Goal" :use (field-pow-add-reversed
                          (:instance field-mul-commutative
                           (x (field-pow x m)) (y (field-pow x n)))))))

(in-theory (disable field-pow-spec field-pow-add))
