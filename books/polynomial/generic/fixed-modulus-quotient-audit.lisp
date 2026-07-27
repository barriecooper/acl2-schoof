(in-package "GPOLY")
(include-book "irreducible-modular-inverse")

; Experimental checkpoint only: a later staged audit will functionally
; instantiate these wrappers.  The sole modulus assumption is irreducibility.
(encapsulate
 (((audit-modulus) => *))
 (local (defun audit-modulus () (monomial (gfield::field-one) 1)))
 (defthm audit-modulus-irreducible
   (poly-irreducible-p (audit-modulus))
   :rule-classes nil
   :hints (("Goal" :use ((:instance canonical-degree-one-poly-irreducible
                           (poly (monomial (gfield::field-one) 1))))
            :in-theory (enable monomial poly-degree canonical-polynomial-p
                               normalize fix-coefficients trim-trailing-zeros
                               zero-prefix)))))

(defun audit-carrier (x) (poly-reduced-p x (audit-modulus)))
(defun audit-fix (x) (poly-remainder x (audit-modulus)))
(defun audit-zero () nil)
(defun audit-one () (poly-reduced-one (audit-modulus)))
(defun audit-add (x y) (poly-reduced-add x y (audit-modulus)))
(defun audit-neg (x) (poly-reduced-neg x (audit-modulus)))
(defun audit-sub (x y) (poly-reduced-sub x y (audit-modulus)))
(defun audit-mul (x y) (poly-reduced-mul x y (audit-modulus)))
(defun audit-inv (x)
  (let ((fixed-x (audit-fix x)))
    (if (equal fixed-x (audit-zero))
        (audit-zero)
      (poly-modular-inverse fixed-x (audit-modulus)))))

(local (in-theory (disable poly-remainder poly-divmod poly-divmod-core
                           poly-modular-inverse poly-monic-extended-euclidean-gcd
                           poly-extended-euclidean-gcd poly-euclidean-gcd
                           poly-reduced-p poly-reduced-add poly-reduced-neg
                           poly-reduced-sub poly-reduced-mul poly-reduced-one)))

(defthm audit-booleanp-of-carrier (booleanp (audit-carrier x))
  :rule-classes :type-prescription :hints (("Goal" :in-theory (enable audit-carrier poly-reduced-p))))
(defthm audit-carrier-of-fix (audit-carrier (audit-fix x))
  :hints (("Goal" :use ((:instance poly-reduced-p-of-poly-remainder (polynomial x) (modulus (audit-modulus)))) :in-theory (enable audit-carrier audit-fix))))
(defthm audit-fix-when-carrier (implies (audit-carrier x) (equal (audit-fix x) x))
  :hints (("Goal" :use ((:instance poly-reduced-p-definition (polynomial x) (modulus (audit-modulus)))) :in-theory (enable audit-carrier audit-fix))))
(defthm audit-fix-idempotent (equal (audit-fix (audit-fix x)) (audit-fix x))
  :hints (("Goal" :use ((:instance poly-remainder-idempotent (dividend x) (modulus (audit-modulus)))) :in-theory (enable audit-fix))))
(defthm audit-carrier-of-zero (audit-carrier (audit-zero)) :hints (("Goal" :use ((:instance poly-reduced-p-of-nil (modulus (audit-modulus)))) :in-theory (enable audit-carrier audit-zero))))
(defthm audit-carrier-of-one (audit-carrier (audit-one)) :hints (("Goal" :use ((:instance poly-reduced-p-of-poly-reduced-one (modulus (audit-modulus)))) :in-theory (enable audit-carrier audit-one))))
(defthm audit-fix-of-zero (equal (audit-fix (audit-zero)) (audit-zero)) :hints (("Goal" :in-theory (enable audit-fix audit-zero))))
(defthm audit-fix-of-one (equal (audit-fix (audit-one)) (audit-one)) :hints (("Goal" :use ((:instance poly-remainder-of-poly-reduced-one (modulus (audit-modulus)))) :in-theory (enable audit-fix audit-one))))
(defthm audit-zero-not-equal-one (not (equal (audit-zero) (audit-one)))
 :hints (("Goal" :use (audit-modulus-irreducible (:instance poly-irreducible-p-implies-positive-degree (poly (audit-modulus))) (:instance poly-reduced-one-positive-degree-modulus (modulus (audit-modulus)))) :in-theory (enable audit-zero audit-one polynomial-one))))

(defthm audit-carrier-of-add (audit-carrier (audit-add x y)) :hints (("Goal" :use ((:instance poly-reduced-p-of-poly-reduced-add (left x) (right y) (modulus (audit-modulus)))) :in-theory (enable audit-carrier audit-add))))
(defthm audit-carrier-of-neg (audit-carrier (audit-neg x)) :hints (("Goal" :use ((:instance poly-reduced-p-of-poly-reduced-neg (polynomial x) (modulus (audit-modulus)))) :in-theory (enable audit-carrier audit-neg))))
(defthm audit-carrier-of-sub (audit-carrier (audit-sub x y)) :hints (("Goal" :use ((:instance poly-reduced-p-of-poly-reduced-sub (left x) (right y) (modulus (audit-modulus)))) :in-theory (enable audit-carrier audit-sub))))
(defthm audit-carrier-of-mul (audit-carrier (audit-mul x y)) :hints (("Goal" :use ((:instance poly-reduced-p-of-poly-reduced-mul (left x) (right y) (modulus (audit-modulus)))) :in-theory (enable audit-carrier audit-mul))))
(defthm audit-fix-of-add (equal (audit-fix (audit-add x y)) (audit-add x y)) :hints (("Goal" :use ((:instance poly-remainder-of-poly-reduced-add (left x) (right y) (modulus (audit-modulus)))) :in-theory (enable audit-fix audit-add))))
(defthm audit-fix-of-neg (equal (audit-fix (audit-neg x)) (audit-neg x)) :hints (("Goal" :use ((:instance poly-remainder-of-poly-reduced-neg (polynomial x) (modulus (audit-modulus)))) :in-theory (enable audit-fix audit-neg))))
(defthm audit-fix-of-sub (equal (audit-fix (audit-sub x y)) (audit-sub x y)) :hints (("Goal" :use ((:instance poly-remainder-of-poly-reduced-sub (left x) (right y) (modulus (audit-modulus)))) :in-theory (enable audit-fix audit-sub))))
(defthm audit-fix-of-mul (equal (audit-fix (audit-mul x y)) (audit-mul x y)) :hints (("Goal" :use ((:instance poly-remainder-of-poly-reduced-mul (left x) (right y) (modulus (audit-modulus)))) :in-theory (enable audit-fix audit-mul))))

(defthm audit-add-of-fixes (equal (audit-add (audit-fix x) (audit-fix y)) (audit-add x y)) :hints (("Goal" :use ((:instance poly-reduced-add-of-remainders (left x) (right y) (modulus (audit-modulus)))) :in-theory (enable audit-add audit-fix))))
(defthm audit-add-fix-left (equal (audit-add (audit-fix x) y) (audit-add x y)) :hints (("Goal" :use ((:instance audit-add-of-fixes) (:instance audit-add-of-fixes (x (audit-fix x))) audit-fix-idempotent) :in-theory (disable audit-add audit-fix))))
(defthm audit-add-fix-right (equal (audit-add x (audit-fix y)) (audit-add x y)) :hints (("Goal" :use ((:instance audit-add-of-fixes) (:instance audit-add-of-fixes (y (audit-fix y))) (:instance audit-fix-idempotent (x y))) :in-theory (disable audit-add audit-fix))))
(defthm audit-mul-of-fixes (equal (audit-mul (audit-fix x) (audit-fix y)) (audit-mul x y)) :hints (("Goal" :use ((:instance poly-reduced-mul-of-remainders (left x) (right y) (modulus (audit-modulus)))) :in-theory (enable audit-mul audit-fix))))
(defthm audit-mul-fix-left (equal (audit-mul (audit-fix x) y) (audit-mul x y)) :hints (("Goal" :use ((:instance poly-remainder-of-poly-mul-remainder-left (left x) (right y) (modulus (audit-modulus)))) :in-theory (enable audit-mul audit-fix poly-reduced-mul))))
(defthm audit-mul-fix-right (equal (audit-mul x (audit-fix y)) (audit-mul x y)) :hints (("Goal" :use ((:instance poly-remainder-of-poly-mul-remainder-right (left x) (right y) (modulus (audit-modulus)))) :in-theory (enable audit-mul audit-fix poly-reduced-mul))))
(defthm audit-neg-of-fix (equal (audit-neg (audit-fix x)) (audit-neg x)) :hints (("Goal" :use ((:instance poly-reduced-neg-of-remainder (polynomial x) (modulus (audit-modulus)))) :in-theory (enable audit-neg audit-fix))))
(defthm audit-sub-of-fixes (equal (audit-sub (audit-fix x) (audit-fix y)) (audit-sub x y)) :hints (("Goal" :use ((:instance poly-reduced-sub-of-remainders (left x) (right y) (modulus (audit-modulus)))) :in-theory (enable audit-sub audit-fix))))

(defthm audit-add-fixed-congruence (implies (and (equal (audit-fix x1) (audit-fix x2)) (equal (audit-fix y1) (audit-fix y2))) (equal (audit-add x1 y1) (audit-add x2 y2))) :hints (("Goal" :use ((:instance audit-add-of-fixes (x x1) (y y1)) (:instance audit-add-of-fixes (x x2) (y y2))) :in-theory (disable audit-add audit-fix audit-add-of-fixes audit-add-fix-left audit-add-fix-right))))
(defthm audit-mul-fixed-congruence (implies (and (equal (audit-fix x1) (audit-fix x2)) (equal (audit-fix y1) (audit-fix y2))) (equal (audit-mul x1 y1) (audit-mul x2 y2))) :hints (("Goal" :use ((:instance audit-mul-of-fixes (x x1) (y y1)) (:instance audit-mul-of-fixes (x x2) (y y2))) :in-theory (disable audit-mul audit-fix audit-mul-of-fixes audit-mul-fix-left audit-mul-fix-right))))

(defthm audit-add-associative (equal (audit-add (audit-add x y) z) (audit-add x (audit-add y z))) :hints (("Goal" :use ((:instance poly-reduced-add-associative (a x) (b y) (c z) (modulus (audit-modulus)))) :in-theory (enable audit-add))))
(defthm audit-add-commutative (equal (audit-add x y) (audit-add y x)) :hints (("Goal" :use ((:instance poly-reduced-add-commutative (a x) (b y) (modulus (audit-modulus)))) :in-theory (enable audit-add))))
(defthm audit-add-zero-left (equal (audit-add (audit-zero) x) (audit-fix x)) :hints (("Goal" :use ((:instance poly-reduced-add-zero-left (a x) (modulus (audit-modulus)))) :in-theory (enable audit-add audit-zero audit-fix))))
(defthm audit-add-inverse-left (equal (audit-add (audit-neg x) x) (audit-zero)) :hints (("Goal" :use ((:instance poly-reduced-add-inverse-left (a x) (modulus (audit-modulus)))) :in-theory (enable audit-add audit-neg audit-zero))))
(defthm audit-mul-associative (equal (audit-mul (audit-mul x y) z) (audit-mul x (audit-mul y z))) :hints (("Goal" :use ((:instance poly-reduced-mul-associative (a x) (b y) (c z) (modulus (audit-modulus)))) :in-theory (enable audit-mul))))
(defthm audit-mul-commutative (equal (audit-mul x y) (audit-mul y x)) :hints (("Goal" :use ((:instance poly-reduced-mul-commutative (a x) (b y) (modulus (audit-modulus)))) :in-theory (enable audit-mul))))
(defthm audit-mul-one-left (equal (audit-mul (audit-one) x) (audit-fix x)) :hints (("Goal" :use ((:instance poly-reduced-mul-one-left (a x) (modulus (audit-modulus)))) :in-theory (enable audit-mul audit-one audit-fix))))
(defthm audit-mul-left-distributive (equal (audit-mul x (audit-add y z)) (audit-add (audit-mul x y) (audit-mul x z))) :hints (("Goal" :use ((:instance poly-reduced-mul-left-distributive (a x) (b y) (c z) (modulus (audit-modulus)))) :in-theory (enable audit-mul audit-add))))
(defthm audit-sub-as-add-neg (equal (audit-sub x y) (audit-add x (audit-neg y))) :hints (("Goal" :use ((:instance poly-reduced-sub-as-add-neg (a x) (b y) (modulus (audit-modulus)))) :in-theory (enable audit-sub audit-add audit-neg))))
(defthm audit-sub-self (equal (audit-sub x x) (audit-zero)) :hints (("Goal" :use ((:instance poly-reduced-sub-self (a x) (modulus (audit-modulus)))) :in-theory (e/d (audit-sub audit-zero) (audit-sub-as-add-neg)))))

(local (defthm audit-modular-inverse-reduced (poly-reduced-p (poly-modular-inverse first modulus) modulus) :rule-classes nil :hints (("Goal" :use ((:instance poly-reduced-p-of-poly-remainder (polynomial (mv-nth 1 (poly-monic-extended-euclidean-gcd first modulus))) (modulus modulus))) :in-theory (e/d (poly-modular-inverse-definition) (poly-reduced-p poly-remainder poly-modular-inverse poly-monic-extended-euclidean-gcd))))))
(defthm audit-carrier-of-inv (audit-carrier (audit-inv x)) :hints (("Goal" :cases ((equal (audit-fix x) nil)) :use ((:instance audit-modular-inverse-reduced (first (audit-fix x)) (modulus (audit-modulus))) (:instance poly-reduced-p-of-nil (modulus (audit-modulus)))) :in-theory (enable audit-carrier audit-inv audit-zero))))
(local (defthm audit-remainder-of-modular-inverse (equal (poly-remainder (poly-modular-inverse first modulus) modulus) (poly-modular-inverse first modulus)) :rule-classes nil :hints (("Goal" :use ((:instance poly-remainder-idempotent (dividend (mv-nth 1 (poly-monic-extended-euclidean-gcd first modulus))) (modulus modulus))) :in-theory (e/d (poly-modular-inverse-definition) (poly-remainder poly-modular-inverse poly-monic-extended-euclidean-gcd))))))
(defthm audit-fix-of-inv (equal (audit-fix (audit-inv x)) (audit-inv x)) :hints (("Goal" :cases ((equal (audit-fix x) nil)) :use ((:instance audit-remainder-of-modular-inverse (first (audit-fix x)) (modulus (audit-modulus)))) :in-theory (enable audit-fix audit-inv audit-zero))))
(defthm audit-inv-of-fix (equal (audit-inv (audit-fix x)) (audit-inv x)) :hints (("Goal" :use (audit-fix-idempotent) :in-theory (enable audit-inv))))
(defthm audit-inv-of-zero (equal (audit-inv (audit-zero)) (audit-zero)) :hints (("Goal" :in-theory (enable audit-inv audit-zero audit-fix))))
(local (defthm audit-nonzero-inverse-product
 (implies (and (poly-irreducible-p modulus) (not (equal (poly-remainder x modulus) nil)))
          (equal (poly-reduced-mul (poly-modular-inverse (poly-remainder x modulus) modulus) x modulus) (poly-reduced-one modulus)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance normalize-of-poly-remainder (dividend x) (modulus modulus)) (:instance poly-remainder-idempotent (dividend x) (modulus modulus)) (:instance poly-irreducible-p-nonzero-remainder-modular-inverse-left (first (poly-remainder x modulus)) (modulus modulus)) (:instance audit-remainder-of-modular-inverse (first (poly-remainder x modulus)) (modulus modulus)) (:instance poly-reduced-mul-of-remainders (left (poly-modular-inverse (poly-remainder x modulus) modulus)) (right x) (modulus modulus))) :in-theory (disable poly-remainder poly-reduced-mul poly-reduced-one normalize poly-modular-inverse poly-modular-inverse-definition poly-monic-extended-euclidean-gcd-is-scaled-xgcd poly-reduced-mul-definition poly-reduced-one-definition poly-reduced-mul-commutative poly-irreducible-p)))))
(defthm audit-inverse-left
 (implies (not (equal (audit-fix x) (audit-zero))) (equal (audit-mul (audit-inv x) x) (audit-one)))
 :rule-classes nil
 :hints (("Goal" :use (audit-modulus-irreducible (:instance audit-nonzero-inverse-product (modulus (audit-modulus)))) :in-theory (e/d (audit-fix audit-zero audit-mul audit-inv audit-one) (poly-remainder poly-reduced-mul poly-reduced-one poly-modular-inverse poly-modular-inverse-definition poly-monic-extended-euclidean-gcd-is-scaled-xgcd poly-reduced-mul-definition poly-reduced-one-definition poly-irreducible-p)))))
