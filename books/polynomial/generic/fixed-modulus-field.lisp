(in-package "GPOLY")
(include-book "irreducible-modular-inverse")

; A fixed irreducible modulus promotes the existing reduced-polynomial
; operations to a total field interface.  The local linear modulus below is
; only a consistency witness; clients may instantiate any irreducible modulus.
(encapsulate
 (((fixed-modulus-field-modulus) => *))
 (local (defun fixed-modulus-field-modulus () (monomial (gfield::field-one) 1)))
 (defthm fixed-modulus-field-modulus-irreducible
   (poly-irreducible-p (fixed-modulus-field-modulus))
   :rule-classes nil
   :hints (("Goal" :use ((:instance canonical-degree-one-poly-irreducible
                           (poly (monomial (gfield::field-one) 1))))
            :in-theory (enable monomial poly-degree canonical-polynomial-p
                               normalize fix-coefficients trim-trailing-zeros
                               zero-prefix)))))

(defun fixed-modulus-field-element-p (x) (poly-reduced-p x (fixed-modulus-field-modulus)))
(defun fixed-modulus-field-fix (x) (poly-remainder x (fixed-modulus-field-modulus)))
(defun fixed-modulus-field-zero () nil)
(defun fixed-modulus-field-one () (poly-reduced-one (fixed-modulus-field-modulus)))
(defun fixed-modulus-field-add (x y) (poly-reduced-add x y (fixed-modulus-field-modulus)))
(defun fixed-modulus-field-neg (x) (poly-reduced-neg x (fixed-modulus-field-modulus)))
(defun fixed-modulus-field-sub (x y) (poly-reduced-sub x y (fixed-modulus-field-modulus)))
(defun fixed-modulus-field-mul (x y) (poly-reduced-mul x y (fixed-modulus-field-modulus)))
(defun fixed-modulus-field-inv (x)
  (let ((fixed-x (fixed-modulus-field-fix x)))
    (if (equal fixed-x (fixed-modulus-field-zero))
        (fixed-modulus-field-zero)
      (poly-modular-inverse fixed-x (fixed-modulus-field-modulus)))))

(local (in-theory (disable poly-remainder poly-divmod poly-divmod-core
                           poly-modular-inverse poly-monic-extended-euclidean-gcd
                           poly-extended-euclidean-gcd poly-euclidean-gcd
                           poly-reduced-p poly-reduced-add poly-reduced-neg
                           poly-reduced-sub poly-reduced-mul poly-reduced-one)))

(defthm booleanp-of-fixed-modulus-field-element-p (booleanp (fixed-modulus-field-element-p x))
  :rule-classes :type-prescription :hints (("Goal" :in-theory (enable fixed-modulus-field-element-p poly-reduced-p))))
(defthm fixed-modulus-field-element-p-of-fix (fixed-modulus-field-element-p (fixed-modulus-field-fix x))
  :hints (("Goal" :use ((:instance poly-reduced-p-of-poly-remainder (polynomial x) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-element-p fixed-modulus-field-fix))))
(defthm fixed-modulus-field-fix-when-element-p (implies (fixed-modulus-field-element-p x) (equal (fixed-modulus-field-fix x) x))
  :hints (("Goal" :use ((:instance poly-reduced-p-definition (polynomial x) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-element-p fixed-modulus-field-fix))))
(defthm fixed-modulus-field-fix-idempotent (equal (fixed-modulus-field-fix (fixed-modulus-field-fix x)) (fixed-modulus-field-fix x))
  :hints (("Goal" :use ((:instance poly-remainder-idempotent (dividend x) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-fix))))
(defthm fixed-modulus-field-element-p-of-zero (fixed-modulus-field-element-p (fixed-modulus-field-zero)) :hints (("Goal" :use ((:instance poly-reduced-p-of-nil (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-element-p fixed-modulus-field-zero))))
(defthm fixed-modulus-field-element-p-of-one (fixed-modulus-field-element-p (fixed-modulus-field-one)) :hints (("Goal" :use ((:instance poly-reduced-p-of-poly-reduced-one (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-element-p fixed-modulus-field-one))))
(defthm fixed-modulus-field-fix-of-zero (equal (fixed-modulus-field-fix (fixed-modulus-field-zero)) (fixed-modulus-field-zero)) :hints (("Goal" :in-theory (enable fixed-modulus-field-fix fixed-modulus-field-zero))))
(defthm fixed-modulus-field-fix-of-one (equal (fixed-modulus-field-fix (fixed-modulus-field-one)) (fixed-modulus-field-one)) :hints (("Goal" :use ((:instance poly-remainder-of-poly-reduced-one (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-fix fixed-modulus-field-one))))
(defthm fixed-modulus-field-zero-not-equal-one (not (equal (fixed-modulus-field-zero) (fixed-modulus-field-one)))
 :hints (("Goal" :use (fixed-modulus-field-modulus-irreducible (:instance poly-irreducible-p-implies-positive-degree (poly (fixed-modulus-field-modulus))) (:instance poly-reduced-one-positive-degree-modulus (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-zero fixed-modulus-field-one polynomial-one))))

(defthm fixed-modulus-field-element-p-of-add (fixed-modulus-field-element-p (fixed-modulus-field-add x y)) :hints (("Goal" :use ((:instance poly-reduced-p-of-poly-reduced-add (left x) (right y) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-element-p fixed-modulus-field-add))))
(defthm fixed-modulus-field-element-p-of-neg (fixed-modulus-field-element-p (fixed-modulus-field-neg x)) :hints (("Goal" :use ((:instance poly-reduced-p-of-poly-reduced-neg (polynomial x) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-element-p fixed-modulus-field-neg))))
(defthm fixed-modulus-field-element-p-of-sub (fixed-modulus-field-element-p (fixed-modulus-field-sub x y)) :hints (("Goal" :use ((:instance poly-reduced-p-of-poly-reduced-sub (left x) (right y) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-element-p fixed-modulus-field-sub))))
(defthm fixed-modulus-field-element-p-of-mul (fixed-modulus-field-element-p (fixed-modulus-field-mul x y)) :hints (("Goal" :use ((:instance poly-reduced-p-of-poly-reduced-mul (left x) (right y) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-element-p fixed-modulus-field-mul))))
(defthm fixed-modulus-field-fix-of-add (equal (fixed-modulus-field-fix (fixed-modulus-field-add x y)) (fixed-modulus-field-add x y)) :hints (("Goal" :use ((:instance poly-remainder-of-poly-reduced-add (left x) (right y) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-fix fixed-modulus-field-add))))
(defthm fixed-modulus-field-fix-of-neg (equal (fixed-modulus-field-fix (fixed-modulus-field-neg x)) (fixed-modulus-field-neg x)) :hints (("Goal" :use ((:instance poly-remainder-of-poly-reduced-neg (polynomial x) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-fix fixed-modulus-field-neg))))
(defthm fixed-modulus-field-fix-of-sub (equal (fixed-modulus-field-fix (fixed-modulus-field-sub x y)) (fixed-modulus-field-sub x y)) :hints (("Goal" :use ((:instance poly-remainder-of-poly-reduced-sub (left x) (right y) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-fix fixed-modulus-field-sub))))
(defthm fixed-modulus-field-fix-of-mul (equal (fixed-modulus-field-fix (fixed-modulus-field-mul x y)) (fixed-modulus-field-mul x y)) :hints (("Goal" :use ((:instance poly-remainder-of-poly-reduced-mul (left x) (right y) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-fix fixed-modulus-field-mul))))

(defthm fixed-modulus-field-add-of-fixes (equal (fixed-modulus-field-add (fixed-modulus-field-fix x) (fixed-modulus-field-fix y)) (fixed-modulus-field-add x y)) :hints (("Goal" :use ((:instance poly-reduced-add-of-remainders (left x) (right y) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-add fixed-modulus-field-fix))))
(defthm fixed-modulus-field-add-fix-left (equal (fixed-modulus-field-add (fixed-modulus-field-fix x) y) (fixed-modulus-field-add x y)) :hints (("Goal" :use ((:instance fixed-modulus-field-add-of-fixes) (:instance fixed-modulus-field-add-of-fixes (x (fixed-modulus-field-fix x))) fixed-modulus-field-fix-idempotent) :in-theory (disable fixed-modulus-field-add fixed-modulus-field-fix))))
(defthm fixed-modulus-field-add-fix-right (equal (fixed-modulus-field-add x (fixed-modulus-field-fix y)) (fixed-modulus-field-add x y)) :hints (("Goal" :use ((:instance fixed-modulus-field-add-of-fixes) (:instance fixed-modulus-field-add-of-fixes (y (fixed-modulus-field-fix y))) (:instance fixed-modulus-field-fix-idempotent (x y))) :in-theory (disable fixed-modulus-field-add fixed-modulus-field-fix))))
(defthm fixed-modulus-field-mul-of-fixes (equal (fixed-modulus-field-mul (fixed-modulus-field-fix x) (fixed-modulus-field-fix y)) (fixed-modulus-field-mul x y)) :hints (("Goal" :use ((:instance poly-reduced-mul-of-remainders (left x) (right y) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-mul fixed-modulus-field-fix))))
(defthm fixed-modulus-field-mul-fix-left (equal (fixed-modulus-field-mul (fixed-modulus-field-fix x) y) (fixed-modulus-field-mul x y)) :hints (("Goal" :use ((:instance poly-remainder-of-poly-mul-remainder-left (left x) (right y) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-mul fixed-modulus-field-fix poly-reduced-mul))))
(defthm fixed-modulus-field-mul-fix-right (equal (fixed-modulus-field-mul x (fixed-modulus-field-fix y)) (fixed-modulus-field-mul x y)) :hints (("Goal" :use ((:instance poly-remainder-of-poly-mul-remainder-right (left x) (right y) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-mul fixed-modulus-field-fix poly-reduced-mul))))
(defthm fixed-modulus-field-neg-of-fix (equal (fixed-modulus-field-neg (fixed-modulus-field-fix x)) (fixed-modulus-field-neg x)) :hints (("Goal" :use ((:instance poly-reduced-neg-of-remainder (polynomial x) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-neg fixed-modulus-field-fix))))
(defthm fixed-modulus-field-sub-of-fixes (equal (fixed-modulus-field-sub (fixed-modulus-field-fix x) (fixed-modulus-field-fix y)) (fixed-modulus-field-sub x y)) :hints (("Goal" :use ((:instance poly-reduced-sub-of-remainders (left x) (right y) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-sub fixed-modulus-field-fix))))

(defthm fixed-modulus-field-add-fixed-congruence (implies (and (equal (fixed-modulus-field-fix x1) (fixed-modulus-field-fix x2)) (equal (fixed-modulus-field-fix y1) (fixed-modulus-field-fix y2))) (equal (fixed-modulus-field-add x1 y1) (fixed-modulus-field-add x2 y2))) :hints (("Goal" :use ((:instance fixed-modulus-field-add-of-fixes (x x1) (y y1)) (:instance fixed-modulus-field-add-of-fixes (x x2) (y y2))) :in-theory (disable fixed-modulus-field-add fixed-modulus-field-fix fixed-modulus-field-add-of-fixes fixed-modulus-field-add-fix-left fixed-modulus-field-add-fix-right))))
(defthm fixed-modulus-field-mul-fixed-congruence (implies (and (equal (fixed-modulus-field-fix x1) (fixed-modulus-field-fix x2)) (equal (fixed-modulus-field-fix y1) (fixed-modulus-field-fix y2))) (equal (fixed-modulus-field-mul x1 y1) (fixed-modulus-field-mul x2 y2))) :hints (("Goal" :use ((:instance fixed-modulus-field-mul-of-fixes (x x1) (y y1)) (:instance fixed-modulus-field-mul-of-fixes (x x2) (y y2))) :in-theory (disable fixed-modulus-field-mul fixed-modulus-field-fix fixed-modulus-field-mul-of-fixes fixed-modulus-field-mul-fix-left fixed-modulus-field-mul-fix-right))))

(defthm fixed-modulus-field-add-associative (equal (fixed-modulus-field-add (fixed-modulus-field-add x y) z) (fixed-modulus-field-add x (fixed-modulus-field-add y z))) :hints (("Goal" :use ((:instance poly-reduced-add-associative (a x) (b y) (c z) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-add))))
(defthm fixed-modulus-field-add-commutative (equal (fixed-modulus-field-add x y) (fixed-modulus-field-add y x)) :hints (("Goal" :use ((:instance poly-reduced-add-commutative (a x) (b y) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-add))))
(defthm fixed-modulus-field-add-zero-left (equal (fixed-modulus-field-add (fixed-modulus-field-zero) x) (fixed-modulus-field-fix x)) :hints (("Goal" :use ((:instance poly-reduced-add-zero-left (a x) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-add fixed-modulus-field-zero fixed-modulus-field-fix))))
(defthm fixed-modulus-field-add-inverse-left (equal (fixed-modulus-field-add (fixed-modulus-field-neg x) x) (fixed-modulus-field-zero)) :hints (("Goal" :use ((:instance poly-reduced-add-inverse-left (a x) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-add fixed-modulus-field-neg fixed-modulus-field-zero))))
(defthm fixed-modulus-field-mul-associative (equal (fixed-modulus-field-mul (fixed-modulus-field-mul x y) z) (fixed-modulus-field-mul x (fixed-modulus-field-mul y z))) :hints (("Goal" :use ((:instance poly-reduced-mul-associative (a x) (b y) (c z) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-mul))))
(defthm fixed-modulus-field-mul-commutative (equal (fixed-modulus-field-mul x y) (fixed-modulus-field-mul y x)) :hints (("Goal" :use ((:instance poly-reduced-mul-commutative (a x) (b y) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-mul))))
(defthm fixed-modulus-field-mul-one-left (equal (fixed-modulus-field-mul (fixed-modulus-field-one) x) (fixed-modulus-field-fix x)) :hints (("Goal" :use ((:instance poly-reduced-mul-one-left (a x) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-mul fixed-modulus-field-one fixed-modulus-field-fix))))
(defthm fixed-modulus-field-mul-left-distributive (equal (fixed-modulus-field-mul x (fixed-modulus-field-add y z)) (fixed-modulus-field-add (fixed-modulus-field-mul x y) (fixed-modulus-field-mul x z))) :hints (("Goal" :use ((:instance poly-reduced-mul-left-distributive (a x) (b y) (c z) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-mul fixed-modulus-field-add))))
(defthm fixed-modulus-field-sub-as-add-neg (equal (fixed-modulus-field-sub x y) (fixed-modulus-field-add x (fixed-modulus-field-neg y))) :hints (("Goal" :use ((:instance poly-reduced-sub-as-add-neg (a x) (b y) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-sub fixed-modulus-field-add fixed-modulus-field-neg))))
(defthm fixed-modulus-field-sub-self (equal (fixed-modulus-field-sub x x) (fixed-modulus-field-zero)) :hints (("Goal" :use ((:instance poly-reduced-sub-self (a x) (modulus (fixed-modulus-field-modulus)))) :in-theory (e/d (fixed-modulus-field-sub fixed-modulus-field-zero) (fixed-modulus-field-sub-as-add-neg)))))

(local (defthm fixed-modulus-field-modular-inverse-reduced (poly-reduced-p (poly-modular-inverse first modulus) modulus) :rule-classes nil :hints (("Goal" :use ((:instance poly-reduced-p-of-poly-remainder (polynomial (mv-nth 1 (poly-monic-extended-euclidean-gcd first modulus))) (modulus modulus))) :in-theory (e/d (poly-modular-inverse-definition) (poly-reduced-p poly-remainder poly-modular-inverse poly-monic-extended-euclidean-gcd))))))
(defthm fixed-modulus-field-element-p-of-inv (fixed-modulus-field-element-p (fixed-modulus-field-inv x)) :hints (("Goal" :cases ((equal (fixed-modulus-field-fix x) nil)) :use ((:instance fixed-modulus-field-modular-inverse-reduced (first (fixed-modulus-field-fix x)) (modulus (fixed-modulus-field-modulus))) (:instance poly-reduced-p-of-nil (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-element-p fixed-modulus-field-inv fixed-modulus-field-zero))))
(local (defthm fixed-modulus-field-remainder-of-modular-inverse (equal (poly-remainder (poly-modular-inverse first modulus) modulus) (poly-modular-inverse first modulus)) :rule-classes nil :hints (("Goal" :use ((:instance poly-remainder-idempotent (dividend (mv-nth 1 (poly-monic-extended-euclidean-gcd first modulus))) (modulus modulus))) :in-theory (e/d (poly-modular-inverse-definition) (poly-remainder poly-modular-inverse poly-monic-extended-euclidean-gcd))))))
(defthm fixed-modulus-field-fix-of-inv (equal (fixed-modulus-field-fix (fixed-modulus-field-inv x)) (fixed-modulus-field-inv x)) :hints (("Goal" :cases ((equal (fixed-modulus-field-fix x) nil)) :use ((:instance fixed-modulus-field-remainder-of-modular-inverse (first (fixed-modulus-field-fix x)) (modulus (fixed-modulus-field-modulus)))) :in-theory (enable fixed-modulus-field-fix fixed-modulus-field-inv fixed-modulus-field-zero))))
(defthm fixed-modulus-field-inv-of-fix (equal (fixed-modulus-field-inv (fixed-modulus-field-fix x)) (fixed-modulus-field-inv x)) :hints (("Goal" :use (fixed-modulus-field-fix-idempotent) :in-theory (enable fixed-modulus-field-inv))))
(defthm fixed-modulus-field-inv-of-zero (equal (fixed-modulus-field-inv (fixed-modulus-field-zero)) (fixed-modulus-field-zero)) :hints (("Goal" :in-theory (enable fixed-modulus-field-inv fixed-modulus-field-zero fixed-modulus-field-fix))))
(local (defthm fixed-modulus-field-nonzero-inverse-product
 (implies (and (poly-irreducible-p modulus) (not (equal (poly-remainder x modulus) nil)))
          (equal (poly-reduced-mul (poly-modular-inverse (poly-remainder x modulus) modulus) x modulus) (poly-reduced-one modulus)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance normalize-of-poly-remainder (dividend x) (modulus modulus)) (:instance poly-remainder-idempotent (dividend x) (modulus modulus)) (:instance poly-irreducible-p-nonzero-remainder-modular-inverse-left (first (poly-remainder x modulus)) (modulus modulus)) (:instance fixed-modulus-field-remainder-of-modular-inverse (first (poly-remainder x modulus)) (modulus modulus)) (:instance poly-reduced-mul-of-remainders (left (poly-modular-inverse (poly-remainder x modulus) modulus)) (right x) (modulus modulus))) :in-theory (disable poly-remainder poly-reduced-mul poly-reduced-one normalize poly-modular-inverse poly-modular-inverse-definition poly-monic-extended-euclidean-gcd-is-scaled-xgcd poly-reduced-mul-definition poly-reduced-one-definition poly-reduced-mul-commutative poly-irreducible-p)))))
(defthm fixed-modulus-field-mul-inverse-left
 (implies (not (equal (fixed-modulus-field-fix x) (fixed-modulus-field-zero))) (equal (fixed-modulus-field-mul (fixed-modulus-field-inv x) x) (fixed-modulus-field-one)))
 :rule-classes nil
 :hints (("Goal" :use (fixed-modulus-field-modulus-irreducible (:instance fixed-modulus-field-nonzero-inverse-product (modulus (fixed-modulus-field-modulus)))) :in-theory (e/d (fixed-modulus-field-fix fixed-modulus-field-zero fixed-modulus-field-mul fixed-modulus-field-inv fixed-modulus-field-one) (poly-remainder poly-reduced-mul poly-reduced-one poly-modular-inverse poly-modular-inverse-definition poly-monic-extended-euclidean-gcd-is-scaled-xgcd poly-reduced-mul-definition poly-reduced-one-definition poly-irreducible-p)))))
