(in-package "GPOLY")

(include-book "runtime-p-representation")
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

; The PFIELD add/mul/neg definitions are modular-ring operations for every
; positive modulus.  No theorem below uses INV or a primality hypothesis.

(defthm runtime-p-add-fix-left
  (equal (runtime-p-add (runtime-p-coefficient-fix x p) y p)
         (runtime-p-add x y p)))
(defthm runtime-p-add-fix-right
  (equal (runtime-p-add x (runtime-p-coefficient-fix y p) p)
         (runtime-p-add x y p)))
(defthm runtime-p-mul-fix-left
  (equal (runtime-p-mul (runtime-p-coefficient-fix x p) y p)
         (runtime-p-mul x y p)))
(defthm runtime-p-mul-fix-right
  (equal (runtime-p-mul x (runtime-p-coefficient-fix y p) p)
         (runtime-p-mul x y p)))

(defthm runtime-p-add-associative
  (equal (runtime-p-add (runtime-p-add x y p) z p)
         (runtime-p-add x (runtime-p-add y z p) p))
  :rule-classes nil
  :hints (("Goal" :use ((:instance pfield::add-associative
                          (x (runtime-p-coefficient-fix x p))
                          (y (runtime-p-coefficient-fix y p))
                          (z (runtime-p-coefficient-fix z p))
                          (p (runtime-p-effective-modulus p)))))))
(defthm runtime-p-add-commutative
  (equal (runtime-p-add x y p) (runtime-p-add y x p))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-p-add pfield::add))))
(defthm runtime-p-add-zero-left
  (equal (runtime-p-add (runtime-p-zero p) x p)
         (runtime-p-coefficient-fix x p)))
(defthm runtime-p-add-zero-right
  (equal (runtime-p-add x (runtime-p-zero p) p)
         (runtime-p-coefficient-fix x p)))
(defthm runtime-p-add-inverse-left
  (equal (runtime-p-add (runtime-p-neg x p) x p) (runtime-p-zero p))
  :hints (("Goal" :in-theory (enable runtime-p-add runtime-p-neg pfield::add pfield::neg))))
(defthm runtime-p-add-inverse-right
  (equal (runtime-p-add x (runtime-p-neg x p) p) (runtime-p-zero p))
  :hints (("Goal" :use (runtime-p-add-inverse-left runtime-p-add-commutative))))
(defthm runtime-p-neg-double
  (equal (runtime-p-neg (runtime-p-neg x p) p)
         (runtime-p-coefficient-fix x p)))
(defthm runtime-p-sub-reconstruction
  (equal (runtime-p-add y (runtime-p-sub x y p) p)
         (runtime-p-coefficient-fix x p))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-add-associative
                          (x y) (y x) (z (runtime-p-neg y p)))
                         runtime-p-add-commutative)
           :in-theory (enable runtime-p-sub))))
(defthm runtime-p-sub-self
  (equal (runtime-p-sub x x p) (runtime-p-zero p)))
(defthm runtime-p-sub-cancel-right
  (equal (runtime-p-sub (runtime-p-add x y p) y p)
         (runtime-p-coefficient-fix x p))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-add-associative
                          (z (runtime-p-neg y p))))
           :in-theory (enable runtime-p-sub))))

(defthm runtime-p-mul-associative
  (equal (runtime-p-mul (runtime-p-mul x y p) z p)
         (runtime-p-mul x (runtime-p-mul y z p) p))
  :rule-classes nil
  :hints (("Goal" :use ((:instance pfield::mul-associative
                          (x (runtime-p-coefficient-fix x p))
                          (y (runtime-p-coefficient-fix y p))
                          (z (runtime-p-coefficient-fix z p))
                          (p (runtime-p-effective-modulus p)))))))
(defthm runtime-p-mul-commutative
  (equal (runtime-p-mul x y p) (runtime-p-mul y x p))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-p-mul pfield::mul))))
(defthm runtime-p-mul-one-left
  (equal (runtime-p-mul (runtime-p-one p) x p)
         (runtime-p-coefficient-fix x p)))
(defthm runtime-p-mul-one-right
  (equal (runtime-p-mul x (runtime-p-one p) p)
         (runtime-p-coefficient-fix x p)))
(defthm runtime-p-mul-zero-left
  (equal (runtime-p-mul (runtime-p-zero p) x p) (runtime-p-zero p)))
(defthm runtime-p-mul-zero-right
  (equal (runtime-p-mul x (runtime-p-zero p) p) (runtime-p-zero p)))
(defthm runtime-p-mul-left-distributive
  (equal (runtime-p-mul x (runtime-p-add y z p) p)
         (runtime-p-add (runtime-p-mul x y p) (runtime-p-mul x z p) p))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-p-add runtime-p-mul
                                      pfield::add pfield::mul))))
(defthm runtime-p-mul-right-distributive
  (equal (runtime-p-mul (runtime-p-add x y p) z p)
         (runtime-p-add (runtime-p-mul x z p) (runtime-p-mul y z p) p))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-mul-left-distributive
                          (x z) (y x) (z y))
                         (:instance runtime-p-mul-commutative (x z) (y x))
                         (:instance runtime-p-mul-commutative (x z) (y y))
                         (:instance runtime-p-mul-commutative
                          (x z) (y (runtime-p-add x y p)))))))
(defthm runtime-p-mul-neg-left
  (equal (runtime-p-mul (runtime-p-neg x p) y p)
         (runtime-p-neg (runtime-p-mul x y p) p))
  :hints (("Goal" :use ((:instance pfield::mul-of-neg-arg1
                          (x (runtime-p-coefficient-fix x p))
                          (y (runtime-p-coefficient-fix y p))
                          (p (runtime-p-effective-modulus p)))))))
(defthm runtime-p-mul-neg-right
  (equal (runtime-p-mul x (runtime-p-neg y p) p)
         (runtime-p-neg (runtime-p-mul x y p) p))
  :hints (("Goal" :use ((:instance runtime-p-mul-neg-left (x y) (y x))
                         (:instance runtime-p-mul-commutative)))))
