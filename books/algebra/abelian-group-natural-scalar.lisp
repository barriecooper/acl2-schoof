(in-package "GFIELD")

(include-book "abelian-group")

; Architecture: this is the transparent, linear reference specification.  Its
; scalar argument is totalised with NFIX, and each successor adds X on the
; left.  A future binary algorithm must be proved equal to this function.
(defun abelian-group-nat-mul (n x)
  (declare (xargs :measure (nfix n)))
  (let ((n (nfix n)))
    (if (zp n)
        (abelian-group-identity)
      (abelian-group-op x
                        (abelian-group-nat-mul (1- n) x)))))

(defthm abelian-group-nat-mul-of-nfix
  (equal (abelian-group-nat-mul (nfix n) x)
         (abelian-group-nat-mul n x)))

(defthm abelian-group-nat-mul-zero
  (equal (abelian-group-nat-mul 0 x)
         (abelian-group-identity)))

(defthm abelian-group-nat-mul-successor-total
  (equal (abelian-group-nat-mul (+ 1 (nfix n)) x)
         (abelian-group-op x (abelian-group-nat-mul n x))))

(defthm abelian-group-nat-mul-successor
  (implies (natp n)
           (equal (abelian-group-nat-mul (+ 1 n) x)
                  (abelian-group-op x
                                    (abelian-group-nat-mul n x)))))

(defthm abelian-group-right-identity
  (implies (and (abelian-group-context-p)
                (abelian-group-element-p x))
           (equal (abelian-group-op x (abelian-group-identity)) x))
  :hints (("Goal" :use ((:instance abelian-group-commutativity
                          (y (abelian-group-identity)))
                         abelian-group-identity-in-carrier
                         (:instance abelian-group-left-identity (x x))))))

(defthm abelian-group-element-p-of-nat-mul
  (implies (and (abelian-group-context-p)
                (natp n)
                (abelian-group-element-p x))
           (abelian-group-element-p (abelian-group-nat-mul n x)))
  :hints (("Goal" :induct (abelian-group-nat-mul n x)
           :in-theory (enable abelian-group-nat-mul))))

(defthm abelian-group-nat-mul-one
  (implies (and (abelian-group-context-p)
                (abelian-group-element-p x))
           (equal (abelian-group-nat-mul 1 x) x))
  :hints (("Goal" :use ((:instance abelian-group-right-identity (x x)))
           :in-theory (enable abelian-group-nat-mul))))

(defthm abelian-group-nat-mul-of-sum
  (implies (and (abelian-group-context-p)
                (natp m)
                (natp n)
                (abelian-group-element-p x))
           (equal (abelian-group-nat-mul (+ m n) x)
                  (abelian-group-op (abelian-group-nat-mul m x)
                                    (abelian-group-nat-mul n x))))
  :hints (("Goal" :induct (abelian-group-nat-mul m x)
           :in-theory (e/d (abelian-group-nat-mul
                            abelian-group-associativity)
                           (abelian-group-commutativity)))))

(defthm abelian-group-swap-first-two
  (implies (and (abelian-group-context-p)
                (abelian-group-element-p y)
                (abelian-group-element-p a)
                (abelian-group-element-p b))
           (equal (abelian-group-op y (abelian-group-op a b))
                  (abelian-group-op a (abelian-group-op y b))))
  :hints (("Goal"
           :use ((:instance abelian-group-commutativity (x y) (y a))
                 (:instance abelian-group-associativity
                            (x y) (y a) (z b))
                 (:instance abelian-group-associativity
                            (x a) (y y) (z b)))
           :in-theory (disable abelian-group-associativity
                               abelian-group-commutativity))))

(defthm abelian-group-nat-mul-distributes-over-op
  (implies (and (abelian-group-context-p)
                (natp n)
                (abelian-group-element-p x)
                (abelian-group-element-p y))
           (equal (abelian-group-nat-mul n (abelian-group-op x y))
                  (abelian-group-op (abelian-group-nat-mul n x)
                                    (abelian-group-nat-mul n y))))
  :hints (("Goal" :induct (abelian-group-nat-mul n x)
           :in-theory (e/d (abelian-group-nat-mul
                            abelian-group-associativity)
                           (abelian-group-commutativity)))))

(verify-guards abelian-group-nat-mul)
