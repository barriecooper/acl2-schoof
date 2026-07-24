(in-package "GPOLY")
(include-book "mul")

; Public, total embedding of the coefficient field.  In particular, zero is
; NIL rather than the noncanonical coefficient list (0).
(def-const-instance const gfield::field-fix gfield::field-zero)

(defun polynomial-one ()
  (list (gfield::field-one)))

(verify-guards polynomial-one)

(defthm canonical-polynomial-p-of-polynomial-one
  (canonical-polynomial-p (polynomial-one)))

(defthm poly-mul-of-polynomial-one-left
  (equal (poly-mul (polynomial-one) x) (normalize x))
  :hints (("Goal" :in-theory (enable polynomial-one))))

(defthm poly-mul-of-polynomial-one-right
  (equal (poly-mul x (polynomial-one)) (normalize x))
  :hints (("Goal" :in-theory (enable polynomial-one))))

(defthm canonical-polynomial-p-of-const
  (canonical-polynomial-p (const a))
  :hints (("Goal" :in-theory (enable const))))

(defthm const-of-field-fix
  (equal (const (gfield::field-fix a)) (const a)))

(defthm const-of-field-zero
  (equal (const (gfield::field-zero)) nil))

(defthm const-of-field-one
  (equal (const (gfield::field-one)) (polynomial-one)))

(defthm const-equal-nil
  (equal (equal (const a) nil)
         (equal (gfield::field-fix a) (gfield::field-zero)))
  :hints (("Goal" :in-theory (enable const))))

(defthm coefficients-of-nonzero-const
  (implies (consp (const a))
           (and (equal (car (const a)) (gfield::field-fix a))
                (equal (cdr (const a)) nil)))
  :hints (("Goal" :in-theory (enable const))))

(defthm eval-of-const
  (equal (eval (const a) x) (gfield::field-fix a))
  :hints (("Goal" :in-theory (enable const))))

(defthm eval-of-polynomial-one
  (equal (eval (polynomial-one) x) (gfield::field-one)))

(defthm field-add-when-fixed-right-zero
  (implies (equal (gfield::field-fix b) (gfield::field-zero))
           (equal (gfield::field-add a b) (gfield::field-fix a)))
  :hints (("Goal"
           :use ((:instance gfield::field-add-fixed-congruence
                            (x1 a) (x2 a)
                            (y1 b) (y2 (gfield::field-zero)))))))

(defthm field-add-when-fixed-left-zero
  (implies (equal (gfield::field-fix a) (gfield::field-zero))
           (equal (gfield::field-add a b) (gfield::field-fix b)))
  :hints (("Goal"
           :use ((:instance gfield::field-add-fixed-congruence
                            (x1 a) (x2 (gfield::field-zero))
                            (y1 b) (y2 b))))))

(defthm poly-mul-const-left
  (equal (poly-mul (const a) p) (poly-scale a p))
  :hints (("Goal"
           :cases ((equal (gfield::field-fix a) (gfield::field-zero)))
           :use ((:instance poly-mul-of-constant-left (a a) (x p))
                 (:instance poly-scale-of-field-fix (a a) (x p))
                 (:instance poly-scale-by-zero (x p)))
           :in-theory (e/d (const) (poly-mul-of-constant-left
                                    poly-scale-of-field-fix
                                    poly-scale-by-zero)))))

(defthm poly-mul-const-right
  (equal (poly-mul p (const a)) (poly-scale a p))
  :hints (("Goal"
           :use ((:instance poly-mul-commutative (x p) (y (const a)))
                 (:instance poly-mul-const-left (p p) (a a)))
           :in-theory (disable poly-mul-const-left))))

(defthm poly-add-of-consts
  (equal (poly-add (const a) (const b))
         (const (gfield::field-add a b)))
  :hints (("Goal" :in-theory (enable const poly-add raw-add normalize
                                      trim-trailing-zeros fix-coefficients))))

(defthm poly-neg-of-const
  (equal (poly-neg (const a)) (const (gfield::field-neg a)))
  :hints (("Goal" :in-theory (enable const poly-neg raw-neg normalize
                                      trim-trailing-zeros fix-coefficients))))

(defthm poly-sub-of-consts
  (equal (poly-sub (const a) (const b))
         (const (gfield::field-sub a b)))
  :hints (("Goal" :in-theory (enable gfield::field-sub))))

(defthm poly-mul-of-consts
  (equal (poly-mul (const a) (const b))
         (const (gfield::field-mul a b)))
  :hints (("Goal" :in-theory (enable const poly-scale raw-scale normalize
                                      trim-trailing-zeros fix-coefficients))))

; Ring rearrangements and embedding expansion are deliberately not global
; simplifiers.  The reducing constant and evaluation rules remain enabled.
(in-theory (disable poly-add-commutative poly-add-associative
                    poly-add-of-consts poly-neg-of-const poly-sub-of-consts
                    poly-mul-of-consts))
