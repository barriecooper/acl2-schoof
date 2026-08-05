(in-package "GPOLY")

(include-book "finite-field-reduction")
(include-book "reduced-ring")

; Finite-field-prefixed spelling of the generic polynomial one.  Keeping this
; name explicit lets later reduced-ring and fixed-modulus packages instantiate
; the generic quotient interface without importing coefficient-vector coding.
(defun finite-field-polynomial-one ()
  (declare (xargs :guard t))
  (list (gfield::finite-field-one)))

(defun finite-field-poly-congruent-p (left right modulus)
  (declare (xargs :guard t))
  (equal (finite-field-poly-remainder left modulus)
         (finite-field-poly-remainder right modulus)))

(defun finite-field-poly-reduced-add (left right modulus)
  (declare (xargs :guard t))
  (finite-field-poly-remainder (finite-field-poly-add left right) modulus))

(defun finite-field-poly-reduced-neg (polynomial modulus)
  (declare (xargs :guard t))
  (finite-field-poly-remainder (finite-field-poly-neg polynomial) modulus))

(defun finite-field-poly-reduced-sub (left right modulus)
  (declare (xargs :guard t))
  (finite-field-poly-remainder (finite-field-poly-sub left right) modulus))

(defun finite-field-poly-reduced-mul (left right modulus)
  (declare (xargs :guard t))
  (finite-field-poly-remainder (finite-field-poly-mul left right) modulus))

(defun finite-field-poly-reduced-one (modulus)
  (declare (xargs :guard t))
  (finite-field-poly-remainder (finite-field-polynomial-one) modulus))

(defthm finite-field-polynomial-one-definition
  (equal (finite-field-polynomial-one)
         (list (gfield::finite-field-one)))
  :hints (("Goal" :in-theory (enable finite-field-polynomial-one))))

(defthm finite-field-poly-congruent-p-definition
  (equal (finite-field-poly-congruent-p left right modulus)
         (equal (finite-field-poly-remainder left modulus)
                (finite-field-poly-remainder right modulus)))
  :hints (("Goal" :in-theory (enable finite-field-poly-congruent-p))))

(defthm finite-field-poly-reduced-add-definition
  (equal (finite-field-poly-reduced-add left right modulus)
         (finite-field-poly-remainder (finite-field-poly-add left right) modulus))
  :hints (("Goal" :in-theory (enable finite-field-poly-reduced-add))))

(defthm finite-field-poly-reduced-neg-definition
  (equal (finite-field-poly-reduced-neg polynomial modulus)
         (finite-field-poly-remainder (finite-field-poly-neg polynomial) modulus))
  :hints (("Goal" :in-theory (enable finite-field-poly-reduced-neg))))

(defthm finite-field-poly-reduced-sub-definition
  (equal (finite-field-poly-reduced-sub left right modulus)
         (finite-field-poly-remainder (finite-field-poly-sub left right) modulus))
  :hints (("Goal" :in-theory (enable finite-field-poly-reduced-sub))))

(defthm finite-field-poly-reduced-mul-definition
  (equal (finite-field-poly-reduced-mul left right modulus)
         (finite-field-poly-remainder (finite-field-poly-mul left right) modulus))
  :hints (("Goal" :in-theory (enable finite-field-poly-reduced-mul))))

(defthm finite-field-poly-reduced-one-definition
  (equal (finite-field-poly-reduced-one modulus)
         (finite-field-poly-remainder (finite-field-polynomial-one) modulus))
  :hints (("Goal" :in-theory (enable finite-field-poly-reduced-one))))

(verify-guards finite-field-polynomial-one)
(verify-guards finite-field-poly-congruent-p)
(verify-guards finite-field-poly-reduced-add)
(verify-guards finite-field-poly-reduced-neg)
(verify-guards finite-field-poly-reduced-sub)
(verify-guards finite-field-poly-reduced-mul)
(verify-guards finite-field-poly-reduced-one)

; Keep the staged algebraic prefix narrow: reduced addition commutativity uses
; only the transparent wrapper and polynomial addition commutativity.
(local (in-theory (disable finite-field-poly-reduced-add
                           finite-field-poly-reduced-neg
                           finite-field-poly-reduced-sub
                           finite-field-poly-reduced-mul
                           finite-field-poly-reduced-one
                           finite-field-poly-remainder
                           finite-field-poly-add
                           finite-field-poly-neg
                           finite-field-poly-sub
                           finite-field-poly-mul
                           finite-field-poly-normalize)))

(defthm finite-field-poly-reduced-add-commutative
  (equal (finite-field-poly-reduced-add a b modulus)
         (finite-field-poly-reduced-add b a modulus))
  :hints (("Goal"
           :use ((:instance finite-field-poly-add-commutative
                            (x a) (y b)))
           :in-theory (enable finite-field-poly-reduced-add))))
