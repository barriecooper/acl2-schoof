(in-package "GPOLY")

(include-book "runtime-p-representation")

; This book deliberately implements only monic division.  In particular, no
; coefficient inverse occurs anywhere in this execution path.
(defun runtime-p-poly-degree (x p)
  (let ((x (runtime-p-normalize x p)))
    (if (consp x) (1- (len x)) -1)))

(defun runtime-p-poly-leading-coefficient (x p)
  (let ((x (runtime-p-normalize x p)))
    (if (consp x) (car (last x)) (runtime-p-zero p))))

(defun runtime-p-monic-polynomial-p (x p)
  (equal (runtime-p-poly-leading-coefficient x p)
         (runtime-p-one p)))

(defun runtime-p-monomial (coefficient degree p)
  (declare (xargs :measure (nfix degree)))
  (if (zp (nfix degree))
      (runtime-p-normalize (list coefficient) p)
    (cons 0 (runtime-p-monomial coefficient (1- (nfix degree)) p))))

; The result is (term . next-remainder).  The caller only enters the active
; branch for normalized monic DIVISOR and sufficiently long REMAINDER.
(defun runtime-p-monic-division-step (remainder divisor p)
  (let* ((remainder (runtime-p-normalize remainder p))
         (divisor (runtime-p-normalize divisor p)))
    (if (and (runtime-p-monic-polynomial-p divisor p)
             (consp remainder)
             (<= (len divisor) (len remainder)))
        (let ((term
               (runtime-p-monomial
                (runtime-p-poly-leading-coefficient remainder p)
                (- (len remainder) (len divisor)) p)))
          (cons term
                (runtime-p-poly-sub
                 remainder (runtime-p-poly-mul term divisor p) p)))
      (cons nil remainder))))

; A single recursion computes both projections.  FUEL is an execution
; totalizer.  The public call supplies the normalized dividend length; every
; genuine monic step cancels its leading coefficient, so this is also a bound
; on the strict normalized-length descent.
(defun runtime-p-monic-divmod-core (fuel quotient remainder divisor p)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp (nfix fuel))
          (not (runtime-p-monic-polynomial-p divisor p))
          (not (consp remainder))
          (< (len remainder) (len divisor)))
      (cons (runtime-p-normalize quotient p) remainder)
    (let ((step (runtime-p-monic-division-step remainder divisor p)))
      (runtime-p-monic-divmod-core
       (1- (nfix fuel))
       (runtime-p-poly-add quotient (car step) p)
       (cdr step) divisor p))))

(defun runtime-p-monic-divmod (dividend modulus p)
  (let* ((dividend (runtime-p-normalize dividend p))
         (modulus (runtime-p-normalize modulus p)))
    (if (runtime-p-monic-polynomial-p modulus p)
        (runtime-p-monic-divmod-core
         (len dividend) nil dividend modulus p)
      (cons nil dividend))))

(defun runtime-p-monic-quotient (dividend modulus p)
  (car (runtime-p-monic-divmod dividend modulus p)))

(defun runtime-p-monic-remainder (dividend modulus p)
  (cdr (runtime-p-monic-divmod dividend modulus p)))

(defun runtime-p-reduced-add (x y modulus p)
  (runtime-p-monic-remainder (runtime-p-poly-add x y p) modulus p))
(defun runtime-p-reduced-neg (x modulus p)
  (runtime-p-monic-remainder (runtime-p-poly-neg x p) modulus p))
(defun runtime-p-reduced-sub (x y modulus p)
  (runtime-p-monic-remainder (runtime-p-poly-sub x y p) modulus p))
(defun runtime-p-reduced-mul (x y modulus p)
  ; Exactly one reduction of the unreduced product.
  (runtime-p-monic-remainder (runtime-p-poly-mul x y p) modulus p))
(defun runtime-p-reduced-zero (modulus p)
  (runtime-p-monic-remainder nil modulus p))
(defun runtime-p-reduced-one (modulus p)
  (runtime-p-monic-remainder (list (runtime-p-one p)) modulus p))

(defthm runtime-p-monic-divmod-nonmonic
  (implies (not (runtime-p-monic-polynomial-p modulus p))
           (equal (runtime-p-monic-divmod dividend modulus p)
                  (cons nil (runtime-p-normalize dividend p))))
  :rule-classes nil)

(defthm runtime-p-monic-remainder-nonmonic
  (implies (not (runtime-p-monic-polynomial-p modulus p))
           (equal (runtime-p-monic-remainder dividend modulus p)
                  (runtime-p-normalize dividend p))))

(defthm runtime-p-monic-quotient-nonmonic
  (implies (not (runtime-p-monic-polynomial-p modulus p))
           (equal (runtime-p-monic-quotient dividend modulus p) nil)))

(defthm runtime-p-canonical-polynomial-p-of-monic-division-step-remainder
  (runtime-p-canonical-polynomial-p
   (cdr (runtime-p-monic-division-step remainder divisor p)) p)
  :hints (("Goal" :in-theory (enable runtime-p-monic-division-step))))

(defthm runtime-p-canonical-polynomial-p-of-monic-divmod-core-remainder
  (implies (runtime-p-canonical-polynomial-p remainder p)
           (runtime-p-canonical-polynomial-p
            (cdr (runtime-p-monic-divmod-core
                  fuel quotient remainder divisor p)) p))
  :hints (("Goal"
           :induct (runtime-p-monic-divmod-core
                    fuel quotient remainder divisor p)
           :in-theory (e/d (runtime-p-monic-divmod-core)
                           (runtime-p-normalize
                            runtime-p-monic-division-step
                            runtime-p-poly-add
                            runtime-p-poly-sub
                            runtime-p-poly-mul
                            runtime-p-canonical-polynomial-p)))
          ))

(defthm runtime-p-canonical-polynomial-p-of-monic-remainder
  (runtime-p-canonical-polynomial-p
   (runtime-p-monic-remainder dividend modulus p) p)
  :hints (("Goal"
           :use ((:instance
                  runtime-p-canonical-polynomial-p-of-monic-divmod-core-remainder
                  (fuel (len (runtime-p-normalize dividend p)))
                  (quotient nil)
                  (remainder (runtime-p-normalize dividend p))
                  (divisor (runtime-p-normalize modulus p))))
           :in-theory (e/d (runtime-p-monic-remainder runtime-p-monic-divmod)
                           (runtime-p-monic-divmod-core
                            runtime-p-normalize
                            runtime-p-canonical-polynomial-p)))))

(defthm runtime-p-normalize-of-monic-remainder
  (equal (runtime-p-normalize
          (runtime-p-monic-remainder dividend modulus p) p)
         (runtime-p-monic-remainder dividend modulus p))
  :hints (("Goal"
           :use ((:instance
                  runtime-p-canonical-polynomial-p-of-monic-remainder)
                 (:instance runtime-p-normalize-when-canonical
                  (xs (runtime-p-monic-remainder dividend modulus p))))
           :in-theory (disable runtime-p-monic-remainder
                               runtime-p-normalize
                               runtime-p-canonical-polynomial-p))))

(verify-guards runtime-p-poly-degree)
(verify-guards runtime-p-poly-leading-coefficient)
(verify-guards runtime-p-monic-polynomial-p)
(verify-guards runtime-p-monomial)
(verify-guards runtime-p-monic-division-step)
(verify-guards runtime-p-monic-divmod-core)
(verify-guards runtime-p-monic-divmod)
(verify-guards runtime-p-monic-quotient)
(verify-guards runtime-p-monic-remainder)
(verify-guards runtime-p-reduced-add)
(verify-guards runtime-p-reduced-neg)
(verify-guards runtime-p-reduced-sub)
(verify-guards runtime-p-reduced-mul)
(verify-guards runtime-p-reduced-zero)
(verify-guards runtime-p-reduced-one)
