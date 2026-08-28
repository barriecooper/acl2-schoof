(in-package "GPOLY")

(include-book "runtime-p-monic-associate")
(include-book "runtime-p-monic-remainder-operations")

; Divisor-first, executable divisibility through the existing general remainder.
(defun runtime-p-poly-divides-p (divisor dividend p)
  (declare (xargs :guard t))
  (equal (runtime-p-remainder dividend divisor p) nil))

(defun runtime-p-poly-common-divisor-p (candidate first second p)
  (declare (xargs :guard t))
  (and (runtime-p-poly-divides-p candidate first p)
       (runtime-p-poly-divides-p candidate second p)))

(defthm booleanp-of-runtime-p-poly-divides-p
  (booleanp (runtime-p-poly-divides-p divisor dividend p)))

(defthm runtime-p-poly-divides-p-iff-zero-remainder
  (iff (runtime-p-poly-divides-p divisor dividend p)
       (equal (runtime-p-remainder dividend divisor p) nil))
  :rule-classes nil)

(defthm runtime-p-poly-divides-p-of-normalize-divisor
  (equal (runtime-p-poly-divides-p (runtime-p-normalize divisor p) dividend p)
         (runtime-p-poly-divides-p divisor dividend p))
  :hints (("Goal" :in-theory (enable runtime-p-poly-divides-p))))

(defthm runtime-p-poly-divides-p-of-normalize-dividend
  (equal (runtime-p-poly-divides-p divisor (runtime-p-normalize dividend p) p)
         (runtime-p-poly-divides-p divisor dividend p))
  :hints (("Goal" :in-theory (enable runtime-p-poly-divides-p))))

(defthm booleanp-of-runtime-p-poly-common-divisor-p
  (booleanp (runtime-p-poly-common-divisor-p candidate first second p)))

(defthm runtime-p-poly-common-divisor-p-implies-divides-first
  (implies (runtime-p-poly-common-divisor-p candidate first second p)
           (runtime-p-poly-divides-p candidate first p))
  :rule-classes :forward-chaining)

(defthm runtime-p-poly-common-divisor-p-implies-divides-second
  (implies (runtime-p-poly-common-divisor-p candidate first second p)
           (runtime-p-poly-divides-p candidate second p))
  :rule-classes :forward-chaining)

(defthm runtime-p-poly-common-divisor-p-of-normalize-candidate
  (equal (runtime-p-poly-common-divisor-p
          (runtime-p-normalize candidate p) first second p)
         (runtime-p-poly-common-divisor-p candidate first second p)))

(defthm runtime-p-poly-common-divisor-p-of-normalize-first
  (equal (runtime-p-poly-common-divisor-p
          candidate (runtime-p-normalize first p) second p)
         (runtime-p-poly-common-divisor-p candidate first second p)))

(defthm runtime-p-poly-common-divisor-p-of-normalize-second
  (equal (runtime-p-poly-common-divisor-p
          candidate first (runtime-p-normalize second p) p)
         (runtime-p-poly-common-divisor-p candidate first second p)))

; This total bridge handles the zero divisor separately and otherwise uses the
; certified associate bridge.  No recursive general-divmod definition is open.
(local
 (defthm runtime-p-poly-monic-normalize-nil-when-normalize-nil
   (implies (equal (runtime-p-normalize g p) nil)
            (equal (runtime-p-poly-monic-normalize g p) nil))
   :hints (("Goal" :in-theory (enable runtime-p-poly-monic-normalize)))))

(defthm runtime-p-remainder-is-monic-remainder-when-prime
  (implies
   (dm::primep (runtime-p-effective-modulus p))
   (equal (runtime-p-remainder f g p)
          (runtime-p-monic-remainder
           f (runtime-p-poly-monic-normalize g p) p)))
  :rule-classes nil
  :hints
  (("Goal" :cases ((consp (runtime-p-normalize g p))))
   ("Subgoal 2"
    :use ((:instance runtime-p-divmod-inactive)
          (:instance runtime-p-monic-divmod-inactive
                     (g (runtime-p-poly-monic-normalize g p)))
          (:instance runtime-p-normalize-equal-nil-when-not-consp (xs g))
          (:instance runtime-p-poly-monic-normalize-nil-when-normalize-nil))
    :in-theory (disable runtime-p-remainder runtime-p-monic-remainder
                        runtime-p-normalize runtime-p-poly-monic-normalize))
   ("Subgoal 1"
    :use ((:instance
           runtime-p-remainder-is-monic-remainder-of-poly-monic-normalize))
    :in-theory (theory 'minimal-theory))))

(defthm runtime-p-remainder-zero-dividend-when-prime
  (implies (dm::primep (runtime-p-effective-modulus p))
           (equal (runtime-p-remainder nil divisor p) nil))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-remainder-is-monic-remainder-when-prime)
                 (:instance runtime-p-monic-divmod-inactive (f nil)))
           :in-theory (enable runtime-p-monic-remainder))))

(defthm runtime-p-poly-divides-p-zero-when-prime
  (implies (dm::primep (runtime-p-effective-modulus p))
           (runtime-p-poly-divides-p divisor nil p))
  :hints (("Goal" :use runtime-p-remainder-zero-dividend-when-prime
           :in-theory (enable runtime-p-poly-divides-p))))
