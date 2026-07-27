(in-package "GPOLY")
(include-book "quotient-equivalence")

; The multiplicative identity varies with the total modulus semantics.  Unlike
; zero (which is already canonically NIL), this deserves a public name.
(defun poly-reduced-one (modulus)
  (poly-remainder (polynomial-one) modulus))

(defthm poly-reduced-one-definition
  (equal (poly-reduced-one modulus)
         (poly-remainder (polynomial-one) modulus))
  :hints (("Goal" :in-theory (enable poly-reduced-one))))

(local (in-theory (disable poly-reduced-one poly-remainder poly-divmod
                           polynomial-one normalize)))

(defthm canonical-polynomial-p-of-poly-reduced-one
  (canonical-polynomial-p (poly-reduced-one modulus)))

(defthm normalize-of-poly-reduced-one
  (equal (normalize (poly-reduced-one modulus))
         (poly-reduced-one modulus)))

(defthm poly-remainder-of-poly-reduced-one
  (equal (poly-remainder (poly-reduced-one modulus) modulus)
         (poly-reduced-one modulus)))

; NIL is the existing reduced zero.  Reduced one is defined through the same
; remainder fixer, so both carrier facts are unconditional even for the total
; zero- and constant-modulus cases.
(defthm poly-reduced-p-of-nil
  (poly-reduced-p nil modulus)
  :hints (("Goal" :use ((:instance poly-reduced-p-definition (polynomial nil))
                 (:instance poly-remainder-zero-dividend))
           :in-theory (disable poly-reduced-p poly-remainder))))

(defthm poly-reduced-p-of-poly-reduced-one
  (poly-reduced-p (poly-reduced-one modulus) modulus)
  :hints (("Goal" :use ((:instance poly-reduced-p-definition
                            (polynomial (poly-reduced-one modulus)))
                 (:instance poly-remainder-of-poly-reduced-one))
           :in-theory (disable poly-reduced-p poly-remainder))))

(defthm poly-reduced-one-zero-modulus
  (equal (poly-reduced-one nil) (polynomial-one))
  :hints (("Goal"
           :use ((:instance normalize-when-canonical
                            (xs (polynomial-one)))))))

(defthm poly-reduced-one-polynomial-one-modulus
  (equal (poly-reduced-one (polynomial-one)) nil))

(defthm poly-reduced-one-nonzero-constant-modulus
  (implies (and (consp (normalize modulus))
                (equal (poly-degree (normalize modulus)) 0))
           (equal (poly-reduced-one modulus) nil)))

(defthm poly-reduced-one-positive-degree-modulus
  (implies (and (consp (normalize modulus))
                (< 0 (poly-degree (normalize modulus))))
           (equal (poly-reduced-one modulus) (polynomial-one)))
  :hints (("Goal"
           :use ((:instance poly-remainder-of-polynomial-one-when-positive-degree)))))

(verify-guards poly-reduced-one)

(local (in-theory (disable poly-reduced-add poly-reduced-neg
                           poly-reduced-sub poly-reduced-mul
                           poly-add poly-neg poly-sub poly-mul raw-add
                           raw-add-commutative)))

; All operands below are arbitrary ACL2 objects.  Identity conclusions name
; their canonical representative rather than the possibly noncanonical input.
(defthm poly-reduced-add-commutative
  (equal (poly-reduced-add a b modulus)
         (poly-reduced-add b a modulus))
  :hints (("Goal" :use ((:instance poly-add-commutative (x a) (y b))))))

(defthm poly-reduced-add-associative
  (equal (poly-reduced-add (poly-reduced-add a b modulus) c modulus)
         (poly-reduced-add a (poly-reduced-add b c modulus) modulus))
  :hints
  (("Goal"
    :use ((:instance poly-remainder-of-poly-add-remainder-left
                     (left (poly-add a b)) (right c))
          (:instance poly-remainder-of-poly-add-remainder-right
                     (left a) (right (poly-add b c)))
          (:instance poly-add-associative-total
                     (x a) (y b) (z c))))))

(defthm poly-reduced-add-zero-left
  (equal (poly-reduced-add nil a modulus)
         (poly-remainder a modulus)))

(defthm poly-reduced-add-zero-right
  (equal (poly-reduced-add a nil modulus)
         (poly-remainder a modulus)))

(defthm poly-reduced-add-inverse-left
  (equal (poly-reduced-add (poly-reduced-neg a modulus) a modulus) nil)
  :hints (("Goal"
           :use ((:instance poly-remainder-of-poly-add-remainder-left
                            (left (poly-neg a)) (right a))
                 (:instance poly-add-inverse-left-total (x a))))))

(defthm poly-reduced-add-inverse-right
  (equal (poly-reduced-add a (poly-reduced-neg a modulus) modulus) nil)
  :hints (("Goal"
           :use ((:instance poly-remainder-of-poly-add-remainder-right
                            (left a) (right (poly-neg a)))
                 (:instance poly-add-inverse-right-total (x a))))))

(defthm poly-reduced-neg-double
  (equal (poly-reduced-neg (poly-reduced-neg a modulus) modulus)
         (poly-remainder a modulus))
  :hints (("Goal"
           :use ((:instance poly-remainder-of-poly-neg-remainder
                            (polynomial (poly-neg a)))
                 (:instance poly-neg-of-poly-neg-total (x a))))))

(defthm poly-reduced-neg-zero
  (equal (poly-reduced-neg nil modulus) nil))

(defthm poly-reduced-sub-as-add-neg
  (equal (poly-reduced-sub a b modulus)
         (poly-reduced-add a (poly-reduced-neg b modulus) modulus))
  :hints (("Goal"
           :use ((:instance poly-remainder-of-poly-add-remainder-right
                            (left a) (right (poly-neg b)))))))

(defthm poly-reduced-sub-self
  (equal (poly-reduced-sub a a modulus) nil)
  :hints (("Goal" :use ((:instance poly-sub-self-total (x a))))))

(defthm poly-reduced-sub-zero-right
  (equal (poly-reduced-sub a nil modulus)
         (poly-remainder a modulus)))

(defthm poly-reduced-sub-zero-left
  (equal (poly-reduced-sub nil a modulus)
         (poly-reduced-neg a modulus)))

(defthm poly-reduced-mul-commutative
  (equal (poly-reduced-mul a b modulus)
         (poly-reduced-mul b a modulus))
  :hints (("Goal" :use ((:instance poly-mul-commutative (x a) (y b))))))

(defthm poly-reduced-mul-associative
  (equal (poly-reduced-mul (poly-reduced-mul a b modulus) c modulus)
         (poly-reduced-mul a (poly-reduced-mul b c modulus) modulus))
  :hints (("Goal"
           :use ((:instance poly-remainder-of-poly-mul-remainder-left
                            (left (poly-mul a b)) (right c))
                 (:instance poly-remainder-of-poly-mul-remainder-right
                            (left a) (right (poly-mul b c)))
                 (:instance poly-mul-associative (x a) (y b) (z c))))))

(defthm poly-reduced-mul-zero-left
  (equal (poly-reduced-mul nil a modulus) nil))

(defthm poly-reduced-mul-zero-right
  (equal (poly-reduced-mul a nil modulus) nil))

(defthm poly-reduced-mul-one-left
  (equal (poly-reduced-mul (poly-reduced-one modulus) a modulus)
         (poly-remainder a modulus))
  :hints (("Goal"
           :use ((:instance poly-remainder-of-poly-mul-remainder-left
                            (left (polynomial-one)) (right a))
                 (:instance poly-mul-of-polynomial-one-left (x a))))))

(defthm poly-reduced-mul-one-right
  (equal (poly-reduced-mul a (poly-reduced-one modulus) modulus)
         (poly-remainder a modulus))
  :hints (("Goal"
           :use ((:instance poly-remainder-of-poly-mul-remainder-right
                            (left a) (right (polynomial-one)))
                 (:instance poly-mul-of-polynomial-one-right (x a))))))

(defthm poly-reduced-mul-left-distributive
  (equal (poly-reduced-mul a (poly-reduced-add b c modulus) modulus)
         (poly-reduced-add (poly-reduced-mul a b modulus)
                           (poly-reduced-mul a c modulus) modulus))
  :hints (("Goal"
           :use ((:instance poly-remainder-of-poly-mul-remainder-right
                            (left a) (right (poly-add b c)))
                 (:instance poly-remainder-of-poly-add-remainders
                            (left (poly-mul a b)) (right (poly-mul a c)))
                 (:instance poly-mul-left-distributive
                            (x a) (y b) (z c))))))

(defthm poly-reduced-mul-right-distributive
  (equal (poly-reduced-mul (poly-reduced-add a b modulus) c modulus)
         (poly-reduced-add (poly-reduced-mul a c modulus)
                           (poly-reduced-mul b c modulus) modulus))
  :hints (("Goal"
           :use ((:instance poly-remainder-of-poly-mul-remainder-left
                            (left (poly-add a b)) (right c))
                 (:instance poly-remainder-of-poly-add-remainders
                            (left (poly-mul a c)) (right (poly-mul b c)))
                 (:instance poly-mul-right-distributive
                            (x a) (y b) (z c))))))

(defthm poly-reduced-mul-neg-left
  (equal (poly-reduced-mul (poly-reduced-neg a modulus) b modulus)
         (poly-reduced-neg (poly-reduced-mul a b modulus) modulus))
  :hints (("Goal"
           :use ((:instance poly-remainder-of-poly-mul-remainder-left
                            (left (poly-neg a)) (right b))
                 (:instance poly-remainder-of-poly-neg-remainder
                            (polynomial (poly-mul a b)))
                 (:instance poly-mul-of-poly-neg-left-total (x a) (y b))))))

; Focused literal-identity conveniences for already fixed representatives.
(defthm poly-reduced-add-zero-right-when-remainder-fixed
  (implies (equal (poly-remainder a modulus) a)
           (equal (poly-reduced-add a nil modulus) a)))

(defthm poly-reduced-mul-one-right-when-remainder-fixed
  (implies (equal (poly-remainder a modulus) a)
           (equal (poly-reduced-mul a (poly-reduced-one modulus) modulus) a))
  :hints (("Goal" :use ((:instance poly-reduced-mul-one-right)))))
