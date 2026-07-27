(in-package "GPOLY")
(include-book "f7-division")

; This is the presentation-specific carrier F7[x]/(x^2+1), not an abstract
; implementation of every field of order 49.  Reduction is the sole fixer.
(defun f7x2-fix (x)
  (f7-poly-remainder x '(1 0 1)))

(defun f7x2-element-p (x)
  (equal (f7x2-fix x) x))

; Nullary carrier constants follow the GFIELD and concrete F7 interfaces.
; Dense-polynomial normalization represents zero by NIL and one by the
; singleton containing the concrete coefficient-field one.
(defun f7x2-zero () nil)

(defun f7x2-one () (list (gfield::f7-one)))

(verify-guards f7x2-fix)
(verify-guards f7x2-element-p)
(verify-guards f7x2-zero)
(verify-guards f7x2-one)

; The concrete division book already certifies canonical output and its final
; degree bound.  These small local bridges specialize those facts to the sole
; modulus without introducing another reduction algorithm.
(local
 (defthm f7x2-normalize-of-remainder
   (equal (f7-normalize (f7-poly-remainder dividend modulus))
          (f7-poly-remainder dividend modulus))
   :hints (("Goal"
            :use ((:instance f7-poly-remainder-canonical (f dividend) (g modulus))
                  (:instance f7-normalize-when-canonical
                             (xs (f7-poly-remainder dividend modulus))))
            :in-theory (disable f7-poly-remainder f7-normalize
                                f7-canonical-polynomial-p)))))

(local
 (defthm f7x2-remainder-strict-degree-bound
   (implies (consp (f7-normalize modulus))
            (or (equal (f7-poly-remainder dividend modulus) nil)
                (< (f7-poly-degree (f7-poly-remainder dividend modulus))
                   (f7-poly-degree (f7-normalize modulus)))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7-poly-divmod-final-remainder-degree-bound
                             (f dividend) (g modulus))
                  (:instance f7-poly-remainder-is-divmod-remainder
                             (f dividend) (g modulus)))
            :in-theory (disable f7-poly-remainder f7-poly-divmod
                                f7-poly-degree f7-normalize)))))

(local
 (defthm f7x2-remainder-canonical-lower-degree
   (implies (and (f7-canonical-polynomial-p dividend)
                 (consp (f7-normalize modulus))
                 (< (f7-poly-degree dividend)
                    (f7-poly-degree (f7-normalize modulus))))
            (equal (f7-poly-remainder dividend modulus) dividend))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable f7-poly-remainder f7-poly-divmod
                               f7-poly-divmod-core
                               f7-canonical-polynomial-p)))))

(local (defthm f7x2-modulus-normalized
         (equal (f7-normalize '(1 0 1)) '(1 0 1))))
(local (defthm f7x2-modulus-degree
         (equal (f7-poly-degree '(1 0 1)) 2)))

(local
 (defthm f7x2-remainder-idempotent
   (equal (f7-poly-remainder
           (f7-poly-remainder dividend '(1 0 1)) '(1 0 1))
          (f7-poly-remainder dividend '(1 0 1)))
   :hints (("Goal"
            :use ((:instance f7x2-modulus-normalized)
                  (:instance f7x2-modulus-degree)
                  (:instance f7x2-remainder-strict-degree-bound
                             (modulus '(1 0 1)))
                  (:instance f7-poly-remainder-canonical
                             (f dividend) (g '(1 0 1)))
                  (:instance f7-poly-remainder-zero-dividend
                             (modulus '(1 0 1)))
                  (:instance f7-canonical-polynomial-atom-is-nil
                             (polynomial
                              (f7-poly-remainder dividend '(1 0 1))))
                  (:instance f7x2-remainder-canonical-lower-degree
                             (dividend (f7-poly-remainder dividend '(1 0 1)))
                             (modulus '(1 0 1))))
            :in-theory (theory 'minimal-theory)))))

(defthm f7x2-fix-idempotent
  (equal (f7x2-fix (f7x2-fix x)) (f7x2-fix x))
  :hints (("Goal" :use ((:instance f7x2-remainder-idempotent (dividend x)))
           :in-theory (enable f7x2-fix))))

(defthm f7x2-element-p-of-f7x2-fix
  (f7x2-element-p (f7x2-fix x))
  :hints (("Goal" :use ((:instance f7x2-fix-idempotent))
           :in-theory (e/d (f7x2-element-p) (f7x2-fix)))))

(defthm f7x2-fix-when-f7x2-element-p
  (implies (f7x2-element-p x)
           (equal (f7x2-fix x) x))
  :hints (("Goal" :in-theory (enable f7x2-element-p))))

(defthm f7x2-element-p-iff-fix-equal
  (equal (f7x2-element-p x) (equal (f7x2-fix x) x))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable f7x2-element-p))))

(defthm booleanp-of-f7x2-element-p
  (booleanp (f7x2-element-p x))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable f7x2-element-p))))

(defthm f7x2-fix-normalized
  (equal (f7-normalize (f7x2-fix x)) (f7x2-fix x))
  :hints (("Goal" :use ((:instance f7x2-normalize-of-remainder
                                   (dividend x) (modulus '(1 0 1))))
           :in-theory (enable f7x2-fix))))

(local
 (defthm f7x2-fix-canonical
   (f7-canonical-polynomial-p (f7x2-fix x))
   :hints (("Goal" :use ((:instance f7-poly-remainder-canonical
                                    (f x) (g '(1 0 1))))
            :in-theory (enable f7x2-fix)))))

(defthm f7x2-fix-degree-below-two
  (< (f7-poly-degree (f7x2-fix x)) 2)
  :rule-classes (:rewrite :linear)
  :hints (("Goal"
           :use ((:instance f7x2-remainder-strict-degree-bound
                            (dividend x) (modulus '(1 0 1))))
           :in-theory (enable f7x2-fix f7-poly-degree
                              f7-normalize f7-fix-coefficients
                              f7-trim-trailing-zeros))))

(defthm f7x2-element-p-characterization
  (equal (f7x2-element-p x)
         (and (equal x (f7-normalize x))
              (< (f7-poly-degree x) 2)))
  :rule-classes nil
  :hints (("Goal" :cases ((f7x2-element-p x)))
          ("Subgoal 1"
           :use ((:instance f7x2-fix-normalized)
                 (:instance f7x2-fix-degree-below-two))
           :in-theory (enable f7x2-element-p))
          ("Subgoal 2"
           :use ((:instance f7x2-remainder-canonical-lower-degree
                            (dividend x) (modulus '(1 0 1))))
           :in-theory (enable f7x2-element-p f7x2-fix
                              f7-canonical-polynomial-p))))

; Coefficient projections first fix their arbitrary input, so they are stable
; on every ACL2 object rather than merely guarded canonical lists.
(defun f7x2-constant-coefficient (x)
  (gfield::f7-fix (car (f7x2-fix x))))

(defun f7x2-linear-coefficient (x)
  (gfield::f7-fix (cadr (f7x2-fix x))))

(defthm f7-element-p-of-f7x2-constant-coefficient
  (gfield::f7-element-p (f7x2-constant-coefficient x))
  :hints (("Goal" :in-theory (enable f7x2-constant-coefficient))))

(defthm f7-element-p-of-f7x2-linear-coefficient
  (gfield::f7-element-p (f7x2-linear-coefficient x))
  :hints (("Goal" :in-theory (enable f7x2-linear-coefficient))))

; Canonical zero/one interface.  Each rewrite strictly removes either the
; outer carrier fixer or a projection; none expands polynomial arithmetic.
(defthm f7x2-fix-of-zero
  (equal (f7x2-fix (f7x2-zero)) (f7x2-zero))
  :hints (("Goal" :in-theory (enable f7x2-zero f7x2-fix))))

(defthm f7x2-fix-of-one
  (equal (f7x2-fix (f7x2-one)) (f7x2-one))
  :hints (("Goal" :in-theory (enable f7x2-one f7x2-fix))))

(defthm f7x2-element-p-of-zero
  (f7x2-element-p (f7x2-zero))
  :hints (("Goal" :in-theory (e/d (f7x2-element-p)
                                    (f7x2-zero f7x2-fix)))))

(defthm f7x2-element-p-of-one
  (f7x2-element-p (f7x2-one))
  :hints (("Goal" :in-theory (e/d (f7x2-element-p)
                                    (f7x2-one f7x2-fix)))))

(defthm f7x2-constant-coefficient-of-zero
  (equal (f7x2-constant-coefficient (f7x2-zero))
         (gfield::f7-zero))
  :hints (("Goal" :in-theory (enable f7x2-constant-coefficient
                                     f7x2-zero gfield::f7-zero))))

(defthm f7x2-linear-coefficient-of-zero
  (equal (f7x2-linear-coefficient (f7x2-zero))
         (gfield::f7-zero))
  :hints (("Goal" :in-theory (enable f7x2-linear-coefficient
                                     f7x2-zero gfield::f7-zero))))

(defthm f7x2-constant-coefficient-of-one
  (equal (f7x2-constant-coefficient (f7x2-one))
         (gfield::f7-one))
  :hints (("Goal" :in-theory (enable f7x2-constant-coefficient
                                     f7x2-one gfield::f7-one))))

(defthm f7x2-zero-not-equal-f7x2-one
  (not (equal (f7x2-zero)
              (f7x2-one)))
  :hints (("Goal"
           :use ((:instance f7x2-constant-coefficient-of-zero)
                 (:instance f7x2-constant-coefficient-of-one)
                 (:instance gfield::f7-zero-not-equal-f7-one))
           :in-theory nil)))

(local
 (defthm f7x2-zero-not-equal-f7x2-one-regression
   (and (not (equal (f7x2-zero) (f7x2-one)))
        (not (equal (f7x2-one) (f7x2-zero))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7x2-zero-not-equal-f7x2-one))
            :in-theory (disable f7x2-zero-not-equal-f7x2-one
                                f7x2-zero f7x2-one)))))

(defthm f7x2-linear-coefficient-of-one
  (equal (f7x2-linear-coefficient (f7x2-one))
         (gfield::f7-zero))
  :hints (("Goal" :in-theory (enable f7x2-linear-coefficient
                                     f7x2-one gfield::f7-zero))))

(defthm f7x2-constant-coefficient-of-fix
  (equal (f7x2-constant-coefficient (f7x2-fix x))
         (f7x2-constant-coefficient x))
  :hints (("Goal" :use ((:instance f7x2-fix-idempotent))
           :in-theory (e/d (f7x2-constant-coefficient) (f7x2-fix)))))

(defthm f7x2-linear-coefficient-of-fix
  (equal (f7x2-linear-coefficient (f7x2-fix x))
         (f7x2-linear-coefficient x))
  :hints (("Goal" :use ((:instance f7x2-fix-idempotent))
           :in-theory (e/d (f7x2-linear-coefficient) (f7x2-fix)))))

(defthm len-of-f7x2-fix
  (<= (len (f7x2-fix x)) 2)
  :rule-classes :linear
  :hints (("Goal"
           :use ((:instance f7x2-fix-degree-below-two)
                 (:instance f7-poly-degree-semantics-from-pfield
                            (poly (f7x2-fix x))))
           :in-theory (disable f7x2-fix f7-poly-degree f7-normalize))))

; An explicit three-coefficient presentation is fixed coefficientwise before
; the public remainder calculation.  Splitting only on the fixed leading
; coefficient isolates the degree-two division case from trailing-zero
; normalization.
(local
 (defthm f7-normalize-of-three-fixed-coefficients
   (equal (f7-normalize (list a b c))
          (if (equal (gfield::f7-fix c) 0)
              (f7-normalize (list (gfield::f7-fix a)
                                  (gfield::f7-fix b)))
            (list (gfield::f7-fix a)
                  (gfield::f7-fix b)
                  (gfield::f7-fix c))))
   :hints (("Goal" :in-theory (enable f7-normalize f7-fix-coefficients
                                        f7-trim-trailing-zeros)))))

(local
 (defthm f7x2-remainder-of-normalized-two-fixed-coefficients
   (equal (f7-poly-remainder
           (f7-normalize (list (gfield::f7-fix a) (gfield::f7-fix b)))
           '(1 0 1))
          (f7-normalize (list (gfield::f7-fix a) (gfield::f7-fix b))))
   :hints
   (("Goal"
     :use ((:instance f7x2-remainder-canonical-lower-degree
                      (dividend
                       (f7-normalize
                        (list (gfield::f7-fix a) (gfield::f7-fix b))))
                      (modulus '(1 0 1))))
     :in-theory (enable f7-canonical-polynomial-p f7-poly-degree
                        f7-normalize f7-fix-coefficients
                        f7-trim-trailing-zeros)))))

(local
 (defthm f7-poly-remainder-to-normalize-dividend
   (equal (f7-poly-remainder f g)
          (f7-poly-remainder (f7-normalize f) g))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7-poly-remainder-of-normalize-dividend))
            :in-theory
            (disable f7-poly-remainder-of-normalize-dividend
                     f7-poly-remainder f7-poly-divmod
                     f7-poly-divmod-core f7-poly-division-step-core
                     f7-poly-division-step)))))

(defthm f7x2-fix-of-three-coefficients
  (equal (f7x2-fix (list a b c))
         (f7-normalize
          (list (gfield::f7-sub (gfield::f7-fix a)
                                (gfield::f7-fix c))
                (gfield::f7-fix b))))
  :rule-classes nil
  :hints
  (("Goal"
    :cases ((equal (gfield::f7-fix c) 0))
    :use ((:instance f7-poly-remainder-to-normalize-dividend
                     (f (list a b c)) (g '(1 0 1)))
          (:instance f7-normalize-of-three-fixed-coefficients)
          (:instance f7x2-remainder-of-normalized-two-fixed-coefficients))
    :in-theory
    (e/d (f7x2-fix gfield::f7-sub)
         (f7-poly-divmod f7-poly-divmod-core
                         f7-poly-division-step-core
                         f7-poly-division-step
                         f7-poly-remainder-of-normalize-dividend
                         f7-normalize f7-fix-coefficients
                         f7-trim-trailing-zeros)))
   ("Subgoal 2"
    :use ((:instance f7-poly-remainder-degree-two-by-x2-plus-one
                     (a (gfield::f7-fix a))
                     (b (gfield::f7-fix b))
                     (c (gfield::f7-fix c)))))))

(local
 (defthm f7x2-fix-of-three-coefficients-rewrite
   (equal (f7x2-fix (list a b c))
          (f7-normalize
           (list (gfield::f7-sub (gfield::f7-fix a)
                                 (gfield::f7-fix c))
                 (gfield::f7-fix b))))
   :hints (("Goal" :use ((:instance f7x2-fix-of-three-coefficients))))))

(local
 (defthm f7-fix-of-f7-sub
   (equal (gfield::f7-fix (gfield::f7-sub x y))
          (gfield::f7-sub x y))
   :hints (("Goal" :in-theory (enable gfield::f7-sub gfield::f7-add
                                       gfield::f7-neg gfield::f7-fix)))))

(local
 (defthm f7-fix-idempotent-for-f7x2-three-coefficients
   (equal (gfield::f7-fix (gfield::f7-fix x))
          (gfield::f7-fix x))
   :hints (("Goal"
            :use ((:instance gfield::f7-element-p-of-f7-fix))
            :in-theory (disable gfield::f7-fix
                                gfield::f7-element-p)))))

(local
 (defthm f7-fix-of-car-of-normalize-two
   (equal (gfield::f7-fix (car (f7-normalize (list x y))))
          (gfield::f7-fix x))
   :hints (("Goal"
            :use ((:instance gfield::f7-element-p-of-f7-fix (x x))
                  (:instance gfield::f7-element-p-of-f7-fix (x y)))
            :in-theory (e/d (f7-normalize f7-fix-coefficients
                                           f7-trim-trailing-zeros)
                            (gfield::f7-fix gfield::f7-element-p))))))

(local
 (defthm f7-fix-of-cadr-of-normalize-two
   (equal (gfield::f7-fix (cadr (f7-normalize (list x y))))
          (gfield::f7-fix y))
   :hints (("Goal"
            :use ((:instance gfield::f7-element-p-of-f7-fix (x x))
                  (:instance gfield::f7-element-p-of-f7-fix (x y)))
            :in-theory (e/d (f7-normalize f7-fix-coefficients
                                           f7-trim-trailing-zeros)
                            (gfield::f7-fix gfield::f7-element-p))))))

(defthm f7x2-constant-coefficient-of-three-coefficients
  (equal (f7x2-constant-coefficient (list a b c))
         (gfield::f7-sub (gfield::f7-fix a)
                         (gfield::f7-fix c)))
  :hints (("Goal"
           :in-theory
           (e/d (f7x2-constant-coefficient)
                (f7x2-fix f7-poly-remainder f7-poly-divmod
                           f7-poly-divmod-core
                           f7-poly-division-step-core
                           f7-poly-division-step f7-normalize
                           f7-fix-coefficients f7-trim-trailing-zeros)))))

(defthm f7x2-linear-coefficient-of-three-coefficients
  (equal (f7x2-linear-coefficient (list a b c))
         (gfield::f7-fix b))
  :hints (("Goal"
           :in-theory
           (e/d (f7x2-linear-coefficient)
                (f7x2-fix f7-poly-remainder f7-poly-divmod
                           f7-poly-divmod-core
                           f7-poly-division-step-core
                           f7-poly-division-step f7-normalize
                           f7-fix-coefficients f7-trim-trailing-zeros
                           gfield::f7-fix gfield::f7-sub
                           gfield::f7-add gfield::f7-neg)))))

(defthm f7x2-three-coefficient-bridge-regressions
  (and
   (implies (and (gfield::f7-element-p a)
                 (gfield::f7-element-p b))
            (equal (f7x2-fix (list a b 0))
                   (f7-normalize (list a b))))
   (equal (f7x2-fix '(0 0 1)) '(6))
   (equal (f7x2-fix '(1 0 1)) nil)
   (equal (f7x2-fix '(0 1 1)) '(6 1))
   (equal (f7x2-fix '(3 4 3)) '(0 4))
   (equal (f7x2-fix '(10 -3 8)) '(2 4))
   (equal (f7x2-fix '(bad 9 also-bad)) '(0 2))
   (equal (f7x2-fix '(3 4 14)) '(3 4))
   (equal (f7x2-constant-coefficient '(10 -3 8)) 2)
   (equal (f7x2-linear-coefficient '(bad 9 also-bad)) 2)
   (equal (f7x2-constant-coefficient '(3 4 14)) 3)
   (equal (f7x2-linear-coefficient '(3 4 14)) 4))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance f7x2-fix-of-three-coefficients)
                 (:instance f7x2-fix-of-three-coefficients
                            (a 0) (b 0) (c 1))
                 (:instance f7x2-fix-of-three-coefficients
                            (a 1) (b 0) (c 1))
                 (:instance f7x2-fix-of-three-coefficients
                            (a 0) (b 1) (c 1))
                 (:instance f7x2-fix-of-three-coefficients
                            (a 3) (b 4) (c 3))
                 (:instance f7x2-fix-of-three-coefficients
                            (a 10) (b -3) (c 8))
                 (:instance f7x2-fix-of-three-coefficients
                            (a 'bad) (b 9) (c 'also-bad))
                 (:instance f7x2-fix-of-three-coefficients
                            (a 3) (b 4) (c 14)))
           :in-theory (enable f7-normalize f7-fix-coefficients
                              f7-trim-trailing-zeros
                              gfield::f7-element-p gfield::f7-fix
                              gfield::f7-sub gfield::f7-add
                              gfield::f7-neg))))

; Exact executable representation boundary, including total malformed input.

(local
 (defthm f7x2-element-p-implies-normalized
   (implies (f7x2-element-p x)
            (equal (f7-normalize x) x))
   :hints (("Goal" :use ((:instance f7x2-element-p-characterization))
            :in-theory (disable f7x2-fix f7-poly-remainder)))))

(local
 (defthm len-of-f7x2-element-p
   (implies (f7x2-element-p x)
            (<= (len x) 2))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance len-of-f7x2-fix))
            :in-theory (enable f7x2-element-p)))))

(local
 (defthm f7-normalize-reconstruct-short-normalized
   (implies (and (equal (f7-normalize x) x)
                 (<= (len x) 2))
            (equal (f7-normalize (list (gfield::f7-fix (car x))
                                       (gfield::f7-fix (cadr x))))
                   x))
   :hints (("Goal" :cases ((not (consp x))
                           (not (consp (cdr x)))
                           (consp (cddr x)))
            :in-theory (enable f7-normalize f7-fix-coefficients
                               f7-trim-trailing-zeros)))))

(defthm f7x2-reconstruct-from-coefficients
  (implies (f7x2-element-p value)
           (equal (f7-normalize
                   (list (f7x2-constant-coefficient value)
                         (f7x2-linear-coefficient value)))
                  value))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance f7x2-element-p-implies-normalized (x value))
                 (:instance len-of-f7x2-element-p (x value))
                 (:instance f7-normalize-reconstruct-short-normalized
                            (x value)))
           :in-theory (e/d (f7x2-constant-coefficient
                            f7x2-linear-coefficient
                            f7x2-element-p)
                           (f7x2-fix f7-poly-remainder
                                     f7-normalize)))))

(defthm f7x2-coefficient-extensionality
  (implies (and (f7x2-element-p first)
                (f7x2-element-p second)
                (equal (f7x2-constant-coefficient first)
                       (f7x2-constant-coefficient second))
                (equal (f7x2-linear-coefficient first)
                       (f7x2-linear-coefficient second)))
           (equal first second))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance f7x2-reconstruct-from-coefficients
                            (value first))
                 (:instance f7x2-reconstruct-from-coefficients
                            (value second)))
           :in-theory (disable f7x2-fix f7-poly-remainder
                               f7-normalize))))

(defthm f7x2-fix-coefficient-extensionality
  (implies (and (equal (f7x2-constant-coefficient first)
                      (f7x2-constant-coefficient second))
                (equal (f7x2-linear-coefficient first)
                       (f7x2-linear-coefficient second)))
           (equal (f7x2-fix first) (f7x2-fix second)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance f7x2-coefficient-extensionality
                            (first (f7x2-fix first))
                            (second (f7x2-fix second)))
                 (:instance f7x2-element-p-of-f7x2-fix (x first))
                 (:instance f7x2-element-p-of-f7x2-fix (x second)))
           :in-theory (disable f7x2-fix f7-poly-remainder
                               f7x2-element-p-of-f7x2-fix))))

(defthm f7x2-reconstruction-regressions
  (and (equal (f7-normalize
               (list (f7x2-constant-coefficient nil)
                     (f7x2-linear-coefficient nil)))
              nil)
       (equal (f7-normalize
               (list (f7x2-constant-coefficient '(1))
                     (f7x2-linear-coefficient '(1))))
              '(1))
       (equal (f7-normalize
               (list (f7x2-constant-coefficient '(0 1))
                     (f7x2-linear-coefficient '(0 1))))
              '(0 1))
       (equal (f7-normalize
               (list (f7x2-constant-coefficient '(1 1))
                     (f7x2-linear-coefficient '(1 1))))
              '(1 1))
       (implies (and (gfield::f7-element-p a)
                     (not (equal a 0)))
                (equal (f7-normalize
                        (list (f7x2-constant-coefficient (list a))
                              (f7x2-linear-coefficient (list a))))
                       (list a)))
       (implies (and (gfield::f7-element-p a)
                     (gfield::f7-element-p b)
                     (not (equal b 0)))
                (equal (f7-normalize
                        (list (f7x2-constant-coefficient (list a b))
                              (f7x2-linear-coefficient (list a b))))
                       (list a b))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable f7x2-fix f7x2-constant-coefficient
                                     f7x2-linear-coefficient
                                     f7-normalize f7-fix-coefficients
                                     f7-trim-trailing-zeros))))

(defthm f7x2-fix-extensionality-regressions
  (and (equal (f7x2-fix '(1 0)) (f7x2-fix '(1)))
       (equal (f7x2-fix '(8 7)) (f7x2-fix '(1)))
       (equal (f7x2-fix '(1 2 . bad)) (f7x2-fix '(1 2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable f7x2-fix))))

(defthm f7x2-zero-one-interface-regressions
  (and (equal (f7x2-zero) nil)
       (equal (f7x2-one) '(1))
       (equal (f7x2-fix (f7x2-zero)) (f7x2-zero))
       (equal (f7x2-fix (f7x2-one)) (f7x2-one))
       (f7x2-element-p (f7x2-zero))
       (f7x2-element-p (f7x2-one))
       (equal (f7x2-constant-coefficient (f7x2-zero)) 0)
       (equal (f7x2-linear-coefficient (f7x2-zero)) 0)
       (equal (f7x2-constant-coefficient (f7x2-one)) 1)
       (equal (f7x2-linear-coefficient (f7x2-one)) 0)
       (equal (f7x2-fix '(0)) (f7x2-zero))
       (equal (f7x2-fix '(0 0 0)) (f7x2-zero))
       (equal (f7x2-fix '(1 0)) (f7x2-one))
       (equal (f7x2-fix '(1 0 0 0)) (f7x2-one))
       (equal (f7x2-fix '(8 7)) (f7x2-one))
       (equal (f7-normalize
               (list (f7x2-constant-coefficient (f7x2-zero))
                     (f7x2-linear-coefficient (f7x2-zero))))
              (f7x2-zero))
       (equal (f7-normalize
               (list (f7x2-constant-coefficient (f7x2-one))
                     (f7x2-linear-coefficient (f7x2-one))))
              (f7x2-one)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance f7x2-reconstruct-from-coefficients
                            (value (f7x2-zero)))
                 (:instance f7x2-reconstruct-from-coefficients
                            (value (f7x2-one))))
           :in-theory (enable f7x2-zero f7x2-one f7x2-fix))))

(defthm f7x2-representation-regressions
  (and (equal (f7x2-fix nil) nil)
       (equal (f7x2-fix '(1)) '(1))
       (equal (f7x2-fix '(0 1)) '(0 1))
       (equal (f7x2-fix '(1 1)) '(1 1))
       (equal (f7x2-fix '(1 0 1)) nil)
       (equal (f7x2-fix '(1 0 1 0)) nil)
       (equal (f7x2-fix '(8)) '(1))
       (equal (f7x2-fix '(1 7)) '(1))
       (equal (f7x2-fix '(8 -1)) '(1 6))
       (equal (f7x2-fix '(1 2 . bad)) '(1 2))
       (equal (f7x2-fix 'bad) nil)
       (equal (f7x2-fix '(0 0 0 1)) '(0 6)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable f7x2-fix))))

(defthm f7x2-modulus-boundary
  (and (equal (f7x2-fix '(1 0 1)) nil)
       (equal (f7x2-fix '(1 0 1 0)) nil)
       (equal (f7x2-fix '(8 7 8)) nil)
       (not (f7x2-element-p '(1 0 1))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable f7x2-element-p f7x2-fix))))
