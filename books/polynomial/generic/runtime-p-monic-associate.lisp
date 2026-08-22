(in-package "GPOLY")

(include-book "runtime-p-divmod")
(include-book "runtime-p-monic-remainder-coset")

; A transparent total associate operation.  Over a prime effective modulus its
; nonzero result is monic; composites retain the total coefficient-inverse
; behavior without a field claim.
(defun runtime-p-poly-monic-normalize (g p)
  (declare (xargs :guard t))
  (let ((g (runtime-p-normalize g p)))
    (runtime-p-poly-scale
     (runtime-p-inv (runtime-p-poly-leading-coefficient g p) p)
     g p)))

(verify-guards runtime-p-poly-monic-normalize)

(defthm runtime-p-poly-monic-normalize-equation
  (equal (runtime-p-poly-monic-normalize g p)
         (runtime-p-poly-scale
          (runtime-p-inv
           (runtime-p-poly-leading-coefficient
            (runtime-p-normalize g p) p) p)
          (runtime-p-normalize g p) p))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-p-poly-monic-normalize))))

(defthm runtime-p-poly-monic-normalize-of-normalize
  (equal (runtime-p-poly-monic-normalize (runtime-p-normalize g p) p)
         (runtime-p-poly-monic-normalize g p))
  :hints (("Goal" :in-theory (enable runtime-p-poly-monic-normalize))))

(defthm runtime-p-canonical-polynomial-p-of-poly-monic-normalize
  (runtime-p-canonical-polynomial-p
   (runtime-p-poly-monic-normalize g p) p)
  :hints (("Goal" :in-theory (enable runtime-p-poly-monic-normalize))))

(defthm runtime-p-normalize-of-poly-monic-normalize
  (equal (runtime-p-normalize (runtime-p-poly-monic-normalize g p) p)
         (runtime-p-poly-monic-normalize g p))
  :hints (("Goal"
           :use ((:instance runtime-p-normalize-when-canonical
                            (xs (runtime-p-poly-monic-normalize g p)))
                 (:instance runtime-p-canonical-polynomial-p-of-poly-monic-normalize))
           :in-theory (disable runtime-p-normalize
                               runtime-p-poly-monic-normalize))))

(defthm runtime-p-poly-monic-normalize-of-zero
  (equal (runtime-p-poly-monic-normalize nil p) nil)
  :hints (("Goal" :in-theory (enable runtime-p-poly-monic-normalize))))

(local
 (defthm runtime-p-raw-scale-nested-local
   (equal (runtime-p-raw-scale a (runtime-p-raw-scale b x p) p)
          (runtime-p-raw-scale (runtime-p-mul a b p) x p))
   :hints (("Goal" :induct (runtime-p-raw-scale b x p)
            :in-theory (enable runtime-p-raw-scale))
           (and stable-under-simplificationp
                '(:use ((:instance runtime-p-mul-associative
                                  (x a) (y b) (z (car x)))))))))

(local
 (defthm runtime-p-normalize-raw-scale-of-normalize-local
   (equal
    (runtime-p-normalize
     (runtime-p-raw-scale a (runtime-p-normalize x p) p) p)
    (runtime-p-normalize (runtime-p-raw-scale a x p) p))
   :hints (("Goal" :induct (runtime-p-raw-scale a x p)))))

(defthm runtime-p-poly-scale-nested
  (equal (runtime-p-poly-scale a (runtime-p-poly-scale b x p) p)
         (runtime-p-poly-scale (runtime-p-mul a b p) x p))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-raw-scale-nested-local
                            (x (runtime-p-normalize x p)))
                 (:instance runtime-p-poly-scale-of-normalize
                            (a a)
                            (x (runtime-p-raw-scale
                                b (runtime-p-normalize x p) p)))
                 (:instance runtime-p-normalize-raw-scale-of-normalize-local
                            (a a)
                            (x (runtime-p-raw-scale
                                b (runtime-p-normalize x p) p))))
           :in-theory (e/d (runtime-p-poly-scale)
                           (runtime-p-normalize
                            runtime-p-raw-scale)))))

(defthm runtime-p-poly-scale-one
  (equal (runtime-p-poly-scale (runtime-p-one p) x p)
         (runtime-p-normalize x p))
  :hints (("Goal" :in-theory (enable runtime-p-poly-scale
                                     runtime-p-polynomial-one))))

(local
 (defthm runtime-p-inverse-leading-coefficient-nonzero-local
   (implies
    (and (dm::primep (runtime-p-effective-modulus p))
         (consp (runtime-p-normalize g p)))
    (not (equal
          (runtime-p-coefficient-fix
           (runtime-p-inv
            (runtime-p-poly-leading-coefficient
             (runtime-p-normalize g p) p) p) p)
          (runtime-p-zero p))))
   :hints
   (("Goal"
     :use ((:instance runtime-p-poly-leading-coefficient-equal-zero
                      (poly g))
           (:instance runtime-p-inv-involution
                      (x (runtime-p-poly-leading-coefficient g p)))
           (:instance runtime-p-inv-of-zero)
           (:instance runtime-p-coefficient-p-of-poly-leading-coefficient
                      (poly g))
           (:instance runtime-p-coefficient-fix-when-recognized
                      (x (runtime-p-poly-leading-coefficient g p))))
     :in-theory (disable runtime-p-normalize runtime-p-inv
                         runtime-p-poly-leading-coefficient)))))

(defthm runtime-p-poly-scale-monic-normalize-by-leading-coefficient
  (implies
   (and (dm::primep (runtime-p-effective-modulus p))
        (consp (runtime-p-normalize g p)))
   (equal
    (runtime-p-poly-scale
     (runtime-p-poly-leading-coefficient (runtime-p-normalize g p) p)
     (runtime-p-poly-monic-normalize g p) p)
    (runtime-p-normalize g p)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance runtime-p-poly-scale-nested
                     (a (runtime-p-poly-leading-coefficient
                         (runtime-p-normalize g p) p))
                     (b (runtime-p-inv
                         (runtime-p-poly-leading-coefficient
                          (runtime-p-normalize g p) p) p))
                     (x (runtime-p-normalize g p)))
          (:instance runtime-p-mul-inv-right
                     (x (runtime-p-poly-leading-coefficient
                         (runtime-p-normalize g p) p)))
          (:instance runtime-p-poly-leading-coefficient-equal-zero
                     (poly g))
          (:instance runtime-p-coefficient-p-of-poly-leading-coefficient
                     (poly g))
          (:instance runtime-p-coefficient-fix-when-recognized
                     (x (runtime-p-poly-leading-coefficient g p)))
          (:instance runtime-p-poly-scale-one
                     (x (runtime-p-normalize g p))))
    :in-theory (e/d (runtime-p-poly-monic-normalize)
                    (runtime-p-poly-scale runtime-p-normalize
                     runtime-p-poly-leading-coefficient
                     runtime-p-poly-leading-coefficient-when-canonical-nonzero)))))

(defthm runtime-p-consp-of-poly-monic-normalize-when-prime
  (implies
   (and (dm::primep (runtime-p-effective-modulus p))
        (consp (runtime-p-normalize g p)))
   (consp (runtime-p-poly-monic-normalize g p)))
  :rule-classes nil
  :hints
  (("Goal"
    :cases ((consp (runtime-p-poly-monic-normalize g p)))
    :use ((:instance
           runtime-p-poly-scale-monic-normalize-by-leading-coefficient)
          (:instance runtime-p-normalize-equal-nil-when-not-consp
                     (xs (runtime-p-poly-monic-normalize g p))))
    :in-theory (e/d (runtime-p-poly-scale runtime-p-raw-scale)
                    (runtime-p-poly-monic-normalize runtime-p-normalize)))))

(local
 (defthm runtime-p-last-of-raw-scale-local
   (implies (consp x)
            (equal (car (last (runtime-p-raw-scale a x p)))
                   (runtime-p-mul a (car (last x)) p)))
   :hints (("Goal" :induct (runtime-p-raw-scale a x p)
            :in-theory (enable runtime-p-raw-scale)))))

(local
 (defthm runtime-p-len-of-raw-scale-local
   (equal (len (runtime-p-raw-scale a x p)) (len x))
   :hints (("Goal" :induct (runtime-p-raw-scale a x p)
            :in-theory (enable runtime-p-raw-scale)))))

(local
 (defthm runtime-p-consp-of-raw-scale-local
   (equal (consp (runtime-p-raw-scale a x p)) (consp x))
   :hints (("Goal" :in-theory (enable runtime-p-raw-scale)))))

(local
 (defthm runtime-p-raw-scale-nonempty-local
   (implies (consp x) (consp (runtime-p-raw-scale a x p)))
   :hints (("Goal" :in-theory (enable runtime-p-raw-scale)))))

(local
 (defthm runtime-p-coefficient-list-p-of-raw-scale-local
   (runtime-p-coefficient-list-p (runtime-p-raw-scale a x p) p)
   :hints (("Goal" :induct (runtime-p-raw-scale a x p)
            :in-theory (enable runtime-p-raw-scale
                               runtime-p-coefficient-list-p)))))

(local
 (defthm runtime-p-raw-scale-of-coefficient-fix-local
   (equal (runtime-p-raw-scale (runtime-p-coefficient-fix a p) x p)
          (runtime-p-raw-scale a x p))
   :hints (("Goal" :induct (runtime-p-raw-scale a x p)
            :in-theory (enable runtime-p-raw-scale)))))

(local
 (defthm runtime-p-canonical-of-raw-scale-when-top-nonzero-local
   (implies
    (and (runtime-p-canonical-polynomial-p x p)
         (consp x)
         (not (equal (runtime-p-mul a (car (last x)) p)
                     (runtime-p-zero p))))
    (runtime-p-canonical-polynomial-p (runtime-p-raw-scale a x p) p))
   :hints
   (("Goal"
     :use ((:instance runtime-p-last-of-raw-scale-local))
     :in-theory (enable runtime-p-canonical-polynomial-p
                        runtime-p-raw-scale runtime-p-zero)))))

(local
 (defthm runtime-p-mul-nonzero-when-prime-local
   (implies
    (and (dm::primep (runtime-p-effective-modulus p))
         (not (equal (runtime-p-coefficient-fix a p) (runtime-p-zero p)))
         (not (equal (runtime-p-coefficient-fix b p) (runtime-p-zero p))))
    (not (equal (runtime-p-mul a b p) (runtime-p-zero p))))
   :hints
   (("Goal"
     :use ((:instance runtime-p-mul-inv-left (x a))
           (:instance runtime-p-mul-associative
                      (x (runtime-p-inv a p)) (y a) (z b))
           (:instance runtime-p-mul-zero-right
                      (x (runtime-p-inv a p)))
           (:instance runtime-p-mul-one-left (x b)))
     :in-theory (disable runtime-p-mul runtime-p-inv)))))

(local
 (defthm runtime-p-canonical-last-fixed-nonzero-local
   (implies (and (runtime-p-canonical-polynomial-p x p) (consp x))
            (not (equal (runtime-p-coefficient-fix (car (last x)) p)
                        (runtime-p-zero p))))
   :hints (("Goal"
            :in-theory (enable runtime-p-canonical-polynomial-p
                               runtime-p-coefficient-list-p
                               runtime-p-zero)))))

(local
 (defthm runtime-p-normalize-raw-scale-prime-nonzero-local
   (implies
    (and (dm::primep (runtime-p-effective-modulus p))
         (not (equal (runtime-p-coefficient-fix a p) (runtime-p-zero p)))
         (runtime-p-canonical-polynomial-p x p)
         (consp x))
    (equal (runtime-p-normalize (runtime-p-raw-scale a x p) p)
           (runtime-p-raw-scale a x p)))
   :hints
   (("Goal"
     :use ((:instance runtime-p-canonical-last-fixed-nonzero-local)
           (:instance runtime-p-mul-nonzero-when-prime-local
                      (b (car (last x))))
           (:instance runtime-p-canonical-of-raw-scale-when-top-nonzero-local)
           (:instance runtime-p-normalize-when-canonical
                      (xs (runtime-p-raw-scale a x p))))
     :in-theory (disable runtime-p-normalize runtime-p-raw-scale
                         runtime-p-canonical-polynomial-p runtime-p-mul)))))

(defthm runtime-p-poly-scale-nonzero-prime-properties
  (implies
   (and (dm::primep (runtime-p-effective-modulus p))
        (not (equal (runtime-p-coefficient-fix a p) (runtime-p-zero p)))
        (consp (runtime-p-normalize x p)))
   (and
    (consp (runtime-p-poly-scale a x p))
    (equal (len (runtime-p-poly-scale a x p))
           (len (runtime-p-normalize x p)))
    (equal (runtime-p-poly-leading-coefficient
            (runtime-p-poly-scale a x p) p)
           (runtime-p-mul
            a (runtime-p-poly-leading-coefficient
               (runtime-p-normalize x p) p) p))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance runtime-p-normalize-raw-scale-prime-nonzero-local
                     (x (runtime-p-normalize x p)))
          (:instance runtime-p-len-of-raw-scale-local
                     (x (runtime-p-normalize x p)))
          (:instance runtime-p-consp-of-raw-scale-local
                     (x (runtime-p-normalize x p)))
          (:instance runtime-p-raw-scale-nonempty-local
                     (x (runtime-p-normalize x p)))
          (:instance runtime-p-raw-scale-of-coefficient-fix-local
                     (x (runtime-p-normalize x p)))
          (:instance runtime-p-last-of-raw-scale-local
                     (x (runtime-p-normalize x p)))
          (:instance runtime-p-poly-leading-coefficient-when-canonical-nonzero
                     (poly (runtime-p-normalize x p))))
    :in-theory
    (e/d (runtime-p-poly-scale)
         (runtime-p-normalize runtime-p-raw-scale
          runtime-p-poly-leading-coefficient)))))

(defthm runtime-p-poly-monic-normalize-prime-properties
  (implies
   (and (dm::primep (runtime-p-effective-modulus p))
        (consp (runtime-p-normalize g p)))
   (and
    (consp (runtime-p-poly-monic-normalize g p))
    (equal (runtime-p-poly-leading-coefficient
            (runtime-p-poly-monic-normalize g p) p)
           (runtime-p-one p))
    (equal (len (runtime-p-poly-monic-normalize g p))
           (len (runtime-p-normalize g p)))
    (equal (runtime-p-poly-degree
            (runtime-p-poly-monic-normalize g p) p)
           (runtime-p-poly-degree (runtime-p-normalize g p) p))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance runtime-p-inverse-leading-coefficient-nonzero-local)
          (:instance runtime-p-consp-of-poly-monic-normalize-when-prime)
          (:instance runtime-p-normalize-of-poly-monic-normalize)
          (:instance runtime-p-poly-scale-nonzero-prime-properties
                     (a (runtime-p-inv
                         (runtime-p-poly-leading-coefficient
                          (runtime-p-normalize g p) p) p))
                     (x (runtime-p-normalize g p)))
          (:instance runtime-p-mul-inv-left
                     (x (runtime-p-poly-leading-coefficient
                         (runtime-p-normalize g p) p)))
          (:instance runtime-p-poly-leading-coefficient-equal-zero
                     (poly g))
          (:instance runtime-p-coefficient-p-of-poly-leading-coefficient
                     (poly g))
          (:instance runtime-p-coefficient-fix-when-recognized
                     (x (runtime-p-poly-leading-coefficient g p)))
          (:instance runtime-p-poly-degree-when-canonical-nonzero
                     (poly (runtime-p-poly-monic-normalize g p)))
          (:instance runtime-p-poly-degree-when-canonical-nonzero
                     (poly (runtime-p-normalize g p))))
    :in-theory (e/d (runtime-p-poly-monic-normalize)
                    (runtime-p-poly-scale runtime-p-normalize
                     runtime-p-poly-degree
                     runtime-p-poly-leading-coefficient
                     runtime-p-poly-leading-coefficient-when-canonical-nonzero)))))

(defthm runtime-p-poly-leading-coefficient-of-poly-monic-normalize-when-prime
  (implies
   (and (dm::primep (runtime-p-effective-modulus p))
        (consp (runtime-p-normalize g p)))
   (equal (runtime-p-poly-leading-coefficient
           (runtime-p-poly-monic-normalize g p) p)
          (runtime-p-one p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-poly-monic-normalize-prime-properties))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-p-len-of-poly-monic-normalize-when-prime
  (implies
   (and (dm::primep (runtime-p-effective-modulus p))
        (consp (runtime-p-normalize g p)))
   (equal (len (runtime-p-poly-monic-normalize g p))
          (len (runtime-p-normalize g p))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-poly-monic-normalize-prime-properties))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-p-poly-degree-of-poly-monic-normalize-when-prime
  (implies
   (and (dm::primep (runtime-p-effective-modulus p))
        (consp (runtime-p-normalize g p)))
   (equal (runtime-p-poly-degree (runtime-p-poly-monic-normalize g p) p)
          (runtime-p-poly-degree (runtime-p-normalize g p) p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-poly-monic-normalize-prime-properties))
           :in-theory (theory 'minimal-theory))))

(local
 (defun runtime-p-poly-const-for-associate (a p)
   (if (equal (runtime-p-coefficient-fix a p) (runtime-p-zero p))
       nil
     (list (runtime-p-coefficient-fix a p)))))

(local
 (defthm runtime-p-normalize-raw-scale-zero-local
   (equal (runtime-p-normalize (runtime-p-raw-scale 0 x p) p) nil)
   :hints (("Goal" :induct (runtime-p-raw-scale 0 x p)
            :in-theory (enable runtime-p-raw-scale runtime-p-normalize
                               runtime-p-trim-trailing-zeros)))))

(local
 (defthm runtime-p-poly-scale-zero-local
   (equal (runtime-p-poly-scale (runtime-p-zero p) x p) nil)
   :hints (("Goal"
            :use ((:instance runtime-p-normalize-raw-scale-zero-local
                             (x (runtime-p-normalize x p))))
            :in-theory (e/d (runtime-p-poly-scale runtime-p-zero)
                            (runtime-p-normalize runtime-p-raw-scale))))))

(local
 (defthm runtime-p-poly-scale-when-normalize-nil-local
   (implies (not (consp (runtime-p-normalize x p)))
            (equal (runtime-p-poly-scale a x p) nil))
   :hints (("Goal"
            :use ((:instance runtime-p-normalize-equal-nil-when-not-consp
                             (xs x)))
            :in-theory (enable runtime-p-poly-scale runtime-p-raw-scale)))))

(local
 (defthm runtime-p-normalize-raw-add-zero-tail-local
   (implies (runtime-p-coefficient-list-p x p)
            (equal (runtime-p-normalize
                    (runtime-p-raw-add x '(0) p) p)
                   (runtime-p-normalize x p)))
   :hints (("Goal" :induct (runtime-p-raw-add x '(0) p)
            :in-theory (enable runtime-p-raw-add runtime-p-normalize
                               runtime-p-trim-trailing-zeros
                               runtime-p-coefficient-list-p)))))

(local
 (defthm runtime-p-normalize-scaled-zero-tail-local
   (equal
    (runtime-p-normalize
     (runtime-p-raw-add
      (runtime-p-raw-scale (runtime-p-coefficient-fix a p)
                           (runtime-p-normalize x p) p)
      '(0) p) p)
    (runtime-p-poly-scale a x p))
   :hints
   (("Goal"
     :use ((:instance runtime-p-normalize-raw-add-zero-tail-local
                      (x (runtime-p-raw-scale
                          (runtime-p-coefficient-fix a p)
                          (runtime-p-normalize x p) p)))
           (:instance runtime-p-normalize-raw-scale-of-normalize-local
                      (a (runtime-p-coefficient-fix a p)) (x x))
           (:instance runtime-p-raw-scale-of-coefficient-fix-local
                      (x (runtime-p-normalize x p))))
     :in-theory (e/d (runtime-p-poly-scale)
                     (runtime-p-normalize runtime-p-raw-add
                      runtime-p-raw-scale))))))

(local
 (defthm runtime-p-poly-mul-const-left-local
   (equal (runtime-p-poly-mul
           (runtime-p-poly-const-for-associate a p) x p)
          (runtime-p-poly-scale a x p))
   :hints (("Goal"
            :cases ((equal (runtime-p-coefficient-fix a p)
                           (runtime-p-zero p)))
            :use ((:instance runtime-p-normalize-raw-scale-zero-local
                             (x (runtime-p-normalize x p)))
                  (:instance runtime-p-poly-scale-zero-local (x x))
                  (:instance runtime-p-poly-scale-when-normalize-nil-local)
                  (:instance runtime-p-normalize-raw-scale-of-normalize-local
                             (a (runtime-p-coefficient-fix a p)) (x x))
                  (:instance runtime-p-normalize-raw-add-zero-tail-local
                             (x (runtime-p-raw-scale
                                 (runtime-p-coefficient-fix a p)
                                 (runtime-p-normalize x p) p)))
                  (:instance runtime-p-normalize-scaled-zero-tail-local))
            :in-theory (e/d (runtime-p-poly-const-for-associate
                             runtime-p-poly-mul runtime-p-raw-mul)
                            (runtime-p-poly-scale runtime-p-raw-scale
                             runtime-p-normalize runtime-p-raw-add
                             runtime-p-trim-trailing-zeros
                             runtime-p-fix-coefficients))))))

(defthm runtime-p-poly-mul-of-poly-scale-left
  (equal (runtime-p-poly-mul (runtime-p-poly-scale a x p) y p)
         (runtime-p-poly-scale a (runtime-p-poly-mul x y p) p))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance runtime-p-poly-mul-associative
                     (x (runtime-p-poly-const-for-associate a p))
                     (y x) (z y))
          (:instance runtime-p-poly-mul-const-left-local)
          (:instance runtime-p-poly-mul-const-left-local
                     (x (runtime-p-poly-mul x y p))))
    :in-theory (disable runtime-p-poly-mul runtime-p-poly-scale))))

(defthm runtime-p-poly-mul-of-poly-scale-right
  (equal (runtime-p-poly-mul x (runtime-p-poly-scale a y p) p)
         (runtime-p-poly-scale a (runtime-p-poly-mul x y p) p))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance runtime-p-poly-mul-of-poly-scale-left
                     (x y) (y x))
          (:instance runtime-p-poly-mul-commutative
                     (x x) (y (runtime-p-poly-scale a y p)))
          (:instance runtime-p-poly-mul-commutative (x x) (y y)))
    :in-theory (disable runtime-p-poly-mul runtime-p-poly-scale))))

(defthm runtime-p-poly-mul-absorb-divisor-scale
  (equal
   (runtime-p-poly-mul q (runtime-p-poly-scale a g p) p)
   (runtime-p-poly-mul (runtime-p-poly-scale a q p) g p))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance runtime-p-poly-mul-of-poly-scale-right
                     (x q) (y g))
          (:instance runtime-p-poly-mul-of-poly-scale-left
                     (x q) (y g)))
    :in-theory (disable runtime-p-poly-mul runtime-p-poly-scale))))

(local
 (defthm runtime-p-reconstruction-through-monic-associate-local
   (implies
    (and (dm::primep (runtime-p-effective-modulus p))
         (consp (runtime-p-normalize g p)))
    (equal
     (runtime-p-normalize f p)
     (runtime-p-poly-add
      (runtime-p-poly-mul
       (runtime-p-poly-scale
        (runtime-p-poly-leading-coefficient (runtime-p-normalize g p) p)
        (runtime-p-quotient f g p) p)
       (runtime-p-poly-monic-normalize g p) p)
      (runtime-p-remainder f g p) p)))
   :hints
   (("Goal"
     :use ((:instance runtime-p-projection-reconstruction)
           (:instance
            runtime-p-poly-scale-monic-normalize-by-leading-coefficient)
           (:instance runtime-p-poly-mul-absorb-divisor-scale
                      (q (runtime-p-quotient f g p))
                      (a (runtime-p-poly-leading-coefficient
                          (runtime-p-normalize g p) p))
                      (g (runtime-p-poly-monic-normalize g p))))
     :in-theory (disable runtime-p-normalize runtime-p-poly-add
                         runtime-p-poly-mul runtime-p-poly-scale
                         runtime-p-quotient runtime-p-remainder
                         runtime-p-poly-monic-normalize)))))

(defthm runtime-p-remainder-is-monic-remainder-of-poly-monic-normalize
  (implies
   (and (dm::primep (runtime-p-effective-modulus p))
        (consp (runtime-p-normalize g p)))
   (equal
    (runtime-p-remainder f g p)
    (runtime-p-monic-remainder
     f (runtime-p-poly-monic-normalize g p) p)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance runtime-p-reconstruction-through-monic-associate-local)
          (:instance runtime-p-canonical-polynomial-p-of-remainder)
          (:instance runtime-p-remainder-prime-bound)
          (:instance runtime-p-poly-degree-of-poly-monic-normalize-when-prime)
          (:instance runtime-p-consp-of-poly-monic-normalize-when-prime)
          (:instance runtime-p-normalize-of-poly-monic-normalize)
          (:instance
           runtime-p-poly-leading-coefficient-of-poly-monic-normalize-when-prime)
          (:instance runtime-p-monic-remainder-of-bounded-reconstruction
                     (g (runtime-p-poly-monic-normalize g p))
                     (quotient
                      (runtime-p-poly-scale
                       (runtime-p-poly-leading-coefficient
                        (runtime-p-normalize g p) p)
                       (runtime-p-quotient f g p) p))
                     (candidate (runtime-p-remainder f g p))))
    :in-theory (theory 'minimal-theory))))

(defthm runtime-p-remainder-of-poly-monic-normalize
  (implies
   (and (dm::primep (runtime-p-effective-modulus p))
        (consp (runtime-p-normalize g p)))
   (equal
    (runtime-p-remainder f g p)
    (runtime-p-remainder f (runtime-p-poly-monic-normalize g p) p)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance
           runtime-p-remainder-is-monic-remainder-of-poly-monic-normalize)
          (:instance runtime-p-remainder-when-monic
                     (g (runtime-p-poly-monic-normalize g p)))
          (:instance runtime-p-normalize-of-poly-monic-normalize)
          (:instance
           runtime-p-poly-leading-coefficient-of-poly-monic-normalize-when-prime))
    :in-theory (theory 'minimal-theory))))
