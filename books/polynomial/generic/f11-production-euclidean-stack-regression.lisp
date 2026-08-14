(in-package "GPOLY")

(include-book "f11-production-euclidean-stack")

; Aggregate specifications remain usable without unfolding the algorithms.
(defthm f11-raw-gcd-aggregate-minimal-theory-client
  (f11-poly-common-divisor-p
   (f11-poly-euclidean-gcd first second) first second)
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance f11-poly-euclidean-gcd-raw-correct)))))
(defthm f11-monic-gcd-aggregate-minimal-theory-client
  (f11-canonical-polynomial-p
   (f11-poly-monic-euclidean-gcd first second))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance
                  f11-canonical-polynomial-p-of-poly-monic-euclidean-gcd)))))
(defthm f11-raw-xgcd-aggregate-minimal-theory-client
  (equal (mv-nth 0 (f11-poly-extended-euclidean-gcd first second))
         (f11-poly-euclidean-gcd first second))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance
                  f11-poly-extended-euclidean-gcd-raw-specification)))))
(defthm f11-monic-xgcd-aggregate-minimal-theory-client
  (equal (mv-nth 0 (f11-poly-monic-extended-euclidean-gcd first second))
         (f11-poly-monic-euclidean-gcd first second))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance
                  f11-poly-monic-extended-euclidean-gcd-specification)))))
(defthm f11-modular-inverse-aggregate-minimal-theory-client
  (f11-canonical-polynomial-p (f11-poly-modular-inverse first modulus))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance f11-poly-modular-inverse-specification)))))

; Total normalization: atoms and dotted tails are discarded at the production
; normalizer boundary, coefficients are fixed modulo 11, and trailing zeroes
; are removed before monic scaling.
(assert-event (equal (f11-poly-monic-normalize nil) nil))
(assert-event (equal (f11-poly-monic-normalize 'malformed) nil))
(assert-event (equal (f11-poly-monic-normalize '(22 1 . tail)) '(0 1)))
(assert-event (equal (f11-poly-monic-normalize '(1 11 0)) '(1)))
(assert-event (equal (f11-poly-monic-normalize '(21 17 17 0 3))
                     '(7 2 2 0 1)))
(assert-event (equal (f11-poly-monic-normalize '(10 6 6 0 3))
                     '(7 2 2 0 1)))

; Raw XGCD preserves its base coefficient one; monic XGCD applies the common
; inverse-leading-coefficient scale, so the all-zero triple is distinct.
(assert-event
 (mv-let (g s coefficient-t) (f11-poly-extended-euclidean-gcd nil nil)
   (and (equal g nil) (equal s '(1)) (equal coefficient-t nil))))
(assert-event
 (mv-let (g s coefficient-t)
   (f11-poly-monic-extended-euclidean-gcd nil nil)
   (and (equal g nil) (equal s nil) (equal coefficient-t nil))))

; A repeated linear factor and a nontrivial Euclidean chain through the
; intended quartic modulus.
(assert-event (equal (f11-poly-euclidean-gcd '(1 1) '(1 2 1)) '(1 1)))
(assert-event (equal (f11-poly-euclidean-gcd '(10 6 6 0 3) '(0 1)) '(10)))
(assert-event (equal (f11-poly-monic-euclidean-gcd
                      '(10 6 6 0 3) '(0 1))
                     '(1)))
(assert-event
 (mv-let (g s coefficient-t)
   (f11-poly-extended-euclidean-gcd '(10 6 6 0 3) '(0 1))
   (and (equal g '(10)) (equal s '(1))
        (equal coefficient-t '(5 5 0 8)))))
(assert-event (equal (f11-poly-add
                      (f11-poly-mul '(1) '(10 6 6 0 3))
                      (f11-poly-mul '(5 5 0 8) '(0 1)))
                     '(10)))

; ACL2 executes and certifies the inverse of x modulo psi_3.  These calculations
; are concrete implementation coverage, not a quartic irreducibility proof.
(assert-event (equal (f11-poly-monic-euclidean-gcd
                      '(0 1) '(10 6 6 0 3))
                     '(1)))
(assert-event (equal (f11-poly-modular-inverse '(0 1) '(10 6 6 0 3))
                     '(6 6 0 3)))
(assert-event (equal (f11-poly-reduced-mul
                      (f11-poly-modular-inverse '(0 1) '(10 6 6 0 3))
                      '(0 1) '(10 6 6 0 3))
                     '(1)))
(assert-event (equal (f11-poly-reduced-mul
                      '(0 1)
                      (f11-poly-modular-inverse '(0 1) '(10 6 6 0 3))
                      '(10 6 6 0 3))
                     '(1)))

(defthm f11-x-mod-psi3-left-inverse-from-conditional-boundary
  (equal (f11-poly-reduced-mul
          (f11-poly-modular-inverse '(0 1) '(10 6 6 0 3))
          '(0 1) '(10 6 6 0 3))
         (f11-poly-reduced-one '(10 6 6 0 3)))
  :rule-classes nil
  :hints (("Goal" :use
           ((:instance f11-poly-reduced-mul-modular-inverse-left
                       (first '(0 1)) (modulus '(10 6 6 0 3)))))))
(defthm f11-x-mod-psi3-right-inverse-from-conditional-boundary
  (equal (f11-poly-reduced-mul
          '(0 1)
          (f11-poly-modular-inverse '(0 1) '(10 6 6 0 3))
          '(10 6 6 0 3))
         (f11-poly-reduced-one '(10 6 6 0 3)))
  :rule-classes nil
  :hints (("Goal" :use
           ((:instance f11-poly-reduced-mul-modular-inverse-right
                       (first '(0 1)) (modulus '(10 6 6 0 3)))))))

; The candidate remains total for a non-coprime pair; no inverse theorem is
; asserted because the monic-GCD-one hypothesis is false.
(assert-event (equal (f11-poly-monic-euclidean-gcd '(1 1) '(1 2 1)) '(1 1)))
(assert-event (equal (f11-poly-modular-inverse '(1 1) '(1 2 1)) '(1)))
