(in-package "GPOLY")
(include-book "const")

; Natural polynomial powers.  POLY-POW-SPEC is the disabled linear proof
; specification.  POLY-POW executes POLY-POW-FAST, which halves its exponent
; on every call and relies on POLY-MUL for canonicalization.
(gfield::def-pow-instance poly-pow-spec poly-pow-fast poly-pow
  polynomial-one poly-mul normalize)

(defthm canonical-polynomial-p-of-poly-pow
  (canonical-polynomial-p (poly-pow f n))
  :hints (("Goal" :induct (poly-pow-spec (normalize f) n)
           :in-theory (enable poly-pow poly-pow-spec))))

(defthm poly-pow-of-normalize
  (equal (poly-pow (normalize f) n) (poly-pow f n))
  :hints (("Goal" :in-theory (enable poly-pow))))

(defthm poly-pow-of-nfix
  (equal (poly-pow f (nfix n)) (poly-pow f n))
  :hints (("Goal" :in-theory (enable poly-pow))))

(defthm poly-pow-correct
  (equal (poly-pow f n) (poly-pow-spec (normalize f) (nfix n)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable poly-pow))))

(defthm poly-pow-zero
  (equal (poly-pow f 0) (polynomial-one))
  :hints (("Goal" :in-theory (enable poly-pow poly-pow-spec))))

(defthm poly-pow-successor
  (equal (poly-pow f (+ 1 (nfix n)))
         (poly-mul f (poly-pow f n)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable poly-pow poly-pow-spec))))

(defthm poly-pow-one
  (equal (poly-pow f 1) (normalize f))
  :hints (("Goal" :use ((:instance poly-pow-successor (n 0))))))

(defthm poly-pow-of-one
  (equal (poly-pow (polynomial-one) n) (polynomial-one))
  :hints (("Goal" :induct (poly-pow-spec (polynomial-one) n)
           :in-theory (enable poly-pow poly-pow-spec))))

(defthm poly-pow-of-zero-polynomial
  (equal (poly-pow nil n)
         (if (zp n) (polynomial-one) nil))
  :hints (("Goal" :induct (poly-pow-spec nil n)
           :in-theory (enable poly-pow poly-pow-spec))))

; Monoid-only bridge for the executable accumulator.  POLY-MUL-COMMUTATIVE
; has no rewrite rule and is not used by any theorem in this block.
(defthm poly-mul-associate-right-for-power
  (equal (poly-mul (poly-mul a b) c)
         (poly-mul a (poly-mul b c)))
  :hints (("Goal" :use ((:instance poly-mul-associative
                          (x a) (y b) (z c))))))

(defthm poly-pow-spec-successor
  (equal (poly-pow-spec base (+ 1 (nfix n)))
         (poly-mul (normalize base) (poly-pow-spec base n)))
  :hints (("Goal" :in-theory (enable poly-pow-spec))))

(defthm poly-pow-spec-plus-two
  (implies (and (canonical-polynomial-p base)
                (natp n))
           (equal (poly-pow-spec base (+ 2 n))
                  (poly-mul base
                            (poly-mul base (poly-pow-spec base n)))))
  :hints (("Goal" :use ((:instance poly-pow-spec-successor
                          (base base) (n (+ 1 n)))
                          (:instance poly-pow-spec-successor
                           (base base) (n n))))))

(defthm poly-pow-spec-of-square
  (implies (and (canonical-polynomial-p base)
                (natp n))
           (equal (poly-pow-spec (poly-mul base base) n)
                  (poly-pow-spec base (* 2 n))))
  :hints (("Goal" :induct (poly-pow-spec base n)
           :in-theory (e/d (poly-pow-spec poly-pow-spec-plus-two
                                          poly-mul-associate-right-for-power)
                           (poly-mul)))
          ("Subgoal *1/2" :use ((:instance poly-pow-spec-plus-two
                                  (base base)
                                  (n (+ -2 (* 2 n)))))
           :in-theory (disable poly-mul))))

(defthm poly-pow-spec-odd-form
  (implies (and (canonical-polynomial-p base)
                (natp n))
           (equal (poly-pow-spec base (+ 1 (* 2 n)))
                  (poly-mul base (poly-pow-spec base (* 2 n)))))
  :hints (("Goal" :use ((:instance poly-pow-spec-successor
                          (base base) (n (* 2 n)))))))

; Exact invariant:
;   POLY-POW-FAST(acc,base,n) = POLY-MUL(acc,POLY-POW-SPEC(base,n)).
; Canonicality supplies the fixing and identity conditions.  No polynomial
; commutativity theorem is available to this proof.
(defthm poly-pow-fast-accumulator-invariant
  (implies (and (canonical-polynomial-p acc)
                (canonical-polynomial-p base)
                (natp n))
           (equal (poly-pow-fast acc base n)
                  (poly-mul acc (poly-pow-spec base n))))
  :hints (("Goal" :induct (poly-pow-fast acc base n)
           :in-theory (e/d (poly-pow-fast poly-pow-spec
                                          poly-pow-spec-of-square
                                          poly-pow-spec-odd-form
                                          poly-mul-associate-right-for-power)
                           (poly-mul)))
          ("Subgoal *1/2" :use ((:instance gfield::natural-split-at-low-bit
                                  (n n))
                                  (:instance poly-pow-spec-odd-form
                                   (base base) (n (floor n 2)))))
          ("Subgoal *1/3" :use ((:instance gfield::natural-split-at-low-bit
                                  (n n))))
          ("Subgoal *1/1" :use ((:instance gfield::natural-split-at-low-bit
                                  (n n))))))

(defthm canonical-polynomial-p-of-poly-pow-spec
  (canonical-polynomial-p (poly-pow-spec base n))
  :hints (("Goal" :induct (poly-pow-spec base n)
           :in-theory (enable poly-pow-spec))))

(defthm poly-pow-fast-correct
  (equal (poly-pow-fast (polynomial-one) (normalize f) (nfix n))
         (poly-pow-spec (normalize f) (nfix n)))
  :hints (("Goal" :use ((:instance poly-pow-fast-accumulator-invariant
                          (acc (polynomial-one))
                          (base (normalize f))
                          (n (nfix n)))))))

(verify-guards fix-coefficients)
(verify-guards trim-trailing-zeros)
(verify-guards normalize)
(verify-guards raw-add)
(verify-guards poly-add)
(verify-guards raw-scale)
(verify-guards poly-scale)
(verify-guards raw-mul)
(verify-guards poly-mul)
(verify-guards polynomial-one)
(verify-guards poly-pow-fast)
(verify-guards poly-pow
  :hints (("Goal" :use poly-pow-fast-correct)))

(defthm eval-of-poly-pow-spec
  (equal (eval (poly-pow-spec (normalize f) n) x)
         (gfield::field-pow-spec (eval f x) (nfix n)))
  :hints (("Goal" :induct (poly-pow-spec (normalize f) n)
           :in-theory (enable poly-pow-spec gfield::field-pow-spec))))

(defthm eval-of-poly-pow
  (equal (eval (poly-pow f n) x)
         (gfield::field-pow (eval f x) n))
  :hints (("Goal" :use (poly-pow-correct
                          (:instance eval-of-poly-pow-spec (f f) (n (nfix n)))
                          (:instance gfield::field-pow-correct
                           (x (eval f x)) (n n)))
           :in-theory (disable poly-pow gfield::field-pow))))

(in-theory (disable poly-pow-spec eval-of-poly-pow-spec))
