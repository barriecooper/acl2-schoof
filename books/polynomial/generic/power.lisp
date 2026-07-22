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
