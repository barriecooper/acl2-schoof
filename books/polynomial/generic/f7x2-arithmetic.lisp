(in-package "GPOLY")
(include-book "f7x2-representation")
(include-book "f7-reduced-arithmetic")

; Transparent carrier arithmetic: each operation is the existing concrete F7
; polynomial operation followed by the sole F7X2 fixer/remainder boundary.
(defun f7x2-add (first second)
  (f7x2-fix (f7-poly-add first second)))
(defun f7x2-neg (value)
  (f7x2-fix (f7-poly-neg value)))
(defun f7x2-sub (first second)
  (f7x2-fix (f7-poly-sub first second)))
(defun f7x2-mul (first second)
  (f7x2-fix (f7-poly-mul first second)))

; This is the coefficient-only checkpoint that blocked the earlier bounded
; convolution attempt.  Keep it local and non-rewriting: the reusable public
; fact belongs to the concrete F7 coefficient interface.
(local
 (defthm f7-fixer-congruence-blocked-convolution-checkpoint
   (implies (and (gfield::f7-element-p a)
                 (gfield::f7-element-p b)
                 (gfield::f7-element-p c)
                 (gfield::f7-element-p d))
            (equal
             (gfield::f7-fix
              (pfield::add
               (gfield::f7-fix (pfield::mul a d 7))
               (gfield::f7-fix
                (mod (gfield::f7-fix (pfield::mul b c 7)) 7))
               7))
             (gfield::f7-fix
              (pfield::add
               (gfield::f7-fix (pfield::mul a d 7))
               (gfield::f7-fix (pfield::mul b c 7))
               7))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance gfield::f7-element-p-of-f7-mul
                             (x b) (y c)))
            :in-theory (e/d (gfield::f7-mul)
                            (gfield::f7-fix))))))

; The generic reduction package already proves that operation followed by
; remainder is invariant under replacing every operand by its remainder.  The
; following concrete specializations are kept local: the public interface
; below names the presentation-specific fixer rather than exposing the
; generic quotient machinery.
(local
 (defthm f7-poly-reduced-add-of-remainders-for-f7x2
   (equal (f7-poly-remainder
           (f7-poly-add (f7-poly-remainder left modulus)
                        (f7-poly-remainder right modulus)) modulus)
          (f7-poly-remainder (f7-poly-add left right) modulus))
   :rule-classes nil
   :hints (("Goal" :use ((:functional-instance
                         poly-reduced-add-of-remainders
                         (gfield::field-element-p gfield::f7-element-p)
                         (gfield::field-fix gfield::f7-fix)
                         (gfield::field-zero gfield::f7-zero)
                         (gfield::field-one gfield::f7-one)
                         (gfield::field-add gfield::f7-add)
                         (gfield::field-mul gfield::f7-mul)
                         (gfield::field-neg gfield::f7-neg)
                         (gfield::field-inv gfield::f7-inv)
                         (gfield::field-div gfield::f7-div)
                         (fix-coefficients f7-fix-coefficients)
                         (trim-trailing-zeros f7-trim-trailing-zeros)
                         (normalize f7-normalize)
                         (coefficient-list-p f7-coefficient-list-p)
                         (polynomial-p f7-polynomial-p)
                         (canonical-polynomial-p f7-canonical-polynomial-p)
                         (raw-add f7-raw-add) (poly-add f7-poly-add)
                         (raw-neg f7-raw-neg) (poly-neg f7-poly-neg)
                         (poly-sub f7-poly-sub)
                         (raw-scale f7-raw-scale) (poly-scale f7-poly-scale)
                         (raw-mul f7-raw-mul) (poly-mul f7-poly-mul)
                         (zero-prefix f7-zero-prefix)
                         (poly-shift f7-poly-shift) (monomial f7-monomial)
                         (poly-degree f7-poly-degree)
                         (poly-leading-coefficient f7-poly-leading-coefficient)
                         (poly-division-step-core f7-poly-division-step-core)
                         (poly-division-step f7-poly-division-step)
                         (poly-division-step-term f7-poly-division-step-term)
                         (poly-division-step-next f7-poly-division-step-next)
                         (poly-divmod-core f7-poly-divmod-core)
                         (poly-divmod f7-poly-divmod)
                         (poly-remainder f7-poly-remainder)
                         (poly-reduced-add f7-poly-reduced-add)))
            :in-theory (enable f7-poly-reduced-add))
           ("Subgoal 29.2" :use gfield::f7-mul-inverse-right)
           ("Subgoal 26.9" :use ((:instance f7-mul-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
           ("Subgoal 26.4" :use ((:instance f7-mul-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
           ("Subgoal 25.11" :use ((:instance f7-add-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
           ("Subgoal 25.6" :use ((:instance f7-add-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
           ("Subgoal 22.2.1" :use gfield::f7-element-p-of-f7-fix
            :in-theory (enable gfield::f7-fix gfield::f7-element-p))
           ("Subgoal 22.2.1'''" :in-theory (enable mod))
           ("Subgoal 22.2.1'" :in-theory (enable mod))
           ("Subgoal 21.2.1'" :in-theory (enable mod))
           ("Subgoal 9.9.1'" :use ((:instance f7-poly-divmod-core)))
           ("Subgoal 6.9.1'" :use ((:instance f7-poly-divmod-core)))
           ("Subgoal 2.3'" :use f7-trim-change-implies-last-zero-for-divmod-instantiation)
           ("Subgoal 2.1" :use ((:instance f7-canonical-polynomial-p-implies-last-nonzero (p xs))))
           ("Subgoal 8.2.1'" :in-theory (enable mod))))
 )


(local
 (defthm f7-poly-reduced-neg-of-remainder-for-f7x2
   (equal (f7-poly-remainder
           (f7-poly-neg (f7-poly-remainder polynomial modulus)) modulus)
          (f7-poly-remainder (f7-poly-neg polynomial) modulus))
   :rule-classes nil
   :hints (("Goal" :use ((:functional-instance
                         poly-reduced-neg-of-remainder
                         (gfield::field-element-p gfield::f7-element-p)
                         (gfield::field-fix gfield::f7-fix)
                         (gfield::field-zero gfield::f7-zero)
                         (gfield::field-one gfield::f7-one)
                         (gfield::field-add gfield::f7-add)
                         (gfield::field-mul gfield::f7-mul)
                         (gfield::field-neg gfield::f7-neg)
                         (gfield::field-inv gfield::f7-inv)
                         (gfield::field-div gfield::f7-div)
                         (fix-coefficients f7-fix-coefficients)
                         (trim-trailing-zeros f7-trim-trailing-zeros)
                         (normalize f7-normalize)
                         (coefficient-list-p f7-coefficient-list-p)
                         (polynomial-p f7-polynomial-p)
                         (canonical-polynomial-p f7-canonical-polynomial-p)
                         (raw-add f7-raw-add) (poly-add f7-poly-add)
                         (raw-neg f7-raw-neg) (poly-neg f7-poly-neg)
                         (poly-sub f7-poly-sub)
                         (raw-scale f7-raw-scale) (poly-scale f7-poly-scale)
                         (raw-mul f7-raw-mul) (poly-mul f7-poly-mul)
                         (zero-prefix f7-zero-prefix)
                         (poly-shift f7-poly-shift) (monomial f7-monomial)
                         (poly-degree f7-poly-degree)
                         (poly-leading-coefficient f7-poly-leading-coefficient)
                         (poly-division-step-core f7-poly-division-step-core)
                         (poly-division-step f7-poly-division-step)
                         (poly-division-step-term f7-poly-division-step-term)
                         (poly-division-step-next f7-poly-division-step-next)
                         (poly-divmod-core f7-poly-divmod-core)
                         (poly-divmod f7-poly-divmod)
                         (poly-remainder f7-poly-remainder)
                         (poly-reduced-neg f7-poly-reduced-neg)))
            :in-theory (enable f7-poly-reduced-neg))
           ("Subgoal 29.2" :use gfield::f7-mul-inverse-right)
           ("Subgoal 26.9" :use ((:instance f7-mul-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
           ("Subgoal 26.4" :use ((:instance f7-mul-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
           ("Subgoal 25.11" :use ((:instance f7-add-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
           ("Subgoal 25.6" :use ((:instance f7-add-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
           ("Subgoal 22.2.1" :use gfield::f7-element-p-of-f7-fix
            :in-theory (enable gfield::f7-fix gfield::f7-element-p))
           ("Subgoal 22.2.1'''" :in-theory (enable mod))
           ("Subgoal 22.2.1'" :in-theory (enable mod))
           ("Subgoal 21.2.1'" :in-theory (enable mod))
           ("Subgoal 9.9.1'" :use ((:instance f7-poly-divmod-core)))
           ("Subgoal 6.9.1'" :use ((:instance f7-poly-divmod-core)))
           ("Subgoal 2.3'" :use f7-trim-change-implies-last-zero-for-divmod-instantiation)
           ("Subgoal 2.1" :use ((:instance f7-canonical-polynomial-p-implies-last-nonzero (p xs))))
           ("Subgoal 8.2.1'" :in-theory (enable mod))))
 )


(local
 (defthm f7-poly-reduced-sub-of-remainders-for-f7x2
   (equal (f7-poly-remainder
           (f7-poly-sub (f7-poly-remainder left modulus)
                        (f7-poly-remainder right modulus)) modulus)
          (f7-poly-remainder (f7-poly-sub left right) modulus))
   :rule-classes nil
   :hints (("Goal" :use ((:functional-instance
                         poly-reduced-sub-of-remainders
                         (gfield::field-element-p gfield::f7-element-p)
                         (gfield::field-fix gfield::f7-fix)
                         (gfield::field-zero gfield::f7-zero)
                         (gfield::field-one gfield::f7-one)
                         (gfield::field-add gfield::f7-add)
                         (gfield::field-mul gfield::f7-mul)
                         (gfield::field-neg gfield::f7-neg)
                         (gfield::field-inv gfield::f7-inv)
                         (gfield::field-div gfield::f7-div)
                         (fix-coefficients f7-fix-coefficients)
                         (trim-trailing-zeros f7-trim-trailing-zeros)
                         (normalize f7-normalize)
                         (coefficient-list-p f7-coefficient-list-p)
                         (polynomial-p f7-polynomial-p)
                         (canonical-polynomial-p f7-canonical-polynomial-p)
                         (raw-add f7-raw-add) (poly-add f7-poly-add)
                         (raw-neg f7-raw-neg) (poly-neg f7-poly-neg)
                         (poly-sub f7-poly-sub)
                         (raw-scale f7-raw-scale) (poly-scale f7-poly-scale)
                         (raw-mul f7-raw-mul) (poly-mul f7-poly-mul)
                         (zero-prefix f7-zero-prefix)
                         (poly-shift f7-poly-shift) (monomial f7-monomial)
                         (poly-degree f7-poly-degree)
                         (poly-leading-coefficient f7-poly-leading-coefficient)
                         (poly-division-step-core f7-poly-division-step-core)
                         (poly-division-step f7-poly-division-step)
                         (poly-division-step-term f7-poly-division-step-term)
                         (poly-division-step-next f7-poly-division-step-next)
                         (poly-divmod-core f7-poly-divmod-core)
                         (poly-divmod f7-poly-divmod)
                         (poly-remainder f7-poly-remainder)
                         (poly-reduced-sub f7-poly-reduced-sub)))
            :in-theory (enable f7-poly-reduced-sub))
           ("Subgoal 29.2" :use gfield::f7-mul-inverse-right)
           ("Subgoal 26.9" :use ((:instance f7-mul-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
           ("Subgoal 26.4" :use ((:instance f7-mul-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
           ("Subgoal 25.11" :use ((:instance f7-add-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
           ("Subgoal 25.6" :use ((:instance f7-add-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
           ("Subgoal 22.2.1" :use gfield::f7-element-p-of-f7-fix
            :in-theory (enable gfield::f7-fix gfield::f7-element-p))
           ("Subgoal 22.2.1'''" :in-theory (enable mod))
           ("Subgoal 22.2.1'" :in-theory (enable mod))
           ("Subgoal 21.2.1'" :in-theory (enable mod))
           ("Subgoal 9.9.1'" :use ((:instance f7-poly-divmod-core)))
           ("Subgoal 6.9.1'" :use ((:instance f7-poly-divmod-core)))
           ("Subgoal 2.3'" :use f7-trim-change-implies-last-zero-for-divmod-instantiation)
           ("Subgoal 2.1" :use ((:instance f7-canonical-polynomial-p-implies-last-nonzero (p xs))))
           ("Subgoal 8.2.1'" :in-theory (enable mod))))
 )


(local
 (defthm f7-poly-reduced-mul-of-remainders-for-f7x2
   (equal (f7-poly-remainder
           (f7-poly-mul (f7-poly-remainder left modulus)
                        (f7-poly-remainder right modulus)) modulus)
          (f7-poly-remainder (f7-poly-mul left right) modulus))
   :rule-classes nil
   :hints (("Goal" :use ((:functional-instance
                         poly-reduced-mul-of-remainders
                         (gfield::field-element-p gfield::f7-element-p)
                         (gfield::field-fix gfield::f7-fix)
                         (gfield::field-zero gfield::f7-zero)
                         (gfield::field-one gfield::f7-one)
                         (gfield::field-add gfield::f7-add)
                         (gfield::field-mul gfield::f7-mul)
                         (gfield::field-neg gfield::f7-neg)
                         (gfield::field-inv gfield::f7-inv)
                         (gfield::field-div gfield::f7-div)
                         (fix-coefficients f7-fix-coefficients)
                         (trim-trailing-zeros f7-trim-trailing-zeros)
                         (normalize f7-normalize)
                         (coefficient-list-p f7-coefficient-list-p)
                         (polynomial-p f7-polynomial-p)
                         (canonical-polynomial-p f7-canonical-polynomial-p)
                         (raw-add f7-raw-add) (poly-add f7-poly-add)
                         (raw-neg f7-raw-neg) (poly-neg f7-poly-neg)
                         (poly-sub f7-poly-sub)
                         (raw-scale f7-raw-scale) (poly-scale f7-poly-scale)
                         (raw-mul f7-raw-mul) (poly-mul f7-poly-mul)
                         (zero-prefix f7-zero-prefix)
                         (poly-shift f7-poly-shift) (monomial f7-monomial)
                         (poly-degree f7-poly-degree)
                         (poly-leading-coefficient f7-poly-leading-coefficient)
                         (poly-division-step-core f7-poly-division-step-core)
                         (poly-division-step f7-poly-division-step)
                         (poly-division-step-term f7-poly-division-step-term)
                         (poly-division-step-next f7-poly-division-step-next)
                         (poly-divmod-core f7-poly-divmod-core)
                         (poly-divmod f7-poly-divmod)
                         (poly-remainder f7-poly-remainder)
                         (poly-reduced-mul f7-poly-reduced-mul)))
            :in-theory (enable f7-poly-reduced-mul))
           ("Subgoal 29.2" :use gfield::f7-mul-inverse-right)
           ("Subgoal 26.9" :use ((:instance f7-mul-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
           ("Subgoal 26.4" :use ((:instance f7-mul-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
           ("Subgoal 25.11" :use ((:instance f7-add-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
           ("Subgoal 25.6" :use ((:instance f7-add-fixed-congruence-for-divmod-instantiation (x1 gfield::x1) (x2 gfield::x2) (y1 gfield::y1) (y2 gfield::y2))))
           ("Subgoal 22.2.1" :use gfield::f7-element-p-of-f7-fix
            :in-theory (enable gfield::f7-fix gfield::f7-element-p))
           ("Subgoal 22.2.1'''" :in-theory (enable mod))
           ("Subgoal 22.2.1'" :in-theory (enable mod))
           ("Subgoal 21.2.1'" :in-theory (enable mod))
           ("Subgoal 9.9.1'" :use ((:instance f7-poly-divmod-core)))
           ("Subgoal 6.9.1'" :use ((:instance f7-poly-divmod-core)))
           ("Subgoal 2.3'" :use f7-trim-change-implies-last-zero-for-divmod-instantiation)
           ("Subgoal 2.1" :use ((:instance f7-canonical-polynomial-p-implies-last-nonzero (p xs))))
           ("Subgoal 8.2.1'" :in-theory (enable mod))))
 )


(verify-guards f7x2-add
  :hints (("Goal" :in-theory (enable f7x2-add))))
(verify-guards f7x2-neg
  :hints (("Goal" :in-theory (enable f7x2-neg))))
(verify-guards f7x2-sub
  :hints (("Goal" :in-theory (enable f7x2-sub))))
(verify-guards f7x2-mul
  :hints (("Goal" :in-theory (enable f7x2-mul))))

(defthm f7x2-add-of-fixes
  (equal (f7x2-add (f7x2-fix first) (f7x2-fix second))
         (f7x2-add first second))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f7-poly-reduced-add-of-remainders-for-f7x2
                                   (left first) (right second)
                                   (modulus '(1 0 1))))
           :in-theory (enable f7x2-add f7x2-fix))))
(defthm f7x2-neg-of-fix
  (equal (f7x2-neg (f7x2-fix value)) (f7x2-neg value))
  :hints (("Goal" :use ((:instance f7-poly-reduced-neg-of-remainder-for-f7x2
                                   (polynomial value) (modulus '(1 0 1))))
           :in-theory (enable f7x2-neg f7x2-fix))))
(defthm f7x2-sub-of-fixes
  (equal (f7x2-sub (f7x2-fix first) (f7x2-fix second))
         (f7x2-sub first second))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f7-poly-reduced-sub-of-remainders-for-f7x2
                                   (left first) (right second)
                                   (modulus '(1 0 1))))
           :in-theory (enable f7x2-sub f7x2-fix))))
(defthm f7x2-mul-of-fixes
  (equal (f7x2-mul (f7x2-fix first) (f7x2-fix second))
         (f7x2-mul first second))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f7-poly-reduced-mul-of-remainders-for-f7x2
                                   (left first) (right second)
                                   (modulus '(1 0 1))))
           :in-theory (enable f7x2-mul f7x2-fix))))

(defthm f7x2-add-of-fix-left
  (equal (f7x2-add (f7x2-fix first) second) (f7x2-add first second))
  :hints (("Goal" :use ((:instance f7x2-add-of-fixes)
                         (:instance f7x2-add-of-fixes
                                    (first (f7x2-fix first))))
           :in-theory (disable f7x2-add f7x2-fix))))
(defthm f7x2-add-of-fix-right
  (equal (f7x2-add first (f7x2-fix second)) (f7x2-add first second))
  :hints (("Goal" :use ((:instance f7x2-add-of-fixes)
                         (:instance f7x2-add-of-fixes
                                    (second (f7x2-fix second))))
           :in-theory (disable f7x2-add f7x2-fix))))
(defthm f7x2-sub-of-fix-left
  (equal (f7x2-sub (f7x2-fix first) second) (f7x2-sub first second))
  :hints (("Goal" :use ((:instance f7x2-sub-of-fixes)
                         (:instance f7x2-sub-of-fixes
                                    (first (f7x2-fix first))))
           :in-theory (disable f7x2-sub f7x2-fix))))
(defthm f7x2-sub-of-fix-right
  (equal (f7x2-sub first (f7x2-fix second)) (f7x2-sub first second))
  :hints (("Goal" :use ((:instance f7x2-sub-of-fixes)
                         (:instance f7x2-sub-of-fixes
                                    (second (f7x2-fix second))))
           :in-theory (disable f7x2-sub f7x2-fix))))
(defthm f7x2-mul-of-fix-left
  (equal (f7x2-mul (f7x2-fix first) second) (f7x2-mul first second))
  :hints (("Goal" :use ((:instance f7x2-mul-of-fixes)
                         (:instance f7x2-mul-of-fixes
                                    (first (f7x2-fix first))))
           :in-theory (disable f7x2-mul f7x2-fix))))
(defthm f7x2-mul-of-fix-right
  (equal (f7x2-mul first (f7x2-fix second)) (f7x2-mul first second))
  :hints (("Goal" :use ((:instance f7x2-mul-of-fixes)
                         (:instance f7x2-mul-of-fixes
                                    (second (f7x2-fix second))))
           :in-theory (disable f7x2-mul f7x2-fix))))

(defthm f7x2-element-p-of-f7x2-add
  (f7x2-element-p (f7x2-add first second))
  :hints (("Goal" :use ((:instance f7x2-element-p-of-f7x2-fix (x (f7-poly-add first second))))
           :in-theory (e/d (f7x2-add) (f7x2-element-p-of-f7x2-fix)))) )
(defthm f7x2-element-p-of-f7x2-neg
  (f7x2-element-p (f7x2-neg value))
  :hints (("Goal" :use ((:instance f7x2-element-p-of-f7x2-fix (x (f7-poly-neg value))))
           :in-theory (e/d (f7x2-neg) (f7x2-element-p-of-f7x2-fix)))) )
(defthm f7x2-element-p-of-f7x2-sub
  (f7x2-element-p (f7x2-sub first second))
  :hints (("Goal" :use ((:instance f7x2-element-p-of-f7x2-fix (x (f7-poly-sub first second))))
           :in-theory (e/d (f7x2-sub) (f7x2-element-p-of-f7x2-fix)))) )
(defthm f7x2-element-p-of-f7x2-mul
  (f7x2-element-p (f7x2-mul first second))
  :hints (("Goal" :use ((:instance f7x2-element-p-of-f7x2-fix (x (f7-poly-mul first second))))
           :in-theory (e/d (f7x2-mul) (f7x2-element-p-of-f7x2-fix)))) )

(local
 (defthm f7x2-fix-reconstruct
   (equal (f7x2-fix value)
          (f7-normalize
           (list (f7x2-constant-coefficient value)
                 (f7x2-linear-coefficient value))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7x2-reconstruct-from-coefficients
                             (value (f7x2-fix value))))
            :in-theory (disable f7x2-fix f7-normalize)))))

; Bounded coefficientwise addition for the reconstructed representatives used
; by the coefficient interface.  Keeping this whole-value calculation
; separate prevents the rewriter from expanding recursive addition while it
; is also transporting arbitrary operands through F7X2-FIX.
(defthm f7-poly-add-of-normalized-two-coefficients
  (implies (and (gfield::f7-element-p a)
                (gfield::f7-element-p b)
                (gfield::f7-element-p c)
                (gfield::f7-element-p d))
           (equal (f7-poly-add (f7-normalize (list a b))
                               (f7-normalize (list c d)))
                  (f7-normalize
                   (list (gfield::f7-add a c)
                         (gfield::f7-add b d)))))
  :rule-classes nil
  :hints (("Goal"
           :cases ((equal b 0) (equal d 0))
           :in-theory
           (e/d (f7-poly-add f7-raw-add f7-normalize
                             f7-fix-coefficients f7-trim-trailing-zeros)
                (f7-poly-divmod f7-poly-divmod-core
                                f7-poly-division-step
                                f7-poly-division-step-core
                                f7-poly-remainder)))))

(defthm f7-constant-projection-of-add-of-normalized-two-coefficients
  (implies (and (gfield::f7-element-p a)
                (gfield::f7-element-p b)
                (gfield::f7-element-p c)
                (gfield::f7-element-p d))
           (equal
            (gfield::f7-fix
             (car (f7-poly-add (f7-normalize (list a b))
                               (f7-normalize (list c d)))))
            (gfield::f7-add a c)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance f7-poly-add-of-normalized-two-coefficients)
                 (:instance f7-element-p-of-f7-add-for-raw-shape
                            (x a) (y c)))
           :in-theory
           (e/d (f7-normalize f7-fix-coefficients
                              f7-trim-trailing-zeros)
                (f7-poly-add f7-raw-add gfield::f7-add
                             gfield::f7-fix)))))

(defthm f7-linear-projection-of-add-of-normalized-two-coefficients
  (implies (and (gfield::f7-element-p a)
                (gfield::f7-element-p b)
                (gfield::f7-element-p c)
                (gfield::f7-element-p d))
           (equal
            (gfield::f7-fix
             (cadr (f7-poly-add (f7-normalize (list a b))
                                (f7-normalize (list c d)))))
            (gfield::f7-add b d)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance f7-poly-add-of-normalized-two-coefficients)
                 (:instance f7-element-p-of-f7-add-for-raw-shape
                            (x b) (y d)))
           :in-theory
           (e/d (f7-normalize f7-fix-coefficients
                              f7-trim-trailing-zeros)
                (f7-poly-add f7-raw-add gfield::f7-add
                             gfield::f7-fix)))))

; These bounded negation and subtraction calculations are internal polynomial
; bridges for the later F7X2 coefficient proofs.  They deliberately stop below
; the public carrier operations and keep all reduction and division machinery
; closed.
(local
 (defthm f7-element-p-of-f7-neg-for-bounded-negation
   (gfield::f7-element-p (gfield::f7-neg x))
   :hints (("Goal" :in-theory (enable gfield::f7-element-p
                                      gfield::f7-neg
                                      gfield::f7-fix)))))

(local
 (defthm f7-poly-neg-of-normalized-two-coefficients
   (implies (and (gfield::f7-element-p a)
                 (gfield::f7-element-p b))
            (equal (f7-poly-neg (f7-normalize (list a b)))
                   (f7-normalize
                    (list (gfield::f7-neg a)
                          (gfield::f7-neg b)))))
   :rule-classes nil
   :hints (("Goal"
            :cases ((equal b 0))
            :in-theory
            (e/d (f7-poly-neg f7-raw-neg f7-normalize
                              f7-fix-coefficients f7-trim-trailing-zeros)
                 (f7-poly-add f7-raw-add f7-poly-remainder
                              f7-poly-divmod f7-poly-divmod-core
                              f7-poly-division-step
                              f7-poly-division-step-core))))))

(local
 (defthm f7-constant-projection-of-neg-of-normalized-two-coefficients
   (implies (and (gfield::f7-element-p a)
                 (gfield::f7-element-p b))
            (equal
             (gfield::f7-fix
              (car (f7-poly-neg (f7-normalize (list a b)))))
             (gfield::f7-neg a)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7-poly-neg-of-normalized-two-coefficients)
                  (:instance f7-element-p-of-f7-neg-for-bounded-negation
                             (x a)))
            :in-theory
            (e/d (f7-normalize f7-fix-coefficients
                               f7-trim-trailing-zeros)
                 (f7-poly-neg f7-raw-neg gfield::f7-neg
                              gfield::f7-fix))))))

(local
 (defthm f7-linear-projection-of-neg-of-normalized-two-coefficients
   (implies (and (gfield::f7-element-p a)
                 (gfield::f7-element-p b))
            (equal
             (gfield::f7-fix
              (cadr (f7-poly-neg (f7-normalize (list a b)))))
             (gfield::f7-neg b)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7-poly-neg-of-normalized-two-coefficients)
                  (:instance f7-element-p-of-f7-neg-for-bounded-negation
                             (x b)))
            :in-theory
            (e/d (f7-normalize f7-fix-coefficients
                               f7-trim-trailing-zeros)
                 (f7-poly-neg f7-raw-neg gfield::f7-neg
                              gfield::f7-fix))))))

(local
 (defthm f7-poly-sub-of-normalized-two-coefficients
   (implies (and (gfield::f7-element-p a)
                 (gfield::f7-element-p b)
                 (gfield::f7-element-p c)
                 (gfield::f7-element-p d))
            (equal (f7-poly-sub (f7-normalize (list a b))
                                (f7-normalize (list c d)))
                   (f7-normalize
                    (list (gfield::f7-sub a c)
                          (gfield::f7-sub b d)))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7-poly-sub-definition
                             (x (f7-normalize (list a b)))
                             (y (f7-normalize (list c d))))
                  (:instance f7-poly-neg-of-normalized-two-coefficients
                             (a c) (b d))
                  (:instance f7-poly-add-of-normalized-two-coefficients
                             (c (gfield::f7-neg c))
                             (d (gfield::f7-neg d)))
                  (:instance f7-element-p-of-f7-neg-for-bounded-negation
                             (x c))
                  (:instance f7-element-p-of-f7-neg-for-bounded-negation
                             (x d)))
            :in-theory
            (e/d (gfield::f7-sub)
                 (f7-poly-sub f7-poly-neg f7-raw-neg
                              f7-poly-add f7-raw-add f7-normalize
                              f7-fix-coefficients f7-trim-trailing-zeros
                              f7-poly-remainder f7-poly-divmod
                              f7-poly-divmod-core f7-poly-division-step
                              f7-poly-division-step-core))))))


(local
 (defthm f7-constant-projection-of-sub-of-normalized-two-coefficients
   (implies (and (gfield::f7-element-p a)
                 (gfield::f7-element-p b)
                 (gfield::f7-element-p c)
                 (gfield::f7-element-p d))
            (equal
             (gfield::f7-fix
              (car (f7-poly-sub (f7-normalize (list a b))
                                (f7-normalize (list c d)))))
             (gfield::f7-sub a c)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7-poly-sub-of-normalized-two-coefficients))
            :in-theory
            (e/d (f7-normalize f7-fix-coefficients
                               f7-trim-trailing-zeros
                               gfield::f7-sub)
                 (f7-poly-sub f7-poly-neg f7-raw-neg
                              f7-poly-add f7-raw-add
                              gfield::f7-add gfield::f7-neg
                              gfield::f7-fix))))))

(local
 (defthm f7-linear-projection-of-sub-of-normalized-two-coefficients
   (implies (and (gfield::f7-element-p a)
                 (gfield::f7-element-p b)
                 (gfield::f7-element-p c)
                 (gfield::f7-element-p d))
            (equal
             (gfield::f7-fix
              (cadr (f7-poly-sub (f7-normalize (list a b))
                                 (f7-normalize (list c d)))))
             (gfield::f7-sub b d)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7-poly-sub-of-normalized-two-coefficients))
            :in-theory
            (e/d (f7-normalize f7-fix-coefficients
                               f7-trim-trailing-zeros
                               gfield::f7-sub)
                 (f7-poly-sub f7-poly-neg f7-raw-neg
                              f7-poly-add f7-raw-add
                              gfield::f7-add gfield::f7-neg
                              gfield::f7-fix))))))

(local
 (defthm f7-normalize-two-is-normalize-three-with-zero
   (implies (and (gfield::f7-element-p a)
                 (gfield::f7-element-p b))
            (equal (f7-normalize (list a b 0))
                   (f7-normalize (list a b))))
   :hints (("Goal" :in-theory
            (e/d (f7-normalize f7-fix-coefficients
                               f7-trim-trailing-zeros)
                 (gfield::f7-fix gfield::f7-element-p))))))

; The only recursive multiplication calculation in the bounded bridge.  The
; two case splits account for canonical constant/nil operands; in the genuine
; linear case the public F7 fixer-congruence rules reconcile the raw ADD/MUL
; presentation with the coefficient operations below.
(local
 (defthm f7-poly-mul-of-normalized-two-coefficients
   (implies (and (gfield::f7-element-p a)
                 (gfield::f7-element-p b)
                 (gfield::f7-element-p c)
                 (gfield::f7-element-p d))
            (equal
             (f7-poly-mul (f7-normalize (list a b))
                          (f7-normalize (list c d)))
             (f7-normalize
              (list (gfield::f7-mul a c)
                    (gfield::f7-add (gfield::f7-mul a d)
                                    (gfield::f7-mul b c))
                    (gfield::f7-mul b d)))))
   :rule-classes nil
   :hints
   (("Goal"
     :cases ((equal b 0) (equal d 0))
     :in-theory
     (e/d (f7-poly-mul f7-raw-mul f7-raw-scale f7-raw-add
                       f7-normalize f7-fix-coefficients
                       f7-trim-trailing-zeros)
          (f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
           f7-poly-division-step f7-poly-division-step-core))))))

; Recognition is stated separately from the convolution so that reduction can
; consume the bounded calculation with every multiplication recursion closed.
(local
 (defthm f7-convolution-coefficients-recognized
   (implies (and (gfield::f7-element-p a)
                 (gfield::f7-element-p b)
                 (gfield::f7-element-p c)
                 (gfield::f7-element-p d))
            (and
             (gfield::f7-element-p (gfield::f7-mul a c))
             (gfield::f7-element-p
              (gfield::f7-add (gfield::f7-mul a d)
                              (gfield::f7-mul b c)))
             (gfield::f7-element-p (gfield::f7-mul b d))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7-element-p-of-f7-add-for-raw-shape
                             (x (gfield::f7-mul a d))
                             (y (gfield::f7-mul b c))))))))

(local
 (defthm f7x2-fix-of-normalize-for-bounded-product
   (equal (f7x2-fix (f7-normalize polynomial))
          (f7x2-fix polynomial))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7-poly-remainder-of-normalize-dividend
                             (f polynomial) (g '(1 0 1))))
            :in-theory
            (e/d (f7x2-fix)
                 (f7-poly-remainder f7-poly-divmod
                  f7-poly-divmod-core f7-poly-division-step
                  f7-poly-division-step-core))))))

; Whole-value composition with the existing three-coefficient reduction
; theorem.  In particular, the quadratic coefficient is subtracted from the
; constant coefficient, expressing X^2 = -1 without opening division.
(local
 (defthm f7x2-fix-of-bounded-normalized-product
   (implies (and (gfield::f7-element-p a)
                 (gfield::f7-element-p b)
                 (gfield::f7-element-p c)
                 (gfield::f7-element-p d))
            (equal
             (f7x2-fix
              (f7-poly-mul (f7-normalize (list a b))
                           (f7-normalize (list c d))))
             (f7-normalize
              (list
               (gfield::f7-sub (gfield::f7-mul a c)
                               (gfield::f7-mul b d))
               (gfield::f7-add (gfield::f7-mul a d)
                               (gfield::f7-mul b c))))))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance f7-poly-mul-of-normalized-two-coefficients)
           (:instance f7-convolution-coefficients-recognized)
           (:instance f7x2-fix-of-three-coefficients
                      (a (gfield::f7-mul a c))
                      (b (gfield::f7-add (gfield::f7-mul a d)
                                        (gfield::f7-mul b c)))
                      (c (gfield::f7-mul b d)))
           (:instance f7x2-fix-of-normalize-for-bounded-product
                      (polynomial
                       (list (gfield::f7-mul a c)
                             (gfield::f7-add (gfield::f7-mul a d)
                                             (gfield::f7-mul b c))
                             (gfield::f7-mul b d)))))
     :in-theory
     (disable f7-poly-mul f7-raw-mul f7-raw-scale f7-raw-add
              f7x2-fix
              f7-poly-remainder f7-poly-divmod
              f7-poly-divmod-core f7-poly-division-step
              f7-poly-division-step-core f7-normalize
              gfield::f7-fix gfield::f7-add gfield::f7-mul
              gfield::f7-sub)))))

(local
 (defthm f7x2-constant-projection-of-bounded-normalized-product
   (implies (and (gfield::f7-element-p a)
                 (gfield::f7-element-p b)
                 (gfield::f7-element-p c)
                 (gfield::f7-element-p d))
            (equal
             (f7x2-constant-coefficient
              (f7-poly-mul (f7-normalize (list a b))
                           (f7-normalize (list c d))))
             (gfield::f7-sub (gfield::f7-mul a c)
                             (gfield::f7-mul b d))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7x2-fix-of-bounded-normalized-product)
                  (:instance f7-convolution-coefficients-recognized)
                  (:instance f7x2-constant-coefficient-of-fix
                             (x (f7-poly-mul
                                 (f7-normalize (list a b))
                                 (f7-normalize (list c d))))))
            :in-theory
            (e/d (f7x2-constant-coefficient f7-normalize
                                            f7-fix-coefficients
                                            f7-trim-trailing-zeros
                                            gfield::f7-sub)
                 (f7-poly-mul f7x2-fix f7-poly-remainder
                  f7-poly-divmod f7-poly-divmod-core
                  f7-poly-division-step f7-poly-division-step-core
                  gfield::f7-fix))))))

(local
 (defthm f7x2-linear-projection-of-bounded-normalized-product
   (implies (and (gfield::f7-element-p a)
                 (gfield::f7-element-p b)
                 (gfield::f7-element-p c)
                 (gfield::f7-element-p d))
            (equal
             (f7x2-linear-coefficient
              (f7-poly-mul (f7-normalize (list a b))
                           (f7-normalize (list c d))))
             (gfield::f7-add (gfield::f7-mul a d)
                             (gfield::f7-mul b c))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7x2-fix-of-bounded-normalized-product)
                  (:instance f7-convolution-coefficients-recognized)
                  (:instance f7x2-linear-coefficient-of-fix
                             (x (f7-poly-mul
                                 (f7-normalize (list a b))
                                 (f7-normalize (list c d))))))
            :in-theory
            (e/d (f7x2-linear-coefficient f7-normalize
                                          f7-fix-coefficients
                                          f7-trim-trailing-zeros)
                 (f7-poly-mul f7x2-fix f7-poly-remainder
                  f7-poly-divmod f7-poly-divmod-core
                  f7-poly-division-step f7-poly-division-step-core
                  gfield::f7-fix gfield::f7-add))))))

(local
 (defthm f7-sub-zero-right-for-f7x2-addition
   (implies (gfield::f7-element-p a)
            (equal (gfield::f7-sub a 0) a))
   :hints (("Goal" :in-theory
            (enable gfield::f7-sub gfield::f7-add gfield::f7-neg
                    gfield::f7-fix gfield::f7-element-p)))))

(local
 (defthm f7x2-element-p-of-normalized-two-coefficients
   (implies (and (gfield::f7-element-p a)
                 (gfield::f7-element-p b))
            (f7x2-element-p (f7-normalize (list a b))))
   :hints
   (("Goal"
     :use ((:instance f7-normalize-two-is-normalize-three-with-zero)
           (:instance f7-sub-zero-right-for-f7x2-addition)
           (:instance f7-poly-remainder-of-normalize-dividend
                      (f (list a b 0)) (g '(1 0 1)))
           (:instance f7x2-fix-of-three-coefficients (c 0)))
     :in-theory
     (e/d (f7x2-element-p f7x2-fix)
          (f7-poly-remainder-of-normalize-dividend
           f7-poly-remainder-is-divmod-remainder
           gfield::f7-add gfield::f7-sub gfield::f7-fix
           gfield::f7-element-p
           f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
           f7-poly-division-step f7-poly-division-step-core
           f7-normalize f7-fix-coefficients f7-trim-trailing-zeros))))))

(local
 (defthm f7x2-constant-projection-of-bounded-add
   (implies (and (gfield::f7-element-p a)
                 (gfield::f7-element-p b)
                 (gfield::f7-element-p c)
                 (gfield::f7-element-p d))
            (equal
             (f7x2-constant-coefficient
              (f7-poly-add (f7-normalize (list a b))
                           (f7-normalize (list c d))))
             (gfield::f7-add a c)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance f7-poly-add-of-normalized-two-coefficients)
           (:instance f7-element-p-of-f7-add-for-raw-shape (x a) (y c))
           (:instance f7-element-p-of-f7-add-for-raw-shape (x b) (y d))
           (:instance f7x2-element-p-of-normalized-two-coefficients
                      (a (gfield::f7-add a c))
                      (b (gfield::f7-add b d)))
           (:instance
            f7-constant-projection-of-add-of-normalized-two-coefficients))
     :in-theory
     (e/d (f7x2-constant-coefficient)
          (f7x2-constant-coefficient-of-fix
           gfield::f7-add gfield::f7-fix
              gfield::f7-element-p
              f7-poly-add f7-raw-add f7-normalize f7-fix-coefficients
              f7-trim-trailing-zeros f7x2-fix f7-poly-remainder
              f7-poly-divmod f7-poly-divmod-core f7-poly-division-step
              f7-poly-division-step-core))))))

(local
 (defthm f7x2-linear-projection-of-bounded-add
   (implies (and (gfield::f7-element-p a)
                 (gfield::f7-element-p b)
                 (gfield::f7-element-p c)
                 (gfield::f7-element-p d))
            (equal
             (f7x2-linear-coefficient
              (f7-poly-add (f7-normalize (list a b))
                           (f7-normalize (list c d))))
             (gfield::f7-add b d)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance f7-poly-add-of-normalized-two-coefficients)
           (:instance f7-element-p-of-f7-add-for-raw-shape (x a) (y c))
           (:instance f7-element-p-of-f7-add-for-raw-shape (x b) (y d))
           (:instance f7x2-element-p-of-normalized-two-coefficients
                      (a (gfield::f7-add a c))
                      (b (gfield::f7-add b d)))
           (:instance
            f7-linear-projection-of-add-of-normalized-two-coefficients))
     :in-theory
     (e/d (f7x2-linear-coefficient)
          (f7x2-linear-coefficient-of-fix
           gfield::f7-add gfield::f7-fix
              gfield::f7-element-p
              f7-poly-add f7-raw-add f7-normalize f7-fix-coefficients
              f7-trim-trailing-zeros f7x2-fix f7-poly-remainder
              f7-poly-divmod f7-poly-divmod-core f7-poly-division-step
              f7-poly-division-step-core))))))

; Public coefficient behavior is unconditional: the combined fixer theorem
; first transports both arbitrary ACL2 operands to their canonical
; representatives, and the local reconstruction theorem then presents those
; representatives to the bounded two-coefficient bridge above.
(local
 (defthm f7x2-constant-coefficient-of-add-of-fixes
   (equal
    (f7x2-constant-coefficient
     (f7x2-add (f7x2-fix first) (f7x2-fix second)))
    (gfield::f7-add (f7x2-constant-coefficient first)
                    (f7x2-constant-coefficient second)))
   :hints
   (("Goal"
     :use ((:instance f7x2-fix-reconstruct (value first))
           (:instance f7x2-fix-reconstruct (value second))
           (:instance f7-element-p-of-f7x2-constant-coefficient (x first))
           (:instance f7-element-p-of-f7x2-linear-coefficient (x first))
           (:instance f7-element-p-of-f7x2-constant-coefficient (x second))
           (:instance f7-element-p-of-f7x2-linear-coefficient (x second))
           (:instance f7x2-constant-projection-of-bounded-add
                      (a (f7x2-constant-coefficient first))
                      (b (f7x2-linear-coefficient first))
                      (c (f7x2-constant-coefficient second))
                      (d (f7x2-linear-coefficient second))))
     :in-theory
     (e/d (f7x2-add)
          (f7x2-add-of-fix-left f7x2-add-of-fix-right
           f7x2-constant-coefficient f7x2-linear-coefficient
           gfield::f7-add gfield::f7-fix gfield::f7-element-p
           f7-poly-add-normalize-left f7-poly-add-normalize-right
           f7-poly-add f7-raw-add f7-normalize f7-fix-coefficients
           f7-trim-trailing-zeros f7x2-fix f7-poly-remainder))))))

(local
 (defthm f7x2-linear-coefficient-of-add-of-fixes
   (equal
    (f7x2-linear-coefficient
     (f7x2-add (f7x2-fix first) (f7x2-fix second)))
    (gfield::f7-add (f7x2-linear-coefficient first)
                    (f7x2-linear-coefficient second)))
   :hints
   (("Goal"
     :use ((:instance f7x2-fix-reconstruct (value first))
           (:instance f7x2-fix-reconstruct (value second))
           (:instance f7-element-p-of-f7x2-constant-coefficient (x first))
           (:instance f7-element-p-of-f7x2-linear-coefficient (x first))
           (:instance f7-element-p-of-f7x2-constant-coefficient (x second))
           (:instance f7-element-p-of-f7x2-linear-coefficient (x second))
           (:instance f7x2-linear-projection-of-bounded-add
                      (a (f7x2-constant-coefficient first))
                      (b (f7x2-linear-coefficient first))
                      (c (f7x2-constant-coefficient second))
                      (d (f7x2-linear-coefficient second))))
     :in-theory
     (e/d (f7x2-add)
          (f7x2-add-of-fix-left f7x2-add-of-fix-right
           f7x2-constant-coefficient f7x2-linear-coefficient
           gfield::f7-add gfield::f7-fix gfield::f7-element-p
           f7-poly-add-normalize-left f7-poly-add-normalize-right
           f7-poly-add f7-raw-add f7-normalize f7-fix-coefficients
           f7-trim-trailing-zeros f7x2-fix f7-poly-remainder))))))

(local
 (defthm f7x2-constant-coefficient-add-fixer-transport
   (equal (f7x2-constant-coefficient
           (f7x2-add (f7x2-fix first) (f7x2-fix second)))
          (f7x2-constant-coefficient (f7x2-add first second)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance f7x2-add-of-fixes))
            :in-theory (disable f7x2-add f7x2-fix
                                f7x2-constant-coefficient)))))

(local
 (defthm f7x2-linear-coefficient-add-fixer-transport
   (equal (f7x2-linear-coefficient
           (f7x2-add (f7x2-fix first) (f7x2-fix second)))
          (f7x2-linear-coefficient (f7x2-add first second)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance f7x2-add-of-fixes))
            :in-theory (disable f7x2-add f7x2-fix
                                f7x2-linear-coefficient)))))

(defthm f7x2-constant-coefficient-of-add
  (equal (f7x2-constant-coefficient (f7x2-add first second))
         (gfield::f7-add (f7x2-constant-coefficient first)
                         (f7x2-constant-coefficient second)))
  :hints
  (("Goal"
    :use ((:instance f7x2-constant-coefficient-add-fixer-transport)
          (:instance f7x2-constant-coefficient-of-add-of-fixes))
    :in-theory
    (e/d ()
         (f7x2-add-of-fix-left f7x2-add-of-fix-right
          f7x2-constant-coefficient f7x2-linear-coefficient
          gfield::f7-add gfield::f7-fix gfield::f7-element-p
          f7-poly-add f7-raw-add f7-normalize f7-fix-coefficients
          f7-trim-trailing-zeros f7x2-fix f7-poly-remainder
          f7-poly-divmod f7-poly-divmod-core f7-poly-division-step
          f7-poly-division-step-core)))))

(defthm f7x2-linear-coefficient-of-add
  (equal (f7x2-linear-coefficient (f7x2-add first second))
         (gfield::f7-add (f7x2-linear-coefficient first)
                         (f7x2-linear-coefficient second)))
  :hints
  (("Goal"
    :use ((:instance f7x2-linear-coefficient-add-fixer-transport)
          (:instance f7x2-linear-coefficient-of-add-of-fixes))
    :in-theory
    (e/d ()
         (f7x2-add-of-fix-left f7x2-add-of-fix-right
          f7x2-constant-coefficient f7x2-linear-coefficient
          gfield::f7-add gfield::f7-fix gfield::f7-element-p
          f7-poly-add f7-raw-add f7-normalize f7-fix-coefficients
          f7-trim-trailing-zeros f7x2-fix f7-poly-remainder
          f7-poly-divmod f7-poly-divmod-core f7-poly-division-step
          f7-poly-division-step-core)))))

(defthm f7x2-add-coefficient-formula-regressions
  (and
   (equal (f7x2-constant-coefficient (f7x2-add first second))
          (gfield::f7-add (f7x2-constant-coefficient first)
                          (f7x2-constant-coefficient second)))
   (equal (f7x2-linear-coefficient (f7x2-add first second))
          (gfield::f7-add (f7x2-linear-coefficient first)
                          (f7x2-linear-coefficient second)))
   (equal (list (f7x2-constant-coefficient (f7x2-add '(1 2) '(3 4)))
                (f7x2-linear-coefficient (f7x2-add '(1 2) '(3 4))))
          '(4 6))
   (equal (f7x2-linear-coefficient (f7x2-add '(1 2) '(3 5))) 0)
   (equal (list (f7x2-constant-coefficient (f7x2-add '(1 2) '(6 3)))
                (f7x2-linear-coefficient (f7x2-add '(1 2) '(6 3))))
          '(0 5))
   (equal (list (f7x2-constant-coefficient (f7x2-add '(1 2) '(6 5)))
                (f7x2-linear-coefficient (f7x2-add '(1 2) '(6 5))))
          '(0 0))
   (equal (list (f7x2-constant-coefficient (f7x2-add nil '(0 3)))
                (f7x2-linear-coefficient (f7x2-add nil '(0 3))))
          '(0 3))
   (equal (list (f7x2-constant-coefficient (f7x2-add '(0 0 1) nil))
                (f7x2-linear-coefficient (f7x2-add '(0 0 1) nil)))
          '(6 0))
   (equal (list (f7x2-constant-coefficient (f7x2-add '(-1 9) '(8 bad)))
                (f7x2-linear-coefficient (f7x2-add '(-1 9) '(8 bad))))
          '(0 2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable f7x2-add))))

; Local adapters connect the bounded fixed-CAR/CADR projections to the
; public projections without exposing reduction or recursive arithmetic.
(local
 (defthm f7x2-constant-projection-of-bounded-neg
   (implies (and (gfield::f7-element-p a) (gfield::f7-element-p b))
            (equal (f7x2-constant-coefficient
                    (f7-poly-neg (f7-normalize (list a b))))
                   (gfield::f7-neg a)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7-poly-neg-of-normalized-two-coefficients)
                  (:instance f7-element-p-of-f7-neg-for-bounded-negation (x a))
                  (:instance f7-element-p-of-f7-neg-for-bounded-negation (x b))
                  (:instance f7x2-element-p-of-normalized-two-coefficients
                             (a (gfield::f7-neg a)) (b (gfield::f7-neg b)))
                  (:instance f7-constant-projection-of-neg-of-normalized-two-coefficients))
            :in-theory
            (e/d (f7x2-constant-coefficient)
                 (f7x2-constant-coefficient-of-fix gfield::f7-neg
                  gfield::f7-fix gfield::f7-element-p f7-poly-neg f7-raw-neg
                  f7-normalize f7-fix-coefficients f7-trim-trailing-zeros
                  f7x2-fix f7-poly-remainder f7-poly-divmod
                  f7-poly-divmod-core f7-poly-division-step
                  f7-poly-division-step-core))))))

(local
 (defthm f7x2-linear-projection-of-bounded-neg
   (implies (and (gfield::f7-element-p a) (gfield::f7-element-p b))
            (equal (f7x2-linear-coefficient
                    (f7-poly-neg (f7-normalize (list a b))))
                   (gfield::f7-neg b)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7-poly-neg-of-normalized-two-coefficients)
                  (:instance f7-element-p-of-f7-neg-for-bounded-negation (x a))
                  (:instance f7-element-p-of-f7-neg-for-bounded-negation (x b))
                  (:instance f7x2-element-p-of-normalized-two-coefficients
                             (a (gfield::f7-neg a)) (b (gfield::f7-neg b)))
                  (:instance f7-linear-projection-of-neg-of-normalized-two-coefficients))
            :in-theory
            (e/d (f7x2-linear-coefficient)
                 (f7x2-linear-coefficient-of-fix gfield::f7-neg
                  gfield::f7-fix gfield::f7-element-p f7-poly-neg f7-raw-neg
                  f7-normalize f7-fix-coefficients f7-trim-trailing-zeros
                  f7x2-fix f7-poly-remainder f7-poly-divmod
                  f7-poly-divmod-core f7-poly-division-step
                  f7-poly-division-step-core))))))

(local
 (defthm f7x2-constant-projection-of-bounded-sub
   (implies (and (gfield::f7-element-p a) (gfield::f7-element-p b)
                 (gfield::f7-element-p c) (gfield::f7-element-p d))
            (equal (f7x2-constant-coefficient
                    (f7-poly-sub (f7-normalize (list a b))
                                 (f7-normalize (list c d))))
                   (gfield::f7-sub a c)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7-poly-sub-of-normalized-two-coefficients)
                  (:instance f7-element-p-of-f7-add-for-raw-shape
                             (x a) (y (gfield::f7-neg c)))
                  (:instance f7-element-p-of-f7-add-for-raw-shape
                             (x b) (y (gfield::f7-neg d)))
                  (:instance f7-element-p-of-f7-neg-for-bounded-negation (x c))
                  (:instance f7-element-p-of-f7-neg-for-bounded-negation (x d))
                  (:instance f7x2-element-p-of-normalized-two-coefficients
                             (a (gfield::f7-sub a c))
                             (b (gfield::f7-sub b d)))
                  (:instance f7-constant-projection-of-sub-of-normalized-two-coefficients))
            :in-theory
            (e/d (f7x2-constant-coefficient gfield::f7-sub)
                 (f7x2-constant-coefficient-of-fix gfield::f7-add
                  gfield::f7-neg gfield::f7-fix gfield::f7-element-p
                  f7-poly-sub f7-poly-neg f7-raw-neg f7-poly-add f7-raw-add
                  f7-normalize f7-fix-coefficients f7-trim-trailing-zeros
                  f7x2-fix f7-poly-remainder f7-poly-divmod
                  f7-poly-divmod-core f7-poly-division-step
                  f7-poly-division-step-core))))))

(local
 (defthm f7x2-linear-projection-of-bounded-sub
   (implies (and (gfield::f7-element-p a) (gfield::f7-element-p b)
                 (gfield::f7-element-p c) (gfield::f7-element-p d))
            (equal (f7x2-linear-coefficient
                    (f7-poly-sub (f7-normalize (list a b))
                                 (f7-normalize (list c d))))
                   (gfield::f7-sub b d)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7-poly-sub-of-normalized-two-coefficients)
                  (:instance f7-element-p-of-f7-add-for-raw-shape
                             (x a) (y (gfield::f7-neg c)))
                  (:instance f7-element-p-of-f7-add-for-raw-shape
                             (x b) (y (gfield::f7-neg d)))
                  (:instance f7-element-p-of-f7-neg-for-bounded-negation (x c))
                  (:instance f7-element-p-of-f7-neg-for-bounded-negation (x d))
                  (:instance f7x2-element-p-of-normalized-two-coefficients
                             (a (gfield::f7-sub a c))
                             (b (gfield::f7-sub b d)))
                  (:instance f7-linear-projection-of-sub-of-normalized-two-coefficients))
            :in-theory
            (e/d (f7x2-linear-coefficient gfield::f7-sub)
                 (f7x2-linear-coefficient-of-fix gfield::f7-add
                  gfield::f7-neg gfield::f7-fix gfield::f7-element-p
                  f7-poly-sub f7-poly-neg f7-raw-neg f7-poly-add f7-raw-add
                  f7-normalize f7-fix-coefficients f7-trim-trailing-zeros
                  f7x2-fix f7-poly-remainder f7-poly-divmod
                  f7-poly-divmod-core f7-poly-division-step
                  f7-poly-division-step-core))))))

(local
 (defthm f7x2-constant-coefficient-of-neg-of-fix
   (equal (f7x2-constant-coefficient (f7x2-neg (f7x2-fix value)))
          (gfield::f7-neg (f7x2-constant-coefficient value)))
   :hints (("Goal"
            :use ((:instance f7x2-fix-reconstruct)
                  (:instance f7-element-p-of-f7x2-constant-coefficient (x value))
                  (:instance f7-element-p-of-f7x2-linear-coefficient (x value))
                  (:instance f7x2-constant-projection-of-bounded-neg
                             (a (f7x2-constant-coefficient value))
                             (b (f7x2-linear-coefficient value))))
            :in-theory (e/d (f7x2-neg)
                            (f7x2-neg-of-fix f7x2-constant-coefficient f7x2-linear-coefficient
                             gfield::f7-neg gfield::f7-fix gfield::f7-element-p
                             f7-poly-neg f7-raw-neg f7-normalize
                             f7-fix-coefficients f7-trim-trailing-zeros
                             f7x2-fix f7-poly-remainder f7-poly-divmod
                             f7-poly-divmod-core f7-poly-division-step
                             f7-poly-division-step-core))))))
(local
 (defthm f7x2-linear-coefficient-of-neg-of-fix
   (equal (f7x2-linear-coefficient (f7x2-neg (f7x2-fix value)))
          (gfield::f7-neg (f7x2-linear-coefficient value)))
   :hints (("Goal"
            :use ((:instance f7x2-fix-reconstruct)
                  (:instance f7-element-p-of-f7x2-constant-coefficient (x value))
                  (:instance f7-element-p-of-f7x2-linear-coefficient (x value))
                  (:instance f7x2-linear-projection-of-bounded-neg
                             (a (f7x2-constant-coefficient value))
                             (b (f7x2-linear-coefficient value))))
            :in-theory (e/d (f7x2-neg)
                            (f7x2-neg-of-fix f7x2-constant-coefficient f7x2-linear-coefficient
                             gfield::f7-neg gfield::f7-fix gfield::f7-element-p
                             f7-poly-neg f7-raw-neg f7-normalize
                             f7-fix-coefficients f7-trim-trailing-zeros
                             f7x2-fix f7-poly-remainder f7-poly-divmod
                             f7-poly-divmod-core f7-poly-division-step
                             f7-poly-division-step-core))))))

(defthm f7x2-constant-coefficient-of-neg
  (equal (f7x2-constant-coefficient (f7x2-neg value))
         (gfield::f7-neg (f7x2-constant-coefficient value)))
  :hints (("Goal" :use ((:instance f7x2-neg-of-fix)
                         (:instance f7x2-constant-coefficient-of-neg-of-fix))
           :in-theory (disable f7x2-neg f7x2-fix
                               f7x2-constant-coefficient gfield::f7-neg))))
(defthm f7x2-linear-coefficient-of-neg
  (equal (f7x2-linear-coefficient (f7x2-neg value))
         (gfield::f7-neg (f7x2-linear-coefficient value)))
  :hints (("Goal" :use ((:instance f7x2-neg-of-fix)
                         (:instance f7x2-linear-coefficient-of-neg-of-fix))
           :in-theory (disable f7x2-neg f7x2-fix
                               f7x2-linear-coefficient gfield::f7-neg))))

(local
 (defthm f7x2-constant-coefficient-of-sub-of-fixes
   (equal (f7x2-constant-coefficient
           (f7x2-sub (f7x2-fix first) (f7x2-fix second)))
          (gfield::f7-sub (f7x2-constant-coefficient first)
                          (f7x2-constant-coefficient second)))
   :hints (("Goal"
            :use ((:instance f7x2-fix-reconstruct (value first))
                  (:instance f7x2-fix-reconstruct (value second))
                  (:instance f7-element-p-of-f7x2-constant-coefficient (x first))
                  (:instance f7-element-p-of-f7x2-linear-coefficient (x first))
                  (:instance f7-element-p-of-f7x2-constant-coefficient (x second))
                  (:instance f7-element-p-of-f7x2-linear-coefficient (x second))
                  (:instance f7x2-constant-projection-of-bounded-sub
                             (a (f7x2-constant-coefficient first))
                             (b (f7x2-linear-coefficient first))
                             (c (f7x2-constant-coefficient second))
                             (d (f7x2-linear-coefficient second))))
            :in-theory (e/d (f7x2-sub)
                            (f7x2-sub-of-fix-left f7x2-sub-of-fix-right
                             f7x2-constant-coefficient f7x2-linear-coefficient
                             gfield::f7-sub gfield::f7-fix gfield::f7-element-p
                             f7-poly-sub f7-poly-neg f7-raw-neg f7-poly-add
                             f7-raw-add f7-normalize f7-fix-coefficients
                             f7-trim-trailing-zeros f7x2-fix f7-poly-remainder
                             f7-poly-divmod f7-poly-divmod-core
                             f7-poly-division-step f7-poly-division-step-core))))))
(local
 (defthm f7x2-linear-coefficient-of-sub-of-fixes
   (equal (f7x2-linear-coefficient
           (f7x2-sub (f7x2-fix first) (f7x2-fix second)))
          (gfield::f7-sub (f7x2-linear-coefficient first)
                          (f7x2-linear-coefficient second)))
   :hints (("Goal"
            :use ((:instance f7x2-fix-reconstruct (value first))
                  (:instance f7x2-fix-reconstruct (value second))
                  (:instance f7-element-p-of-f7x2-constant-coefficient (x first))
                  (:instance f7-element-p-of-f7x2-linear-coefficient (x first))
                  (:instance f7-element-p-of-f7x2-constant-coefficient (x second))
                  (:instance f7-element-p-of-f7x2-linear-coefficient (x second))
                  (:instance f7x2-linear-projection-of-bounded-sub
                             (a (f7x2-constant-coefficient first))
                             (b (f7x2-linear-coefficient first))
                             (c (f7x2-constant-coefficient second))
                             (d (f7x2-linear-coefficient second))))
            :in-theory (e/d (f7x2-sub)
                            (f7x2-sub-of-fix-left f7x2-sub-of-fix-right
                             f7x2-constant-coefficient f7x2-linear-coefficient
                             gfield::f7-sub gfield::f7-fix gfield::f7-element-p
                             f7-poly-sub f7-poly-neg f7-raw-neg f7-poly-add
                             f7-raw-add f7-normalize f7-fix-coefficients
                             f7-trim-trailing-zeros f7x2-fix f7-poly-remainder
                             f7-poly-divmod f7-poly-divmod-core
                             f7-poly-division-step f7-poly-division-step-core))))))

(defthm f7x2-constant-coefficient-of-sub
  (equal (f7x2-constant-coefficient (f7x2-sub first second))
         (gfield::f7-sub (f7x2-constant-coefficient first)
                         (f7x2-constant-coefficient second)))
  :hints (("Goal" :use ((:instance f7x2-sub-of-fixes)
                         (:instance f7x2-constant-coefficient-of-sub-of-fixes))
           :in-theory (disable f7x2-sub-of-fix-left f7x2-sub-of-fix-right
                               f7x2-sub f7x2-fix f7x2-constant-coefficient
                               gfield::f7-sub))))
(defthm f7x2-linear-coefficient-of-sub
  (equal (f7x2-linear-coefficient (f7x2-sub first second))
         (gfield::f7-sub (f7x2-linear-coefficient first)
                         (f7x2-linear-coefficient second)))
  :hints (("Goal" :use ((:instance f7x2-sub-of-fixes)
                         (:instance f7x2-linear-coefficient-of-sub-of-fixes))
           :in-theory (disable f7x2-sub-of-fix-left f7x2-sub-of-fix-right
                               f7x2-sub f7x2-fix f7x2-linear-coefficient
                               gfield::f7-sub))))

(defthm f7x2-negation-and-subtraction-coefficient-formula-regressions
  (and
   (equal (f7x2-constant-coefficient (f7x2-neg value))
          (gfield::f7-neg (f7x2-constant-coefficient value)))
   (equal (f7x2-linear-coefficient (f7x2-neg value))
          (gfield::f7-neg (f7x2-linear-coefficient value)))
   (equal (list (f7x2-constant-coefficient (f7x2-neg '(1 2)))
                (f7x2-linear-coefficient (f7x2-neg '(1 2)))) '(6 5))
   (equal (list (f7x2-constant-coefficient (f7x2-neg '(3)))
                (f7x2-linear-coefficient (f7x2-neg '(3)))) '(4 0))
   (equal (list (f7x2-constant-coefficient (f7x2-neg nil))
                (f7x2-linear-coefficient (f7x2-neg nil))) '(0 0))
   (equal (list (f7x2-constant-coefficient (f7x2-neg '(0 2)))
                (f7x2-linear-coefficient (f7x2-neg '(0 2)))) '(0 5))
   (equal (list (f7x2-constant-coefficient (f7x2-neg '(1 2 3)))
                (f7x2-linear-coefficient (f7x2-neg '(1 2 3)))) '(2 5))
   (equal (list (f7x2-constant-coefficient (f7x2-neg '(-1 9 bad)))
                (f7x2-linear-coefficient (f7x2-neg '(-1 9 bad)))) '(1 5))
   (equal (f7x2-constant-coefficient (f7x2-sub first second))
          (gfield::f7-sub (f7x2-constant-coefficient first)
                          (f7x2-constant-coefficient second)))
   (equal (f7x2-linear-coefficient (f7x2-sub first second))
          (gfield::f7-sub (f7x2-linear-coefficient first)
                          (f7x2-linear-coefficient second)))
   (equal (list (f7x2-constant-coefficient (f7x2-sub '(1 2) '(3 4)))
                (f7x2-linear-coefficient (f7x2-sub '(1 2) '(3 4)))) '(5 5))
   (equal (list (f7x2-constant-coefficient (f7x2-sub '(1 2) '(1 2)))
                (f7x2-linear-coefficient (f7x2-sub '(1 2) '(1 2)))) '(0 0))
   (equal (list (f7x2-constant-coefficient (f7x2-sub '(1 2) '(3 2)))
                (f7x2-linear-coefficient (f7x2-sub '(1 2) '(3 2)))) '(5 0))
   (equal (list (f7x2-constant-coefficient (f7x2-sub '(1 2) '(1 4)))
                (f7x2-linear-coefficient (f7x2-sub '(1 2) '(1 4)))) '(0 5))
   (equal (list (f7x2-constant-coefficient (f7x2-sub '(1) '(3 4)))
                (f7x2-linear-coefficient (f7x2-sub '(1) '(3 4)))) '(5 3))
   (equal (list (f7x2-constant-coefficient (f7x2-sub '(1 2) '(3)))
                (f7x2-linear-coefficient (f7x2-sub '(1 2) '(3)))) '(5 2))
   (equal (list (f7x2-constant-coefficient (f7x2-sub nil '(3 4)))
                (f7x2-linear-coefficient (f7x2-sub nil '(3 4)))) '(4 3))
   (equal (list (f7x2-constant-coefficient (f7x2-sub '(1 2) nil))
                (f7x2-linear-coefficient (f7x2-sub '(1 2) nil))) '(1 2))
   (equal (list (f7x2-constant-coefficient (f7x2-sub '(1 2 3) '(-1 9)))
                (f7x2-linear-coefficient (f7x2-sub '(1 2 3) '(-1 9)))) '(6 0)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable f7x2-neg f7x2-sub))))

(defthm f7-bounded-normalized-addition-regressions
  (and
   (equal (f7-poly-add (f7-normalize '(1 2))
                       (f7-normalize '(3 4)))
          '(4 6))
   (equal (f7-poly-add (f7-normalize '(1 2))
                       (f7-normalize '(3 5)))
          '(4))
   (equal (f7-poly-add (f7-normalize '(1 2))
                       (f7-normalize '(6 3)))
          '(0 5))
   (equal (f7-poly-add (f7-normalize '(1 2))
                       (f7-normalize '(6 5)))
          nil)
   (equal (f7-poly-add (f7-normalize '(1 0))
                       (f7-normalize '(2 3)))
          '(3 3))
   (equal (f7-poly-add nil (f7-normalize '(2 3)))
          '(2 3))
   (equal (f7-poly-add (f7-normalize '(1 0))
                       (f7-normalize '(3 4)))
          '(4 4)))
  :rule-classes nil)

(defthm f7-bounded-normalized-multiplication-regressions
  (and
   (equal (f7x2-fix (f7-poly-mul (f7-normalize '(1 2))
                                  (f7-normalize '(3 4))))
          '(2 3))
   (equal (f7x2-fix (f7-poly-mul (f7-normalize '(2 3))
                                  (f7-normalize '(4 5))))
          '(0 1))
   (equal (f7x2-fix (f7-poly-mul (f7-normalize '(0 2))
                                  (f7-normalize '(0 3))))
          '(1))
   (equal (f7x2-fix (f7-poly-mul (f7-normalize '(1 1))
                                  (f7-normalize '(1 1))))
          '(0 2))
   (equal (f7x2-fix (f7-poly-mul (f7-normalize '(1 1))
                                  (f7-normalize '(1 6))))
          '(2))
   (equal (f7x2-fix (f7-poly-mul (f7-normalize '(3 0))
                                  (f7-normalize '(1 2))))
          '(3 6))
   (equal (f7x2-fix (f7-poly-mul (f7-normalize '(1 2))
                                  (f7-normalize '(3 0))))
          '(3 6))
   (equal (f7x2-fix (f7-poly-mul (f7-normalize '(0 0))
                                  (f7-normalize '(3 4))))
          nil)
   (equal (f7x2-fix (f7-poly-mul (f7-normalize '(3 4))
                                  (f7-normalize '(0 0))))
          nil)
   (equal (f7x2-fix (f7-poly-mul (f7-normalize '(2 0))
                                  (f7-normalize '(4 0))))
          '(1))
   (equal (f7x2-fix (f7-poly-mul (f7-normalize '(0 2))
                                  (f7-normalize '(3 4))))
          '(6 6))
   (equal (f7x2-fix (f7-poly-mul (f7-normalize '(1 2 0))
                                  (f7-normalize '(3 4 0))))
          '(2 3))
   (equal (f7x2-fix (f7-poly-mul (f7-normalize '(-6 9))
                                  (f7-normalize '(10 -3))))
          '(2 3)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance f7x2-fix-of-bounded-normalized-product
                     (a 1) (b 2) (c 3) (d 4))
          (:instance f7x2-fix-of-bounded-normalized-product
                     (a 2) (b 3) (c 4) (d 5))
          (:instance f7x2-fix-of-bounded-normalized-product
                     (a 0) (b 2) (c 0) (d 3))
          (:instance f7x2-fix-of-bounded-normalized-product
                     (a 1) (b 1) (c 1) (d 1))
          (:instance f7x2-fix-of-bounded-normalized-product
                     (a 1) (b 1) (c 1) (d 6))
          (:instance f7x2-fix-of-bounded-normalized-product
                     (a 3) (b 0) (c 1) (d 2))
          (:instance f7x2-fix-of-bounded-normalized-product
                     (a 1) (b 2) (c 3) (d 0))
          (:instance f7x2-fix-of-bounded-normalized-product
                     (a 0) (b 0) (c 3) (d 4))
          (:instance f7x2-fix-of-bounded-normalized-product
                     (a 3) (b 4) (c 0) (d 0))
          (:instance f7x2-fix-of-bounded-normalized-product
                     (a 2) (b 0) (c 4) (d 0))
          (:instance f7x2-fix-of-bounded-normalized-product
                     (a 0) (b 2) (c 3) (d 4)))
    :in-theory
    (disable f7-poly-mul f7-raw-mul f7-raw-scale f7-raw-add
             f7x2-fix f7-poly-remainder f7-poly-divmod
             f7-poly-divmod-core f7-poly-division-step
             f7-poly-division-step-core))))

(defthm f7-bounded-normalized-negation-and-subtraction-regressions
  (and
   (equal (f7-poly-neg (f7-normalize '(1 2))) '(6 5))
   (equal (f7-poly-neg (f7-normalize '(3 0))) '(4))
   (equal (f7-poly-neg (f7-normalize '(0 0))) nil)
   (equal (f7-poly-neg (f7-normalize '(1 0))) '(6))
   (equal (f7-poly-neg (f7-normalize '(0 2))) '(0 5))
   (equal (f7-poly-sub (f7-normalize '(1 2))
                       (f7-normalize '(3 4)))
          '(5 5))
   (equal (f7-poly-sub (f7-normalize '(1 2))
                       (f7-normalize '(1 2)))
          nil)
   (equal (f7-poly-sub (f7-normalize '(1 2))
                       (f7-normalize '(3 2)))
          '(5))
   (equal (f7-poly-sub (f7-normalize '(1 2))
                       (f7-normalize '(1 4)))
          '(0 5))
   (equal (f7-poly-sub (f7-normalize '(1 0))
                       (f7-normalize '(3 4)))
          '(5 3))
   (equal (f7-poly-sub (f7-normalize '(1 2))
                       (f7-normalize '(3 0)))
          '(5 2))
   (equal (f7-poly-sub (f7-normalize '(0 0))
                       (f7-normalize '(3 4)))
          '(4 3))
   (equal (f7-poly-sub (f7-normalize '(1 2))
                       (f7-normalize '(0 0)))
          '(1 2)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance f7-poly-neg-of-normalized-two-coefficients (a 1) (b 2))
          (:instance f7-poly-neg-of-normalized-two-coefficients (a 3) (b 0))
          (:instance f7-poly-neg-of-normalized-two-coefficients (a 0) (b 0))
          (:instance f7-poly-neg-of-normalized-two-coefficients (a 1) (b 0))
          (:instance f7-poly-neg-of-normalized-two-coefficients (a 0) (b 2))
          (:instance f7-poly-sub-of-normalized-two-coefficients
                     (a 1) (b 2) (c 3) (d 4))
          (:instance f7-poly-sub-of-normalized-two-coefficients
                     (a 1) (b 2) (c 1) (d 2))
          (:instance f7-poly-sub-of-normalized-two-coefficients
                     (a 1) (b 2) (c 3) (d 2))
          (:instance f7-poly-sub-of-normalized-two-coefficients
                     (a 1) (b 2) (c 1) (d 4))
          (:instance f7-poly-sub-of-normalized-two-coefficients
                     (a 1) (b 0) (c 3) (d 4))
          (:instance f7-poly-sub-of-normalized-two-coefficients
                     (a 1) (b 2) (c 3) (d 0))
          (:instance f7-poly-sub-of-normalized-two-coefficients
                     (a 0) (b 0) (c 3) (d 4))
          (:instance f7-poly-sub-of-normalized-two-coefficients
                     (a 1) (b 2) (c 0) (d 0)))
    :in-theory
    (disable f7-poly-neg f7-raw-neg f7-poly-sub
             f7-poly-add f7-raw-add f7-poly-remainder
             f7-poly-divmod f7-poly-divmod-core
             f7-poly-division-step f7-poly-division-step-core))))


(assert-event
 (and
  (equal (f7x2-add '(1) '(1)) '(2))
  (equal (f7x2-add '(0 1) '(0 1)) '(0 2))
  (equal (f7x2-add '(1 1) '(1 1)) '(2 2))
  (equal (f7x2-add '(8 1 0) '(1 7))
         (f7x2-add (f7x2-fix '(8 1 0)) (f7x2-fix '(1 7))))
  (equal (f7x2-add '(1 0) '(2))
         (f7x2-add (f7x2-fix '(1 0)) '(2)))
  (equal (f7x2-sub '(8 -1) '(3))
         (f7x2-sub (f7x2-fix '(8 -1)) '(3)))
  (equal (f7x2-neg '(1 2 . bad))
         (f7x2-neg (f7x2-fix '(1 2 . bad))))
  (equal (f7x2-neg '(1 1)) '(6 6))
  (equal (f7x2-sub '(1 1) '(1 1)) nil)
  (equal (f7x2-sub '(0 1) '(1)) '(6 1))
  (equal (f7x2-mul '(0 1) '(0 1)) '(6))
  (equal (f7x2-mul '(0 1) '(1 1)) '(6 1))
  (equal (f7x2-mul '(1 1) '(1 1)) '(0 2))
  (equal (f7x2-mul '(8 -1) '(3 10)) '(6))
  (equal (f7x2-mul '(1 1 0 . bad) '(0 1)) '(6 1))
  (equal (f7x2-mul '(0 0 0 1) '(1 1))
         (f7x2-mul (f7x2-fix '(0 0 0 1)) '(1 1)))))
