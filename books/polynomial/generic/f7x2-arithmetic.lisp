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

; Double negation is reconstructed solely from the public coefficient
; interface.  In particular, the carrier and polynomial implementations stay
; closed: each coefficient calculation is the concrete F7 equation -(-a) =
; fix(a), and the projection-of-fix rules reconcile the right-hand side.
(defthm f7x2-double-negation
  (equal (f7x2-neg (f7x2-neg value))
         (f7x2-fix value))
  :hints
  (("Goal"
    :use ((:instance f7x2-coefficient-extensionality
                     (first (f7x2-neg (f7x2-neg value)))
                     (second (f7x2-fix value)))
          (:instance gfield::f7-double-negation-from-generic-kernel
                     (x (f7x2-constant-coefficient value)))
          (:instance gfield::f7-double-negation-from-generic-kernel
                     (x (f7x2-linear-coefficient value))))
    :in-theory
    (disable f7x2-neg f7x2-fix
             gfield::f7-neg gfield::f7-fix
             f7-poly-add f7-raw-add f7-poly-neg f7-raw-neg
             f7-poly-sub f7-poly-mul f7-raw-mul f7-raw-scale
             f7-normalize f7-fix-coefficients f7-trim-trailing-zeros
             f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
             f7-poly-division-step f7-poly-division-step-core))))

(local
 (defthm f7x2-double-negation-regressions
   (and
    (equal (f7x2-neg (f7x2-neg (f7x2-zero)))
           (f7x2-fix (f7x2-zero)))
    (equal (f7x2-neg (f7x2-neg (f7x2-one)))
           (f7x2-fix (f7x2-one)))
    (equal (f7x2-neg (f7x2-neg '(3))) (f7x2-fix '(3)))
    (equal (f7x2-neg (f7x2-neg '(1 2))) (f7x2-fix '(1 2)))
    (equal (f7x2-neg (f7x2-neg nil)) (f7x2-fix nil))
    (equal (f7x2-neg (f7x2-neg '(1 2 0))) (f7x2-fix '(1 2 0)))
    (equal (f7x2-neg (f7x2-neg '(1 2 3 4))) (f7x2-fix '(1 2 3 4)))
    (equal (f7x2-neg (f7x2-neg '(-1 9))) (f7x2-fix '(-1 9)))
    (equal (f7x2-neg (f7x2-neg '(1/2 -3/2)))
           (f7x2-fix '(1/2 -3/2)))
    (equal (f7x2-neg (f7x2-neg 'bad)) (f7x2-fix 'bad))
    (equal (f7x2-neg (f7x2-neg #\A)) (f7x2-fix #\A))
    (equal (f7x2-neg (f7x2-neg '(bad (also bad))))
           (f7x2-fix '(bad (also bad))))
    (equal (f7x2-neg (f7x2-neg '(1 2 . bad)))
           (f7x2-fix '(1 2 . bad)))
    (equal (f7x2-neg (f7x2-neg (f7x2-fix '(8 -1))))
           (f7x2-fix (f7x2-fix '(8 -1))))
    (equal (f7x2-neg (f7x2-neg '(8 -1 3)))
           (f7x2-fix '(8 -1 3))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable f7x2-double-negation)))))

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

; Multiplication follows the same arbitrary-input path as the six formulas
; above: reconstruct each fixed operand from its two recognized coefficients,
; then consume the bounded convolution-and-reduction projections.
(local
 (defthm f7x2-constant-coefficient-of-mul-of-fixes
   (equal
    (f7x2-constant-coefficient
     (f7x2-mul (f7x2-fix first) (f7x2-fix second)))
    (gfield::f7-sub
     (gfield::f7-mul (f7x2-constant-coefficient first)
                     (f7x2-constant-coefficient second))
     (gfield::f7-mul (f7x2-linear-coefficient first)
                     (f7x2-linear-coefficient second))))
   :hints
   (("Goal"
     :use ((:instance f7x2-fix-reconstruct (value first))
           (:instance f7x2-fix-reconstruct (value second))
           (:instance f7-element-p-of-f7x2-constant-coefficient (x first))
           (:instance f7-element-p-of-f7x2-linear-coefficient (x first))
           (:instance f7-element-p-of-f7x2-constant-coefficient (x second))
           (:instance f7-element-p-of-f7x2-linear-coefficient (x second))
           (:instance f7x2-constant-projection-of-bounded-normalized-product
                      (a (f7x2-constant-coefficient first))
                      (b (f7x2-linear-coefficient first))
                      (c (f7x2-constant-coefficient second))
                      (d (f7x2-linear-coefficient second))))
     :in-theory
     (e/d (f7x2-mul)
          (f7x2-mul-of-fix-left f7x2-mul-of-fix-right
           f7x2-constant-coefficient f7x2-linear-coefficient
           gfield::f7-sub gfield::f7-mul gfield::f7-fix
           gfield::f7-element-p f7-poly-mul f7-raw-mul f7-raw-scale
           f7-raw-add f7-normalize f7-fix-coefficients
           f7-trim-trailing-zeros f7x2-fix f7-poly-remainder
           f7-poly-divmod f7-poly-divmod-core f7-poly-division-step
           f7-poly-division-step-core))))))

(local
 (defthm f7x2-linear-coefficient-of-mul-of-fixes
   (equal
    (f7x2-linear-coefficient
     (f7x2-mul (f7x2-fix first) (f7x2-fix second)))
    (gfield::f7-add
     (gfield::f7-mul (f7x2-constant-coefficient first)
                     (f7x2-linear-coefficient second))
     (gfield::f7-mul (f7x2-linear-coefficient first)
                     (f7x2-constant-coefficient second))))
   :hints
   (("Goal"
     :use ((:instance f7x2-fix-reconstruct (value first))
           (:instance f7x2-fix-reconstruct (value second))
           (:instance f7-element-p-of-f7x2-constant-coefficient (x first))
           (:instance f7-element-p-of-f7x2-linear-coefficient (x first))
           (:instance f7-element-p-of-f7x2-constant-coefficient (x second))
           (:instance f7-element-p-of-f7x2-linear-coefficient (x second))
           (:instance f7x2-linear-projection-of-bounded-normalized-product
                      (a (f7x2-constant-coefficient first))
                      (b (f7x2-linear-coefficient first))
                      (c (f7x2-constant-coefficient second))
                      (d (f7x2-linear-coefficient second))))
     :in-theory
     (e/d (f7x2-mul)
          (f7x2-mul-of-fix-left f7x2-mul-of-fix-right
           f7x2-constant-coefficient f7x2-linear-coefficient
           gfield::f7-add gfield::f7-mul gfield::f7-fix
           gfield::f7-element-p f7-poly-mul f7-raw-mul f7-raw-scale
           f7-raw-add f7-normalize f7-fix-coefficients
           f7-trim-trailing-zeros f7x2-fix f7-poly-remainder
           f7-poly-divmod f7-poly-divmod-core f7-poly-division-step
           f7-poly-division-step-core))))))

(defthm f7x2-constant-coefficient-of-mul
  (equal
   (f7x2-constant-coefficient (f7x2-mul first second))
   (gfield::f7-sub
    (gfield::f7-mul (f7x2-constant-coefficient first)
                    (f7x2-constant-coefficient second))
    (gfield::f7-mul (f7x2-linear-coefficient first)
                    (f7x2-linear-coefficient second))))
  :hints (("Goal"
           :use ((:instance f7x2-mul-of-fixes)
                 (:instance f7x2-constant-coefficient-of-mul-of-fixes))
           :in-theory
           (disable f7x2-mul-of-fix-left f7x2-mul-of-fix-right
                    f7x2-mul f7x2-fix f7x2-constant-coefficient
                    f7x2-linear-coefficient gfield::f7-sub
                    gfield::f7-mul))))

(defthm f7x2-linear-coefficient-of-mul
  (equal
   (f7x2-linear-coefficient (f7x2-mul first second))
   (gfield::f7-add
    (gfield::f7-mul (f7x2-constant-coefficient first)
                    (f7x2-linear-coefficient second))
    (gfield::f7-mul (f7x2-linear-coefficient first)
                    (f7x2-constant-coefficient second))))
  :hints (("Goal"
           :use ((:instance f7x2-mul-of-fixes)
                 (:instance f7x2-linear-coefficient-of-mul-of-fixes))
           :in-theory
           (disable f7x2-mul-of-fix-left f7x2-mul-of-fix-right
                    f7x2-mul f7x2-fix f7x2-constant-coefficient
                    f7x2-linear-coefficient gfield::f7-add
                    gfield::f7-mul))))

; Operational constants are proved only through the public coefficient
; interface.  In particular, neither carrier operation nor the polynomial
; implementation below it is enabled by these proofs.
(defthm f7x2-add-zero-left
  (equal (f7x2-add (f7x2-zero) value)
         (f7x2-fix value))
  :hints (("Goal"
           :use ((:instance f7x2-coefficient-extensionality
                            (first (f7x2-add (f7x2-zero) value))
                            (second (f7x2-fix value))))
           :in-theory (disable f7x2-add f7x2-fix))))

(defthm f7x2-add-zero-right
  (equal (f7x2-add value (f7x2-zero))
         (f7x2-fix value))
  :hints (("Goal"
           :use ((:instance f7x2-coefficient-extensionality
                            (first (f7x2-add value (f7x2-zero)))
                            (second (f7x2-fix value))))
           :in-theory (disable f7x2-add f7x2-fix))))

; Additive inverses likewise stay entirely at the public coefficient
; interface.  The two orientations deliberately use the corresponding
; concrete F7 rule rather than obtaining either result by commutativity.
(defthm f7x2-add-inverse-left
  (equal (f7x2-add (f7x2-neg value) value)
         (f7x2-zero))
  :hints (("Goal"
           :use ((:instance f7x2-coefficient-extensionality
                            (first (f7x2-add (f7x2-neg value) value))
                            (second (f7x2-zero)))
                 (:instance gfield::f7-add-inverse-left
                            (value (f7x2-constant-coefficient value)))
                 (:instance gfield::f7-add-inverse-left
                            (value (f7x2-linear-coefficient value))))
           :in-theory (disable f7x2-add f7x2-neg f7x2-fix))))

(defthm f7x2-add-inverse-right
  (equal (f7x2-add value (f7x2-neg value))
         (f7x2-zero))
  :hints (("Goal"
           :use ((:instance f7x2-coefficient-extensionality
                            (first (f7x2-add value (f7x2-neg value)))
                            (second (f7x2-zero)))
                 (:instance f7-add-inverse-right-for-subtraction
                            (x (f7x2-constant-coefficient value)))
                 (:instance f7-add-inverse-right-for-subtraction
                            (x (f7x2-linear-coefficient value))))
           :in-theory (disable f7x2-add f7x2-neg f7x2-fix))))

; Subtraction is used as addition to negation only as a local proof bridge.
; Keeping this equality non-rewriting avoids globally expanding the smaller
; F7X2-SUB term and lets the specialized rules below determine its normal
; forms without overlap from a general subtraction rewrite.
(local
 (defthm f7x2-sub-as-add-neg
   (equal (f7x2-sub first second)
          (f7x2-add first (f7x2-neg second)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7x2-coefficient-extensionality
                             (first (f7x2-sub first second))
                             (second (f7x2-add first (f7x2-neg second)))))
            :in-theory (e/d (gfield::f7-sub)
                            (f7x2-sub f7x2-add f7x2-neg f7x2-fix
                             gfield::f7-add gfield::f7-neg))))))

(local
 (defthm f7x2-neg-zero
   (equal (f7x2-neg (f7x2-zero)) (f7x2-zero))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f7x2-coefficient-extensionality
                             (first (f7x2-neg (f7x2-zero)))
                             (second (f7x2-zero))))
            :in-theory (disable f7x2-neg f7x2-fix)))))

(defthm f7x2-sub-zero-right
  (equal (f7x2-sub value (f7x2-zero))
         (f7x2-fix value))
  :hints (("Goal"
           :use ((:instance f7x2-sub-as-add-neg
                            (first value) (second (f7x2-zero)))
                 (:instance f7x2-neg-zero)
                 (:instance f7x2-add-zero-right))
           :in-theory (disable f7x2-sub f7x2-add f7x2-neg f7x2-fix))))

(defthm f7x2-sub-zero-left
  (equal (f7x2-sub (f7x2-zero) value)
         (f7x2-neg value))
  :hints (("Goal"
           :use ((:instance f7x2-sub-as-add-neg
                            (first (f7x2-zero)) (second value))
                 (:instance f7x2-add-zero-left
                            (value (f7x2-neg value)))
                 (:instance f7x2-fix-when-f7x2-element-p
                            (x (f7x2-neg value)))
                 (:instance f7x2-element-p-of-f7x2-neg))
           :in-theory (disable f7x2-sub f7x2-add f7x2-neg f7x2-fix))))

(defthm f7x2-sub-self
  (equal (f7x2-sub value value)
         (f7x2-zero))
  :hints (("Goal"
           :use ((:instance f7x2-sub-as-add-neg
                            (first value) (second value))
                 (:instance f7x2-add-inverse-right))
           :in-theory (disable f7x2-sub f7x2-add f7x2-neg f7x2-fix))))

; Addition commutativity is reconstructed entirely through the public
; coefficient interface.  ACL2 treats this ordinary rewrite rule as
; permutative, so its loop stopper exchanges operands only toward the stable
; term order rather than repeatedly swapping them.
(defthm f7x2-add-commutative
  (equal (f7x2-add first second)
         (f7x2-add second first))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints
  (("Goal"
    :use ((:instance f7x2-coefficient-extensionality
                     (first (f7x2-add first second))
                     (second (f7x2-add second first)))
          (:instance f7-add-commutative-for-polynomial-structure
                     (x (f7x2-constant-coefficient first))
                     (y (f7x2-constant-coefficient second)))
          (:instance f7-add-commutative-for-polynomial-structure
                     (x (f7x2-linear-coefficient first))
                     (y (f7x2-linear-coefficient second))))
    :in-theory
    (disable f7x2-add f7x2-fix
             gfield::f7-add gfield::f7-fix
             f7-poly-add f7-raw-add f7-poly-neg f7-raw-neg
             f7-poly-sub f7-poly-mul f7-raw-mul f7-raw-scale
             f7-normalize f7-fix-coefficients f7-trim-trailing-zeros
             f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
             f7-poly-division-step f7-poly-division-step-core))))

(local
 (defthm f7x2-add-commutative-regressions
   (and
    (equal (f7x2-add (f7x2-zero) (f7x2-one))
           (f7x2-add (f7x2-one) (f7x2-zero)))
    (equal (f7x2-add '(2) '(5)) (f7x2-add '(5) '(2)))
    (equal (f7x2-add '(3) '(1 4)) (f7x2-add '(1 4) '(3)))
    (equal (f7x2-add '(1 2) '(3 4)) (f7x2-add '(3 4) '(1 2)))
    (equal (f7x2-add nil '(1 2)) (f7x2-add '(1 2) nil))
    (equal (f7x2-add '(1 2 0) '(3)) (f7x2-add '(3) '(1 2 0)))
    (equal (f7x2-add '(1 2 3 4) '(0 5))
           (f7x2-add '(0 5) '(1 2 3 4)))
    (equal (f7x2-add '(-1 9) '(8 -3)) (f7x2-add '(8 -3) '(-1 9)))
    (equal (f7x2-add '(1/2 -3/2) '(2/3 5/4))
           (f7x2-add '(2/3 5/4) '(1/2 -3/2)))
    (equal (f7x2-add 'bad #\A) (f7x2-add #\A 'bad))
    (equal (f7x2-add '(bad (also bad)) '(1 2))
           (f7x2-add '(1 2) '(bad (also bad))))
    (equal (f7x2-add '(1 2 . bad) '(3 4))
           (f7x2-add '(3 4) '(1 2 . bad)))
    (equal (f7x2-add (f7x2-fix '(10 -3 8)) (f7x2-fix '(1 9)))
           (f7x2-add (f7x2-fix '(1 9)) (f7x2-fix '(10 -3 8))))
    (equal (f7x2-add '(10 -3 8) '(1 2))
           (f7x2-add '(1 2) '(10 -3 8)))
    (equal (f7x2-add 'bad '(1 2)) (f7x2-add '(1 2) 'bad))
    (equal (f7x2-add '(1 2) '(bad 9)) (f7x2-add '(bad 9) '(1 2)))
    (equal (f7x2-add '(3 4) '(3 4)) (f7x2-add '(3 4) '(3 4))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable f7x2-add-commutative)))))

; Addition associativity is likewise reconstructed through the two public
; coefficient projections.  Its ordinary rewrite orientation removes one
; left-nested addition, while the permutative commutativity rule above remains
; governed by ACL2's loop stopper.
(defthm f7x2-add-associative
  (equal (f7x2-add (f7x2-add first second) third)
         (f7x2-add first (f7x2-add second third)))
  :hints
  (("Goal"
    :use ((:instance f7x2-coefficient-extensionality
                     (first (f7x2-add (f7x2-add first second) third))
                     (second (f7x2-add first (f7x2-add second third))))
          (:instance f7-add-associative-for-polynomial-structure
                     (x (f7x2-constant-coefficient first))
                     (y (f7x2-constant-coefficient second))
                     (z (f7x2-constant-coefficient third)))
          (:instance f7-add-associative-for-polynomial-structure
                     (x (f7x2-linear-coefficient first))
                     (y (f7x2-linear-coefficient second))
                     (z (f7x2-linear-coefficient third))))
    :in-theory
    (disable f7x2-add f7x2-fix f7x2-add-commutative
             f7-add-associative-for-polynomial-structure
             f7-add-commutative-for-polynomial-structure
             gfield::f7-add gfield::f7-fix
             f7-poly-add f7-raw-add f7-poly-neg f7-raw-neg
             f7-poly-sub f7-poly-mul f7-raw-mul f7-raw-scale
             f7-normalize f7-fix-coefficients f7-trim-trailing-zeros
             f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
             f7-poly-division-step f7-poly-division-step-core))))

; Left cancellation is stated over fixed representatives because F7X2-ADD is
; total on all ACL2 objects and deliberately identifies malformed or
; noncanonical presentations.  The forward direction projects sum equality
; onto the two public coefficients and uses concrete F7 cancellation; the
; reverse direction transports equality through the public right-operand
; fixer compatibility rule.
(local
 (defthm f7x2-add-equality-implies-constant-equality
   (implies (equal (f7x2-add common first)
                   (f7x2-add common second))
            (equal (f7x2-constant-coefficient
                    (f7x2-add common first))
                   (f7x2-constant-coefficient
                    (f7x2-add common second))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (disable f7x2-add f7x2-fix
                                f7x2-add-commutative f7x2-add-associative
                                f7x2-constant-coefficient-of-add
                                f7x2-constant-coefficient)))))

(local
 (defthm f7x2-add-equality-implies-linear-equality
   (implies (equal (f7x2-add common first)
                   (f7x2-add common second))
            (equal (f7x2-linear-coefficient
                    (f7x2-add common first))
                   (f7x2-linear-coefficient
                    (f7x2-add common second))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (disable f7x2-add f7x2-fix
                                f7x2-add-commutative f7x2-add-associative
                                f7x2-linear-coefficient-of-add
                                f7x2-linear-coefficient)))))

(defthm f7x2-add-cancel-left
  (equal (equal (f7x2-add common first)
                (f7x2-add common second))
         (equal (f7x2-fix first)
                (f7x2-fix second)))
  :hints
  (("Goal"
    :cases ((equal (f7x2-add common first)
                   (f7x2-add common second)))
    :use ((:instance f7x2-fix-coefficient-extensionality
                     (first first) (second second))
          (:instance f7x2-add-equality-implies-constant-equality)
          (:instance f7x2-add-equality-implies-linear-equality)
          (:instance gfield::f7-add-cancel-left
                     (common (f7x2-constant-coefficient common))
                     (first (f7x2-constant-coefficient first))
                     (second (f7x2-constant-coefficient second)))
          (:instance gfield::f7-add-cancel-left
                     (common (f7x2-linear-coefficient common))
                     (first (f7x2-linear-coefficient first))
                     (second (f7x2-linear-coefficient second)))
          (:instance f7-element-p-of-f7x2-constant-coefficient (x first))
          (:instance f7-element-p-of-f7x2-constant-coefficient (x second))
          (:instance f7-element-p-of-f7x2-linear-coefficient (x first))
          (:instance f7-element-p-of-f7x2-linear-coefficient (x second))
          (:instance f7x2-add-of-fix-right
                     (first common) (second first))
          (:instance f7x2-add-of-fix-right
                     (first common) (second second))
          (:instance f7x2-add-of-fixes
                     (first common) (second first))
          (:instance f7x2-add-of-fixes
                     (first common) (second second)))
    :in-theory
    (disable f7x2-add f7x2-fix f7x2-constant-coefficient
             f7x2-linear-coefficient f7x2-add-of-fix-left
             f7x2-add-of-fix-right f7x2-add-commutative
             f7x2-add-associative gfield::f7-add gfield::f7-fix
             f7-poly-add f7-raw-add f7-poly-neg f7-raw-neg
             f7-poly-sub f7-poly-mul f7-raw-mul f7-raw-scale
             f7-normalize f7-fix-coefficients f7-trim-trailing-zeros
             f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
             f7-poly-division-step f7-poly-division-step-core))))

(local
 (defthm f7x2-add-cancel-left-regressions
   (and
    (equal (equal (f7x2-add (f7x2-zero) (f7x2-zero))
                         (f7x2-add (f7x2-zero) (f7x2-one)))
           (equal (f7x2-fix (f7x2-zero)) (f7x2-fix (f7x2-one))))
    (equal (equal (f7x2-add '(3) '(2)) (f7x2-add '(3) '(2)))
           (equal (f7x2-fix '(2)) (f7x2-fix '(2))))
    (equal (equal (f7x2-add '(3 4) '(1 2)) (f7x2-add '(3 4) '(5 6)))
           (equal (f7x2-fix '(1 2)) (f7x2-fix '(5 6))))
    ; The raw operands differ, but their fixed representatives are equal.
    (equal (equal (f7x2-add '(1 2) '(3 4 0)) (f7x2-add '(1 2) '(3 4)))
           (equal (f7x2-fix '(3 4 0)) (f7x2-fix '(3 4))))
    (equal (equal (f7x2-add nil nil) (f7x2-add nil '(0)))
           (equal (f7x2-fix nil) (f7x2-fix '(0))))
    (equal (equal (f7x2-add '(1 2 3 4) '(-1 9))
                  (f7x2-add '(1 2 3 4) '(6 2)))
           (equal (f7x2-fix '(-1 9)) (f7x2-fix '(6 2))))
    (equal (equal (f7x2-add '(1/2 -3/2) '(2/3 5/4))
                  (f7x2-add '(1/2 -3/2) '(2/3 5/4)))
           (equal (f7x2-fix '(2/3 5/4)) (f7x2-fix '(2/3 5/4))))
    (equal (equal (f7x2-add 'common 'symbol) (f7x2-add 'common #\A))
           (equal (f7x2-fix 'symbol) (f7x2-fix #\A)))
    (equal (equal (f7x2-add "common" '(bad "value"))
                  (f7x2-add "common" '(#\Z other)))
           (equal (f7x2-fix '(bad "value"))
                  (f7x2-fix '(#\Z other))))
    (equal (equal (f7x2-add '(1 . tail) '(2 . bad))
                  (f7x2-add '(1 . tail) '(2)))
           (equal (f7x2-fix '(2 . bad)) (f7x2-fix '(2))))
    (equal (equal (f7x2-add (f7x2-fix '(10 -3 8)) '(1 2))
                  (f7x2-add (f7x2-fix '(10 -3 8)) '(8 9)))
           (equal (f7x2-fix '(1 2)) (f7x2-fix '(8 9))))
    (equal (equal (f7x2-add '(bad 9) '(1 2))
                  (f7x2-add '(bad 9) '(1 2 0 0)))
           (equal (f7x2-fix '(1 2)) (f7x2-fix '(1 2 0 0))))
    (equal (equal (f7x2-add '(3 4) 'bad) (f7x2-add '(3 4) nil))
           (equal (f7x2-fix 'bad) (f7x2-fix nil)))
    (equal (equal (f7x2-add (f7x2-zero) '(2 3))
                  (f7x2-add (f7x2-zero) (f7x2-neg '(2 3))))
           (equal (f7x2-fix '(2 3)) (f7x2-fix (f7x2-neg '(2 3))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable f7x2-add-cancel-left)))))

; Right cancellation is only the public left-cancellation theorem after two
; explicit operand exchanges.  Keep commutativity disabled so that no
; permutative rewriting is left to theory search.
(defthm f7x2-add-cancel-right
  (equal (equal (f7x2-add first common)
                (f7x2-add second common))
         (equal (f7x2-fix first)
                (f7x2-fix second)))
  :hints
  (("Goal"
    :use ((:instance f7x2-add-commutative
                     (first first) (second common))
          (:instance f7x2-add-commutative
                     (first second) (second common))
          (:instance f7x2-add-cancel-left
                     (common common) (first first) (second second)))
    :in-theory
    (disable f7x2-add-cancel-left f7x2-add-commutative
             f7x2-add f7x2-fix
             gfield::f7-add gfield::f7-fix
             f7-poly-add f7-raw-add f7-poly-neg f7-raw-neg
             f7-poly-sub f7-poly-mul f7-raw-mul f7-raw-scale
             f7-normalize f7-fix-coefficients f7-trim-trailing-zeros
             f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
             f7-poly-division-step f7-poly-division-step-core))))

(local
 (defthm f7x2-add-cancel-right-regressions
   (and
    ; Equal canonical operands.
    (equal (equal (f7x2-add '(2 3) '(4 5))
                  (f7x2-add '(2 3) '(4 5)))
           (equal (f7x2-fix '(2 3)) (f7x2-fix '(2 3))))
    ; Unequal canonical operands.
    (equal (equal (f7x2-add '(1 2) '(3 4))
                  (f7x2-add '(5 6) '(3 4)))
           (equal (f7x2-fix '(1 2)) (f7x2-fix '(5 6))))
    ; Malformed and noncanonical operands.
    (equal (equal (f7x2-add '(bad 9 . tail) '(8 -3 0))
                  (f7x2-add #\A '(8 -3 0)))
           (equal (f7x2-fix '(bad 9 . tail)) (f7x2-fix #\A)))
    ; The raw operands differ, but their fixed representatives are equal.
    (equal (equal (f7x2-add '(3 4 0) '(1 2))
                  (f7x2-add '(3 4) '(1 2)))
           (equal (f7x2-fix '(3 4 0)) (f7x2-fix '(3 4)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable f7x2-add-cancel-right)))))

(local
 (defthm f7x2-add-associative-regressions
   (and
    (equal (f7x2-add (f7x2-add (f7x2-zero) (f7x2-one)) (f7x2-zero))
           (f7x2-add (f7x2-zero) (f7x2-add (f7x2-one) (f7x2-zero))))
    (equal (f7x2-add (f7x2-add '(1) '(2)) '(3))
           (f7x2-add '(1) (f7x2-add '(2) '(3))))
    (equal (f7x2-add (f7x2-add '(3) '(1 4)) '(2))
           (f7x2-add '(3) (f7x2-add '(1 4) '(2))))
    (equal (f7x2-add (f7x2-add '(1 2) '(3 4)) '(5 6))
           (f7x2-add '(1 2) (f7x2-add '(3 4) '(5 6))))
    (equal (f7x2-add (f7x2-add '(3 4) '(3 4)) '(3 4))
           (f7x2-add '(3 4) (f7x2-add '(3 4) '(3 4))))
    (equal (f7x2-add (f7x2-add nil nil) '(1 2))
           (f7x2-add nil (f7x2-add nil '(1 2))))
    (equal (f7x2-add (f7x2-add '(1 2 0) '(3)) '(4 5 6 7))
           (f7x2-add '(1 2 0) (f7x2-add '(3) '(4 5 6 7))))
    (equal (f7x2-add (f7x2-add '(-1 9) '(8 -3)) '(15 22))
           (f7x2-add '(-1 9) (f7x2-add '(8 -3) '(15 22))))
    (equal (f7x2-add (f7x2-add '(1/2 -3/2) '(2/3 5/4)) '(7/3 -2/5))
           (f7x2-add '(1/2 -3/2) (f7x2-add '(2/3 5/4) '(7/3 -2/5))))
    (equal (f7x2-add (f7x2-add 'bad #\A) "atom")
           (f7x2-add 'bad (f7x2-add #\A "atom")))
    (equal (f7x2-add (f7x2-add '(bad (also bad)) '(1 2)) '(#\Z symbol))
           (f7x2-add '(bad (also bad)) (f7x2-add '(1 2) '(#\Z symbol))))
    (equal (f7x2-add (f7x2-add '(1 2 . bad) '(3 4)) '(5 . tail))
           (f7x2-add '(1 2 . bad) (f7x2-add '(3 4) '(5 . tail))))
    (equal (f7x2-add (f7x2-add (f7x2-fix '(10 -3 8))
                                (f7x2-fix '(1 9)))
                      (f7x2-fix '(4 5)))
           (f7x2-add (f7x2-fix '(10 -3 8))
                     (f7x2-add (f7x2-fix '(1 9)) (f7x2-fix '(4 5)))))
    (equal (f7x2-add (f7x2-add '(10 -3 8) '(1 2)) 'bad)
           (f7x2-add '(10 -3 8) (f7x2-add '(1 2) 'bad)))
    (equal (f7x2-add (f7x2-add 'bad '(1 2)) '(10 -3 8))
           (f7x2-add 'bad (f7x2-add '(1 2) '(10 -3 8))))
    (equal (f7x2-add (f7x2-add '(1 2) 'bad) '(3 4))
           (f7x2-add '(1 2) (f7x2-add 'bad '(3 4))))
    (equal (f7x2-add (f7x2-add (f7x2-zero) '(2 3)) '(4 5))
           (f7x2-add (f7x2-zero) (f7x2-add '(2 3) '(4 5))))
    (equal (f7x2-add (f7x2-add '(2 3) (f7x2-neg '(2 3))) '(4 5))
           (f7x2-add '(2 3) (f7x2-add (f7x2-neg '(2 3)) '(4 5))))
    (equal (f7x2-add (f7x2-add '(4 5) '(2 3)) (f7x2-neg '(2 3)))
           (f7x2-add '(4 5) (f7x2-add '(2 3) (f7x2-neg '(2 3))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable f7x2-add-associative)))))

(defthm f7x2-mul-one-left
  (equal (f7x2-mul (f7x2-one) value)
         (f7x2-fix value))
  :hints (("Goal"
           :use ((:instance f7x2-coefficient-extensionality
                            (first (f7x2-mul (f7x2-one) value))
                            (second (f7x2-fix value)))
                 (:instance f7x2-constant-coefficient-of-mul
                            (first (f7x2-one)) (second value))
                 (:instance f7x2-linear-coefficient-of-mul
                            (first (f7x2-one)) (second value))
                 (:instance gfield::f7-mul-one-left
                            (x (f7x2-constant-coefficient value)))
                 (:instance gfield::f7-mul-one-left
                            (x (f7x2-linear-coefficient value))))
           :in-theory (disable f7x2-mul f7x2-fix))))

(defthm f7x2-mul-one-right
  (equal (f7x2-mul value (f7x2-one))
         (f7x2-fix value))
  :hints (("Goal"
           :use ((:instance f7x2-coefficient-extensionality
                            (first (f7x2-mul value (f7x2-one)))
                            (second (f7x2-fix value)))
                 (:instance f7x2-constant-coefficient-of-mul
                            (first value) (second (f7x2-one)))
                 (:instance f7x2-linear-coefficient-of-mul
                            (first value) (second (f7x2-one)))
                 (:instance gfield::f7-mul-one-right
                            (x (f7x2-constant-coefficient value)))
                 (:instance gfield::f7-mul-one-right
                            (x (f7x2-linear-coefficient value))))
           :in-theory (disable f7x2-mul f7x2-fix))))

(defthm f7x2-mul-zero-left
  (equal (f7x2-mul (f7x2-zero) value)
         (f7x2-zero))
  :hints (("Goal"
           :use ((:instance f7x2-coefficient-extensionality
                            (first (f7x2-mul (f7x2-zero) value))
                            (second (f7x2-zero)))
                 (:instance f7x2-constant-coefficient-of-mul
                            (first (f7x2-zero)) (second value))
                 (:instance f7x2-linear-coefficient-of-mul
                            (first (f7x2-zero)) (second value))
                 (:instance gfield::f7-mul-zero-left
                            (value (f7x2-constant-coefficient value)))
                 (:instance gfield::f7-mul-zero-left
                            (value (f7x2-linear-coefficient value))))
           :in-theory (disable f7x2-mul f7x2-fix))))

(defthm f7x2-mul-zero-right
  (equal (f7x2-mul value (f7x2-zero))
         (f7x2-zero))
  :hints (("Goal"
           :use ((:instance f7x2-coefficient-extensionality
                            (first (f7x2-mul value (f7x2-zero)))
                            (second (f7x2-zero)))
                 (:instance f7x2-constant-coefficient-of-mul
                            (first value) (second (f7x2-zero)))
                 (:instance f7x2-linear-coefficient-of-mul
                            (first value) (second (f7x2-zero)))
                 (:instance gfield::f7-mul-zero-right
                            (value (f7x2-constant-coefficient value)))
                 (:instance gfield::f7-mul-zero-right
                            (value (f7x2-linear-coefficient value))))
           :in-theory (disable f7x2-mul f7x2-fix))))

(local
 (defthm f7x2-multiplicative-constant-regressions
   (and
    (equal (f7x2-mul (f7x2-one) (f7x2-zero))
           (f7x2-fix (f7x2-zero)))
    (equal (f7x2-mul (f7x2-one) (f7x2-one))
           (f7x2-fix (f7x2-one)))
    (equal (f7x2-mul (f7x2-one) '(5)) (f7x2-fix '(5)))
    (equal (f7x2-mul '(3 4) (f7x2-one)) (f7x2-fix '(3 4)))
    (equal (f7x2-mul (f7x2-one) nil) (f7x2-fix nil))
    (equal (f7x2-mul '(1 2 0) (f7x2-one)) (f7x2-fix '(1 2 0)))
    (equal (f7x2-mul (f7x2-one) '(1 2 3 4))
           (f7x2-fix '(1 2 3 4)))
    (equal (f7x2-mul '(-1 9) (f7x2-one)) (f7x2-fix '(-1 9)))
    (equal (f7x2-mul (f7x2-one) '(1/2 3/4))
           (f7x2-fix '(1/2 3/4)))
    (equal (f7x2-mul 'bad (f7x2-one)) (f7x2-fix 'bad))
    (equal (f7x2-mul (f7x2-one) '(bad 9)) (f7x2-fix '(bad 9)))
    (equal (f7x2-mul '(1 2 . bad) (f7x2-one))
           (f7x2-fix '(1 2 . bad)))
    (equal (f7x2-mul (f7x2-one) (f7x2-fix '(10 -3 8)))
           (f7x2-fix '(10 -3 8)))
    (equal (f7x2-mul (f7x2-zero) (f7x2-zero)) (f7x2-zero))
    (equal (f7x2-mul (f7x2-one) (f7x2-zero)) (f7x2-zero))
    (equal (f7x2-mul (f7x2-zero) '(5)) (f7x2-zero))
    (equal (f7x2-mul '(3 4) (f7x2-zero)) (f7x2-zero))
    (equal (f7x2-mul (f7x2-zero) nil) (f7x2-zero))
    (equal (f7x2-mul '(1 2 0) (f7x2-zero)) (f7x2-zero))
    (equal (f7x2-mul (f7x2-zero) '(1 2 3 4)) (f7x2-zero))
    (equal (f7x2-mul '(-1 9) (f7x2-zero)) (f7x2-zero))
    (equal (f7x2-mul (f7x2-zero) '(1/2 3/4)) (f7x2-zero))
    (equal (f7x2-mul 'bad (f7x2-zero)) (f7x2-zero))
    (equal (f7x2-mul (f7x2-zero) '(bad 9)) (f7x2-zero))
    (equal (f7x2-mul '(1 2 . bad) (f7x2-zero)) (f7x2-zero))
    (equal (f7x2-mul (f7x2-zero) (f7x2-fix '(10 -3 8)))
           (f7x2-zero)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable f7x2-mul f7x2-fix)))))

(local
 (defthm f7x2-add-zero-regressions
   (and
    (equal (f7x2-add (f7x2-zero) '(3 4)) '(3 4))
    (equal (f7x2-add '(3 4) (f7x2-zero)) '(3 4))
    (equal (f7x2-add (f7x2-zero) nil) (f7x2-fix nil))
    (equal (f7x2-add (f7x2-zero) '(5)) (f7x2-fix '(5)))
    (equal (f7x2-add '(1 2 0) (f7x2-zero)) (f7x2-fix '(1 2 0)))
    (equal (f7x2-add (f7x2-zero) '(1 2 3 4))
           (f7x2-fix '(1 2 3 4)))
    (equal (f7x2-add '(-1 9) (f7x2-zero)) (f7x2-fix '(-1 9)))
    (equal (f7x2-add (f7x2-zero) '(bad 9)) (f7x2-fix '(bad 9)))
    (equal (f7x2-add '(1 2 . bad) (f7x2-zero))
           (f7x2-fix '(1 2 . bad)))
    (equal (f7x2-add (f7x2-zero) 'bad) (f7x2-fix 'bad))
    (equal (f7x2-add (f7x2-zero) (f7x2-zero)) (f7x2-zero))
    (equal (f7x2-add (f7x2-one) (f7x2-zero)) (f7x2-one)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable f7x2-add f7x2-fix)))))

(local
 (defthm f7x2-additive-inverse-regressions
   (and
    (equal (f7x2-add (f7x2-neg (f7x2-zero)) (f7x2-zero)) (f7x2-zero))
    (equal (f7x2-add (f7x2-zero) (f7x2-neg (f7x2-zero))) (f7x2-zero))
    (equal (f7x2-add (f7x2-neg (f7x2-one)) (f7x2-one)) (f7x2-zero))
    (equal (f7x2-add (f7x2-one) (f7x2-neg (f7x2-one))) (f7x2-zero))
    (equal (f7x2-add (f7x2-neg '(5)) '(5)) (f7x2-zero))
    (equal (f7x2-add '(5) (f7x2-neg '(5))) (f7x2-zero))
    (equal (f7x2-add (f7x2-neg '(3 4)) '(3 4)) (f7x2-zero))
    (equal (f7x2-add '(3 4) (f7x2-neg '(3 4))) (f7x2-zero))
    (equal (f7x2-add (f7x2-neg nil) nil) (f7x2-zero))
    (equal (f7x2-add nil (f7x2-neg nil)) (f7x2-zero))
    (equal (f7x2-add (f7x2-neg '(1 2 0)) '(1 2 0)) (f7x2-zero))
    (equal (f7x2-add '(1 2 0) (f7x2-neg '(1 2 0))) (f7x2-zero))
    (equal (f7x2-add (f7x2-neg '(1 2 3 4)) '(1 2 3 4)) (f7x2-zero))
    (equal (f7x2-add '(1 2 3 4) (f7x2-neg '(1 2 3 4))) (f7x2-zero))
    (equal (f7x2-add (f7x2-neg '(-1 9)) '(-1 9)) (f7x2-zero))
    (equal (f7x2-add '(-1 9) (f7x2-neg '(-1 9))) (f7x2-zero))
    (equal (f7x2-add (f7x2-neg '(1/2 3/4)) '(1/2 3/4)) (f7x2-zero))
    (equal (f7x2-add '(1/2 3/4) (f7x2-neg '(1/2 3/4))) (f7x2-zero))
    (equal (f7x2-add (f7x2-neg 'bad) 'bad) (f7x2-zero))
    (equal (f7x2-add 'bad (f7x2-neg 'bad)) (f7x2-zero))
    (equal (f7x2-add (f7x2-neg '(bad 9)) '(bad 9)) (f7x2-zero))
    (equal (f7x2-add '(bad 9) (f7x2-neg '(bad 9))) (f7x2-zero))
    (equal (f7x2-add (f7x2-neg '(1 2 . bad)) '(1 2 . bad)) (f7x2-zero))
    (equal (f7x2-add '(1 2 . bad) (f7x2-neg '(1 2 . bad))) (f7x2-zero))
    (equal (f7x2-add (f7x2-neg (f7x2-fix '(10 -3 8)))
                       (f7x2-fix '(10 -3 8)))
           (f7x2-zero))
    (equal (f7x2-add (f7x2-fix '(10 -3 8))
                       (f7x2-neg (f7x2-fix '(10 -3 8))))
           (f7x2-zero)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable f7x2-add f7x2-neg f7x2-fix)))))

(local
 (defthm f7x2-subtraction-coherence-regressions
   (and
    ; Canonical zero, one, constants, and genuine linear values.
    (equal (f7x2-sub (f7x2-zero) (f7x2-zero)) (f7x2-zero))
    (equal (f7x2-sub (f7x2-one) (f7x2-zero)) (f7x2-fix (f7x2-one)))
    (equal (f7x2-sub '(5) (f7x2-zero)) (f7x2-fix '(5)))
    (equal (f7x2-sub '(3 4) (f7x2-zero)) (f7x2-fix '(3 4)))
    ; NIL, trailing-zero, overlong, out-of-range, and rational inputs.
    (equal (f7x2-sub nil (f7x2-zero)) (f7x2-fix nil))
    (equal (f7x2-sub '(1 2 0) (f7x2-zero)) (f7x2-fix '(1 2 0)))
    (equal (f7x2-sub '(1 2 3 4) (f7x2-zero)) (f7x2-fix '(1 2 3 4)))
    (equal (f7x2-sub '(-1 9) (f7x2-zero)) (f7x2-fix '(-1 9)))
    (equal (f7x2-sub '(1/2 3/4) (f7x2-zero)) (f7x2-fix '(1/2 3/4)))
    ; Nonnumeric atoms, proper/improper malformed lists, and fixed inputs.
    (equal (f7x2-sub 'bad (f7x2-zero)) (f7x2-fix 'bad))
    (equal (f7x2-sub '(bad 9) (f7x2-zero)) (f7x2-fix '(bad 9)))
    (equal (f7x2-sub '(1 2 . bad) (f7x2-zero)) (f7x2-fix '(1 2 . bad)))
    (equal (f7x2-sub (f7x2-fix '(10 -3 8)) (f7x2-zero))
           (f7x2-fix '(10 -3 8)))

    (equal (f7x2-sub (f7x2-zero) (f7x2-zero)) (f7x2-neg (f7x2-zero)))
    (equal (f7x2-sub (f7x2-zero) (f7x2-one)) (f7x2-neg (f7x2-one)))
    (equal (f7x2-sub (f7x2-zero) '(5)) (f7x2-neg '(5)))
    (equal (f7x2-sub (f7x2-zero) '(3 4)) (f7x2-neg '(3 4)))
    (equal (f7x2-sub (f7x2-zero) nil) (f7x2-neg nil))
    (equal (f7x2-sub (f7x2-zero) '(1 2 0)) (f7x2-neg '(1 2 0)))
    (equal (f7x2-sub (f7x2-zero) '(1 2 3 4)) (f7x2-neg '(1 2 3 4)))
    (equal (f7x2-sub (f7x2-zero) '(-1 9)) (f7x2-neg '(-1 9)))
    (equal (f7x2-sub (f7x2-zero) '(1/2 3/4)) (f7x2-neg '(1/2 3/4)))
    (equal (f7x2-sub (f7x2-zero) 'bad) (f7x2-neg 'bad))
    (equal (f7x2-sub (f7x2-zero) '(bad 9)) (f7x2-neg '(bad 9)))
    (equal (f7x2-sub (f7x2-zero) '(1 2 . bad)) (f7x2-neg '(1 2 . bad)))
    (equal (f7x2-sub (f7x2-zero) (f7x2-fix '(10 -3 8)))
           (f7x2-neg (f7x2-fix '(10 -3 8))))

    (equal (f7x2-sub (f7x2-zero) (f7x2-zero)) (f7x2-zero))
    (equal (f7x2-sub (f7x2-one) (f7x2-one)) (f7x2-zero))
    (equal (f7x2-sub '(5) '(5)) (f7x2-zero))
    (equal (f7x2-sub '(3 4) '(3 4)) (f7x2-zero))
    (equal (f7x2-sub nil nil) (f7x2-zero))
    (equal (f7x2-sub '(1 2 0) '(1 2 0)) (f7x2-zero))
    (equal (f7x2-sub '(1 2 3 4) '(1 2 3 4)) (f7x2-zero))
    (equal (f7x2-sub '(-1 9) '(-1 9)) (f7x2-zero))
    (equal (f7x2-sub '(1/2 3/4) '(1/2 3/4)) (f7x2-zero))
    (equal (f7x2-sub 'bad 'bad) (f7x2-zero))
    (equal (f7x2-sub '(bad 9) '(bad 9)) (f7x2-zero))
    (equal (f7x2-sub '(1 2 . bad) '(1 2 . bad)) (f7x2-zero))
    (equal (f7x2-sub (f7x2-fix '(10 -3 8))
                      (f7x2-fix '(10 -3 8)))
           (f7x2-zero)))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (disable f7x2-sub f7x2-add f7x2-neg f7x2-fix)))))

(local
 (defthm f7x2-multiplication-coefficient-formula-regressions
   (and
    (equal (list (f7x2-constant-coefficient (f7x2-mul '(1 2) '(3 4)))
                 (f7x2-linear-coefficient (f7x2-mul '(1 2) '(3 4)))) '(2 3))
    (equal (list (f7x2-constant-coefficient (f7x2-mul '(0 2) '(0 3)))
                 (f7x2-linear-coefficient (f7x2-mul '(0 2) '(0 3)))) '(1 0))
    (equal (list (f7x2-constant-coefficient (f7x2-mul '(3) '(0 4)))
                 (f7x2-linear-coefficient (f7x2-mul '(3) '(0 4)))) '(0 5))
    (equal (list (f7x2-constant-coefficient (f7x2-mul '(0 4) '(3)))
                 (f7x2-linear-coefficient (f7x2-mul '(0 4) '(3)))) '(0 5))
    (equal (list (f7x2-constant-coefficient (f7x2-mul nil '(3 4)))
                 (f7x2-linear-coefficient (f7x2-mul '(3 4) nil))) '(0 0))
    (equal (list (f7x2-constant-coefficient (f7x2-mul '(2) '(4)))
                 (f7x2-linear-coefficient (f7x2-mul '(2) '(4)))) '(1 0))
    (equal (list (f7x2-constant-coefficient (f7x2-mul '(0 2) '(3 4)))
                 (f7x2-linear-coefficient (f7x2-mul '(0 2) '(3 4)))) '(6 6))
    (equal (list (f7x2-constant-coefficient
                  (f7x2-mul '(1 2 0 7) '(3 4 0)))
                 (f7x2-linear-coefficient
                  (f7x2-mul '(1 2 0 7) '(3 4 0)))) '(2 3))
    (equal (list (f7x2-constant-coefficient (f7x2-mul '(-6 9) '(10 -3)))
                 (f7x2-linear-coefficient (f7x2-mul '(-6 9) '(10 -3)))) '(2 3))
    (equal (list (f7x2-constant-coefficient (f7x2-mul 'bad '(3 4)))
                 (f7x2-linear-coefficient (f7x2-mul '(3 4) '(1 . bad)))) '(0 4))
    (equal (f7x2-constant-coefficient (f7x2-mul '(1 1) '(1 1))) 0)
    (equal (f7x2-linear-coefficient (f7x2-mul '(1 1) '(1 6))) 0)
    (equal (list (f7x2-constant-coefficient (f7x2-mul '(0 0) '(3 4)))
                 (f7x2-linear-coefficient (f7x2-mul '(0 0) '(3 4)))) '(0 0)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable f7x2-mul)))))

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

; Multiplication commutativity is inherited directly from the public concrete
; polynomial theorem beneath the common fixer.  Keep every implementation
; below that transparent arithmetic boundary closed.
(defthm f7x2-mul-commutative
  (equal (f7x2-mul first second)
         (f7x2-mul second first))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints
  (("Goal"
    :use ((:instance f7-poly-mul-commutative-from-generic
                     (x first) (y second)))
    :in-theory
    (e/d (f7x2-mul)
         (f7x2-fix f7-poly-mul f7-raw-mul f7-raw-scale f7-raw-add
          f7-normalize f7-fix-coefficients f7-trim-trailing-zeros
          f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
          f7-poly-division-step f7-poly-division-step-core)))))

(local
 (defthm f7x2-mul-commutative-regressions
   (and
    (equal (f7x2-mul (f7x2-zero) (f7x2-one))
           (f7x2-mul (f7x2-one) (f7x2-zero)))
    (equal (f7x2-mul '(1 2) '(3 4))
           (f7x2-mul '(3 4) '(1 2)))
    (equal (f7x2-mul '(5 6) '(5 6))
           (f7x2-mul '(5 6) '(5 6)))
    (equal (f7x2-mul '(bad 9 . tail) '(8 -3 0))
           (f7x2-mul '(8 -3 0) '(bad 9 . tail)))
    (equal (f7x2-mul '(1 2 0) '(3 4))
           (f7x2-mul '(3 4) '(1 2))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable f7x2-mul-commutative)))))

; Multiplication associativity crosses only the public operand-fixer boundary.
; Selective expansion exposes each inner result as a fixed concrete polynomial
; product; the one-sided compatibility rules remove those fixers before the
; remaining outer calls are compared by concrete polynomial associativity.
(defthm f7x2-mul-associative
  (equal (f7x2-mul (f7x2-mul first second) third)
         (f7x2-mul first (f7x2-mul second third)))
  :hints
  (("Goal"
    :use ((:instance f7x2-mul-of-fix-left
                     (first (f7-poly-mul first second))
                     (second third))
          (:instance f7x2-mul-of-fix-right
                     (first first)
                     (second (f7-poly-mul second third)))
          (:instance f7-poly-mul-associative-from-generic
                     (x first) (y second) (z third)))
    :expand ((f7x2-mul first second)
             (f7x2-mul second third)
             (f7x2-mul (f7-poly-mul first second) third)
             (f7x2-mul first (f7-poly-mul second third)))
    :in-theory
    (disable f7x2-fix f7x2-mul f7x2-mul-commutative
             f7-poly-mul-associate-right-for-power
             f7-poly-mul f7-raw-mul f7-raw-scale f7-raw-add
             f7-normalize f7-fix-coefficients f7-trim-trailing-zeros
             f7-poly-remainder f7-poly-divmod f7-poly-divmod-core
             f7-poly-division-step f7-poly-division-step-core
             gfield::f7-fix gfield::f7-add gfield::f7-mul))))

(local
 (defthm f7x2-mul-associative-regressions
   (and
    (equal (f7x2-mul (f7x2-mul (f7x2-zero) (f7x2-one)) '(3 4))
           (f7x2-mul (f7x2-zero) (f7x2-mul (f7x2-one) '(3 4))))
    (equal (f7x2-mul (f7x2-mul '(1 2) '(3 4)) '(5 6))
           (f7x2-mul '(1 2) (f7x2-mul '(3 4) '(5 6))))
    (equal (f7x2-mul (f7x2-mul '(bad 9 . tail) '(8 -3 0)) '(1 . bad))
           (f7x2-mul '(bad 9 . tail) (f7x2-mul '(8 -3 0) '(1 . bad))))
    (equal (f7x2-mul (f7x2-mul (f7x2-fix '(10 -3 8)) '(1 2 0)) '(3 4))
           (f7x2-mul (f7x2-fix '(10 -3 8))
                     (f7x2-mul '(1 2 0) '(3 4))))
    (equal (f7x2-mul (f7x2-mul '(1 2 0) '(3 4)) '(5 6))
           (f7x2-mul '(1 2) (f7x2-mul '(3 4) '(5 6)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable f7x2-mul-associative)))))
