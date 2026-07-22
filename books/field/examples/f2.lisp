(in-package "GFIELD")

; Executable Boolean field used only as an instantiation regression.
(defun f2-element-p (x) (booleanp x))
(defun f2-fix (x) (if x t nil))
(defun f2-zero () nil)
(defun f2-one () t)
(defun f2-add (x y) (if (equal (f2-fix x) (f2-fix y)) nil t))
(defun f2-mul (x y) (if (and (f2-fix x) (f2-fix y)) t nil))
(defun f2-neg (x) (f2-fix x))
(defun f2-inv (x) (f2-fix x))
(defun f2-sub (x y) (f2-add x (f2-neg y)))
(defun f2-div (x y) (f2-mul x (f2-inv y)))
(def-pow-instance f2-pow-spec f2-pow-fast f2-pow
  f2-one f2-mul f2-fix)

(defthm f2-double-negation-from-generic-kernel
  (equal (f2-neg (f2-neg x)) (f2-fix x))
  :hints (("Goal" :by (:functional-instance field-neg-of-neg
                       (field-element-p f2-element-p)
                       (field-fix f2-fix)
                       (field-zero f2-zero)
                       (field-one f2-one)
                       (field-add f2-add)
                       (field-mul f2-mul)
                       (field-neg f2-neg)
                       (field-inv f2-inv)))))

; F2 power assurance.  This is deliberately a direct accumulator proof rather
; than a functional instantiation that maps either recursive power function.
; There is no named F2 multiplication-commutativity theorem in this book; the
; important induction theories disable F2-MUL and list associativity explicitly.
(defthm f2-mul-one-right-for-power
  (equal (f2-mul x (f2-one)) (f2-fix x)))

(defthm f2-element-p-of-f2-fix
  (f2-element-p (f2-fix x)))

(defthm f2-element-p-of-f2-one
  (f2-element-p (f2-one)))

(defthm f2-element-p-of-f2-mul
  (f2-element-p (f2-mul x y)))

(defthm f2-fix-when-f2-element-p
  (implies (f2-element-p x) (equal (f2-fix x) x)))

(defthm f2-mul-one-left-for-power
  (equal (f2-mul (f2-one) x) (f2-fix x)))

(defthm f2-mul-associative-for-power
  (equal (f2-mul (f2-mul x y) z)
         (f2-mul x (f2-mul y z))))

(defthm f2-pow-spec-successor
  (equal (f2-pow-spec base (+ 1 (nfix n)))
         (f2-mul (f2-fix base) (f2-pow-spec base n)))
  :hints (("Goal" :in-theory (enable f2-pow-spec))))

(defthm f2-pow-spec-plus-two
  (implies (and (f2-element-p base) (natp n))
           (equal (f2-pow-spec base (+ 2 n))
                  (f2-mul base
                          (f2-mul base (f2-pow-spec base n)))))
  :hints (("Goal" :use
           ((:instance f2-pow-spec-successor (n (+ 1 n)))
            (:instance f2-pow-spec-successor (n n))))))

(defthm f2-pow-spec-of-square
  (implies (and (f2-element-p base) (natp n))
           (equal (f2-pow-spec (f2-mul base base) n)
                  (f2-pow-spec base (* 2 n))))
  :hints (("Goal" :induct (f2-pow-spec base n)
           :in-theory (e/d (f2-pow-spec f2-pow-spec-plus-two
                                         f2-mul-associative-for-power)
                           (f2-mul)))
          ("Subgoal *1/2" :use
           ((:instance f2-pow-spec-plus-two
             (base base) (n (+ -2 (* 2 n)))))
           :in-theory (disable f2-mul))))

(defthm f2-pow-spec-odd-form
  (implies (and (f2-element-p base) (natp n))
           (equal (f2-pow-spec base (+ 1 (* 2 n)))
                  (f2-mul base (f2-pow-spec base (* 2 n)))))
  :hints (("Goal" :use
           ((:instance f2-pow-spec-successor (base base) (n (* 2 n)))))))

(defthm f2-pow-fast-accumulator-invariant
  (implies (and (f2-element-p acc)
                (f2-element-p base)
                (natp n))
           (equal (f2-pow-fast acc base n)
                  (f2-mul acc (f2-pow-spec base n))))
  :hints (("Goal" :induct (f2-pow-fast acc base n)
           :in-theory (e/d (f2-pow-fast f2-pow-spec
                                         f2-pow-spec-of-square
                                         f2-pow-spec-odd-form
                                         f2-mul-associative-for-power)
                           (f2-mul)))
          ("Subgoal *1/2" :use
           ((:instance natural-split-at-low-bit (n n))
            (:instance f2-pow-spec-odd-form
             (base base) (n (floor n 2))))
           :in-theory (disable f2-mul))
          ("Subgoal *1/3" :use
           ((:instance natural-split-at-low-bit (n n)))
           :in-theory (disable f2-mul))
          ("Subgoal *1/1" :use
           ((:instance natural-split-at-low-bit (n n))
            (:instance f2-mul-one-right-for-power (x acc)))
           :in-theory (disable f2-mul))))

(defthm f2-element-p-of-pow-spec
  (f2-element-p (f2-pow-spec x n))
  :hints (("Goal" :induct (f2-pow-spec x n)
           :in-theory (enable f2-pow-spec))))

(defthm f2-pow-fast-correct
  (equal (f2-pow-fast (f2-one) (f2-fix x) (nfix n))
         (f2-pow-spec (f2-fix x) (nfix n)))
  :hints (("Goal" :use
           ((:instance f2-pow-fast-accumulator-invariant
             (acc (f2-one)) (base (f2-fix x)) (n (nfix n)))
            (:instance f2-mul-one-left-for-power
             (x (f2-pow-spec (f2-fix x) (nfix n))))
            (:instance f2-fix-when-f2-element-p
             (x (f2-pow-spec (f2-fix x) (nfix n)))))
           :in-theory (disable f2-mul f2-pow-spec))))

(verify-guards f2-fix)
(verify-guards f2-one)
(verify-guards f2-mul)
(verify-guards f2-pow-fast)
(verify-guards f2-pow
  :hints (("Goal" :use f2-pow-fast-correct)))
