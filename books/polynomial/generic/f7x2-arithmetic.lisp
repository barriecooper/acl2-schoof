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


(verify-guards f7x2-add
  :hints (("Goal" :in-theory (enable f7x2-add))))
(verify-guards f7x2-neg
  :hints (("Goal" :in-theory (enable f7x2-neg))))
(verify-guards f7x2-sub
  :hints (("Goal" :in-theory (enable f7x2-sub))))
(verify-guards f7x2-mul
  :hints (("Goal" :in-theory (enable f7x2-mul))))

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


(assert-event
 (and
  (equal (f7x2-add '(1) '(1)) '(2))
  (equal (f7x2-add '(0 1) '(0 1)) '(0 2))
  (equal (f7x2-add '(1 1) '(1 1)) '(2 2))
  (equal (f7x2-add '(8 1 0) '(1 7))
         (f7x2-add (f7x2-fix '(8 1 0)) (f7x2-fix '(1 7))))
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
