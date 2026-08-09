(in-package "GPOLY")

(include-book "division-polynomial-base")
(include-book "arithmetic-5/top" :dir :system)

; C is the polynomial 4(x^3 + ax + b).  Normalization is necessary because
; the constrained finite-field context intentionally also admits fields in
; which the natural coefficient 4 is zero.
(defun finite-field-division-polynomial-c (a b)
  (let ((four (finite-field-natural-coefficient 4))
        (a (gfield::finite-field-fix a))
        (b (gfield::finite-field-fix b)))
    (finite-field-poly-normalize
     (list (gfield::finite-field-mul four b)
           (gfield::finite-field-mul four a)
           (gfield::finite-field-zero)
           four))))

(defun finite-field-poly-square (x)
  (finite-field-poly-mul x x))

(defun finite-field-poly-cube (x)
  (finite-field-poly-mul x (finite-field-poly-square x)))

(defthm finite-field-canonical-polynomial-p-of-poly-square
  (finite-field-canonical-polynomial-p (finite-field-poly-square x))
  :hints (("Goal"
           :use ((:instance finite-field-canonical-polynomial-p-of-poly-mul
                            (x x) (y x)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(finite-field-poly-square)))))

(defthm finite-field-canonical-polynomial-p-of-poly-cube
  (finite-field-canonical-polynomial-p (finite-field-poly-cube x))
  :hints (("Goal"
           :use ((:instance finite-field-canonical-polynomial-p-of-poly-mul
                            (x x) (y (finite-field-poly-square x))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(finite-field-poly-cube)))))

; TABLE is in ascending index order.  NTH is deliberately used directly: a
; later table-builder proof will establish that these reads are in range.
(defun finite-field-division-polynomial-odd-even-step (c2 fm-1 fm fm+1 fm+2)
  (finite-field-poly-sub
   (finite-field-poly-mul c2 (finite-field-poly-mul fm+2
                                                     (finite-field-poly-cube fm)))
   (finite-field-poly-mul fm-1 (finite-field-poly-cube fm+1))))

(defun finite-field-division-polynomial-odd-odd-step (c2 fm-1 fm fm+1 fm+2)
  (finite-field-poly-sub
   (finite-field-poly-mul fm+2 (finite-field-poly-cube fm))
   (finite-field-poly-mul c2 (finite-field-poly-mul fm-1
                                                     (finite-field-poly-cube fm+1)))))

(defun finite-field-division-polynomial-even-step (fm-2 fm-1 fm fm+1 fm+2)
  (finite-field-poly-mul
   fm
   (finite-field-poly-sub
    (finite-field-poly-mul fm+2 (finite-field-poly-square fm-1))
    (finite-field-poly-mul fm-2 (finite-field-poly-square fm+1)))))

(defthm finite-field-canonical-polynomial-p-of-division-polynomial-odd-even-step
  (finite-field-canonical-polynomial-p
   (finite-field-division-polynomial-odd-even-step c2 fm-1 fm fm+1 fm+2))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
                           '(finite-field-division-polynomial-odd-even-step
                             finite-field-canonical-polynomial-p-of-poly-sub
                             finite-field-canonical-polynomial-p-of-poly-mul
                             finite-field-canonical-polynomial-p-of-poly-cube)))))

(defthm finite-field-canonical-polynomial-p-of-division-polynomial-odd-odd-step
  (finite-field-canonical-polynomial-p
   (finite-field-division-polynomial-odd-odd-step c2 fm-1 fm fm+1 fm+2))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
                           '(finite-field-division-polynomial-odd-odd-step
                             finite-field-canonical-polynomial-p-of-poly-sub
                             finite-field-canonical-polynomial-p-of-poly-mul
                             finite-field-canonical-polynomial-p-of-poly-cube)))))

(defthm finite-field-canonical-polynomial-p-of-division-polynomial-even-step
  (finite-field-canonical-polynomial-p
   (finite-field-division-polynomial-even-step fm-2 fm-1 fm fm+1 fm+2))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
                           '(finite-field-division-polynomial-even-step
                             finite-field-canonical-polynomial-p-of-poly-sub
                             finite-field-canonical-polynomial-p-of-poly-mul
                             finite-field-canonical-polynomial-p-of-poly-square)))))

(defun finite-field-division-polynomial-recurrence-step (n table a b)
  (declare (xargs :guard (true-listp table) :verify-guards nil))
  (let ((n (nfix n)))
    (if (< n 5)
        (finite-field-division-polynomial-base n a b)
      (let* ((m (floor n 2))
             (fm-2 (nth (- m 2) table))
             (fm-1 (nth (- m 1) table))
             (fm (nth m table))
             (fm+1 (nth (+ m 1) table))
             (fm+2 (nth (+ m 2) table))
             (c2 (finite-field-poly-square
                  (finite-field-division-polynomial-c a b))))
        (if (oddp n)
            (if (evenp m)
                (finite-field-division-polynomial-odd-even-step
                 c2 fm-1 fm fm+1 fm+2)
              (finite-field-division-polynomial-odd-odd-step
               c2 fm-1 fm fm+1 fm+2))
          (finite-field-division-polynomial-even-step
           fm-2 fm-1 fm fm+1 fm+2))))))

(defthm finite-field-division-polynomial-c-equation
  (equal (finite-field-division-polynomial-c a b)
         (let ((four (finite-field-natural-coefficient 4))
               (a (gfield::finite-field-fix a))
               (b (gfield::finite-field-fix b)))
           (finite-field-poly-normalize
            (list (gfield::finite-field-mul four b)
                  (gfield::finite-field-mul four a)
                  (gfield::finite-field-zero)
                  four)))))

(defthm finite-field-division-polynomial-c-of-coefficient-fixes
  (equal (finite-field-division-polynomial-c
          (gfield::finite-field-fix a) (gfield::finite-field-fix b))
         (finite-field-division-polynomial-c a b)))

(defthm finite-field-canonical-polynomial-p-of-division-polynomial-c
  (finite-field-canonical-polynomial-p
   (finite-field-division-polynomial-c a b)))

(defthm finite-field-polynomial-p-of-division-polynomial-c
  (finite-field-polynomial-p (finite-field-division-polynomial-c a b))
  :hints (("Goal"
           :use finite-field-canonical-polynomial-p-of-division-polynomial-c
           :in-theory (enable finite-field-canonical-polynomial-p
                              finite-field-polynomial-p))))

(defthm finite-field-division-polynomial-recurrence-step-of-nfix
  (equal (finite-field-division-polynomial-recurrence-step
          (nfix n) table a b)
         (finite-field-division-polynomial-recurrence-step n table a b))
  :hints (("Goal" :in-theory (union-theories
                               (theory 'minimal-theory)
                               '(nfix finite-field-division-polynomial-recurrence-step)))))

(defthm finite-field-division-polynomial-recurrence-step-of-coefficient-fixes
  (equal (finite-field-division-polynomial-recurrence-step
          n table (gfield::finite-field-fix a) (gfield::finite-field-fix b))
         (finite-field-division-polynomial-recurrence-step n table a b))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(finite-field-division-polynomial-recurrence-step
              finite-field-division-polynomial-base-of-coefficient-fixes
              finite-field-division-polynomial-c-of-coefficient-fixes)))))

(defthm finite-field-canonical-polynomial-p-of-division-polynomial-recurrence-step
  (finite-field-canonical-polynomial-p
   (finite-field-division-polynomial-recurrence-step n table a b))
  :hints (("Goal"
           :cases ((< (nfix n) 5) (oddp (nfix n)) (evenp (floor (nfix n) 2)))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(finite-field-division-polynomial-recurrence-step
                         finite-field-canonical-polynomial-p-of-division-polynomial-base
                         finite-field-canonical-polynomial-p-of-division-polynomial-odd-even-step
                         finite-field-canonical-polynomial-p-of-division-polynomial-odd-odd-step
                         finite-field-canonical-polynomial-p-of-division-polynomial-even-step)))))

(defthm finite-field-polynomial-p-of-division-polynomial-recurrence-step
  (finite-field-polynomial-p
   (finite-field-division-polynomial-recurrence-step n table a b))
  :hints (("Goal"
           :use finite-field-canonical-polynomial-p-of-division-polynomial-recurrence-step
           :in-theory (enable finite-field-canonical-polynomial-p
                              finite-field-polynomial-p))))

(defthm division-polynomial-odd-index-arithmetic
  (implies (natp m)
           (and (equal (nfix (+ 1 (* 2 m))) (+ 1 (* 2 m)))
                (equal (floor (+ 1 (* 2 m)) 2) m)
                (oddp (+ 1 (* 2 m)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable oddp evenp))))

(defthm division-polynomial-even-index-arithmetic
  (implies (natp m)
           (and (equal (nfix (* 2 m)) (* 2 m))
                (equal (floor (* 2 m) 2) m)
                (evenp (* 2 m))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable oddp evenp))))

(defthm finite-field-division-polynomial-recurrence-step-base
  (implies (< (nfix n) 5)
           (equal (finite-field-division-polynomial-recurrence-step n table a b)
                  (finite-field-division-polynomial-base n a b)))
  :hints (("Goal" :in-theory (union-theories
                               (theory 'minimal-theory)
                               '(finite-field-division-polynomial-recurrence-step
                                 finite-field-division-polynomial-base-of-nfix)))))

(defthm finite-field-division-polynomial-recurrence-step-odd-even-half
  (implies (and (natp m) (<= 2 m) (evenp m))
           (equal
            (finite-field-division-polynomial-recurrence-step (+ 1 (* 2 m)) table a b)
            (finite-field-poly-sub
             (finite-field-poly-mul
              (finite-field-poly-square (finite-field-division-polynomial-c a b))
              (finite-field-poly-mul (nth (+ m 2) table)
                                     (finite-field-poly-cube (nth m table))))
             (finite-field-poly-mul (nth (- m 1) table)
                                    (finite-field-poly-cube
                                     (nth (+ m 1) table))))))
  :hints (("Goal" :use division-polynomial-odd-index-arithmetic
           :in-theory (e/d (finite-field-division-polynomial-recurrence-step
                 finite-field-division-polynomial-odd-even-step)
                (finite-field-poly-add finite-field-poly-neg finite-field-poly-sub
                 finite-field-poly-mul finite-field-poly-normalize
                 finite-field-poly-square finite-field-poly-cube)))))

(defthm finite-field-division-polynomial-recurrence-step-odd-odd-half
  (implies (and (natp m) (<= 2 m) (oddp m))
           (equal
            (finite-field-division-polynomial-recurrence-step (+ 1 (* 2 m)) table a b)
            (finite-field-poly-sub
             (finite-field-poly-mul (nth (+ m 2) table)
                                    (finite-field-poly-cube (nth m table)))
             (finite-field-poly-mul
              (finite-field-poly-square (finite-field-division-polynomial-c a b))
              (finite-field-poly-mul (nth (- m 1) table)
                                     (finite-field-poly-cube
                                      (nth (+ m 1) table)))))))
  :hints (("Goal" :use division-polynomial-odd-index-arithmetic
           :in-theory (e/d (finite-field-division-polynomial-recurrence-step
                 finite-field-division-polynomial-odd-odd-step)
                (finite-field-poly-add finite-field-poly-neg finite-field-poly-sub
                 finite-field-poly-mul finite-field-poly-normalize
                 finite-field-poly-square finite-field-poly-cube)))))

(defthm finite-field-division-polynomial-recurrence-step-even
  (implies (and (natp m) (<= 3 m))
           (equal
            (finite-field-division-polynomial-recurrence-step (* 2 m) table a b)
            (finite-field-poly-mul
             (nth m table)
             (finite-field-poly-sub
              (finite-field-poly-mul (nth (+ m 2) table)
                                     (finite-field-poly-square
                                      (nth (- m 1) table)))
              (finite-field-poly-mul (nth (- m 2) table)
                                     (finite-field-poly-square
                                      (nth (+ m 1) table)))))))
  :hints (("Goal" :use division-polynomial-even-index-arithmetic
           :in-theory (e/d (finite-field-division-polynomial-recurrence-step
                 finite-field-division-polynomial-even-step)
                (finite-field-poly-add finite-field-poly-neg finite-field-poly-sub
                 finite-field-poly-mul finite-field-poly-normalize
                 finite-field-poly-square finite-field-poly-cube)))))

(verify-guards finite-field-division-polynomial-c)
(verify-guards finite-field-poly-square)
(verify-guards finite-field-poly-cube)
(verify-guards finite-field-division-polynomial-odd-even-step)
(verify-guards finite-field-division-polynomial-odd-odd-step)
(verify-guards finite-field-division-polynomial-even-step)
(verify-guards finite-field-division-polynomial-recurrence-step)
