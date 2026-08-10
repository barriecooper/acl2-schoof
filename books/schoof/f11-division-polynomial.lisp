(in-package "GPOLY")

(include-book "division-polynomial-sequence")
(include-book "../curve/f11-golden")

; The concrete polynomial seam is generated from the same transparent templates
; as FINITE-FIELD-INSTANCE.  It deliberately contains no second polynomial
; algorithm.
(def-add-instance f11-poly-raw-add f11-poly-add f11-fix-coefficients
                  f11-normalize gfield::f11-add)
(def-neg-sub-instance f11-poly-raw-neg f11-poly-neg f11-poly-sub
                      f11-poly-add f11-normalize gfield::f11-neg)
(def-scale-instance f11-poly-raw-scale f11-poly-scale f11-normalize
                    gfield::f11-fix gfield::f11-mul)
(def-mul-instance f11-poly-raw-mul f11-poly-mul f11-poly-raw-add
                  f11-poly-raw-scale f11-normalize gfield::f11-zero)

(defun f11-natural-coefficient (n)
  (declare (xargs :measure (nfix n)))
  (if (zp (nfix n)) (gfield::f11-zero)
    (gfield::f11-add (gfield::f11-one)
                     (f11-natural-coefficient (1- (nfix n))))))

(defun f11-division-polynomial-base (n a b)
  (let* ((n (nfix n)) (a (gfield::f11-fix a)) (b (gfield::f11-fix b))
         (a2 (gfield::f11-mul a a)) (a3 (gfield::f11-mul a2 a))
         (b2 (gfield::f11-mul b b)) (ab (gfield::f11-mul a b)))
    (cond ((equal n 0) nil)
          ((or (equal n 1) (equal n 2)) (list (gfield::f11-one)))
          ((equal n 3)
           (f11-normalize
            (list (gfield::f11-neg a2)
                  (gfield::f11-mul (f11-natural-coefficient 12) b)
                  (gfield::f11-mul (f11-natural-coefficient 6) a)
                  (gfield::f11-zero) (f11-natural-coefficient 3))))
          ((equal n 4)
           (f11-normalize
            (list (gfield::f11-neg
                   (gfield::f11-add
                    (gfield::f11-mul (f11-natural-coefficient 2) a3)
                    (gfield::f11-mul (f11-natural-coefficient 16) b2)))
                  (gfield::f11-neg (gfield::f11-mul
                                    (f11-natural-coefficient 8) ab))
                  (gfield::f11-neg (gfield::f11-mul
                                    (f11-natural-coefficient 10) a2))
                  (gfield::f11-mul (f11-natural-coefficient 40) b)
                  (gfield::f11-mul (f11-natural-coefficient 10) a)
                  (gfield::f11-zero) (f11-natural-coefficient 2))))
          (t nil))))

(defun f11-division-polynomial-c (a b)
  (let ((four (f11-natural-coefficient 4))
        (a (gfield::f11-fix a)) (b (gfield::f11-fix b)))
    (f11-normalize
     (list (gfield::f11-mul four b) (gfield::f11-mul four a)
           (gfield::f11-zero) four))))
(defun f11-poly-square (x) (f11-poly-mul x x))
(defun f11-poly-cube (x) (f11-poly-mul x (f11-poly-square x)))

(defun f11-division-polynomial-recurrence-step (n table a b)
  (declare (xargs :guard (true-listp table) :verify-guards nil))
  (let* ((n (nfix n)) (m (floor n 2))
         (c2 (f11-poly-square (f11-division-polynomial-c a b))))
    (if (< n 5) (f11-division-polynomial-base n a b)
      (if (oddp n)
          (if (evenp m)
              (f11-poly-sub
               (f11-poly-mul c2 (f11-poly-mul (nth (+ m 2) table)
                                               (f11-poly-cube (nth m table))))
               (f11-poly-mul (nth (- m 1) table)
                             (f11-poly-cube (nth (+ m 1) table))))
            (f11-poly-sub
             (f11-poly-mul (nth (+ m 2) table)
                           (f11-poly-cube (nth m table)))
             (f11-poly-mul c2 (f11-poly-mul (nth (- m 1) table)
                                             (f11-poly-cube (nth (+ m 1) table))))))
        (f11-poly-mul
         (nth m table)
         (f11-poly-sub
          (f11-poly-mul (nth (+ m 2) table)
                        (f11-poly-square (nth (- m 1) table)))
          (f11-poly-mul (nth (- m 2) table)
                        (f11-poly-square (nth (+ m 1) table)))))))))

(defun f11-division-polynomial-table-extend (table value)
  (declare (xargs :guard (true-listp table)))
  (if (endp table)
      (list value)
    (cons (car table)
          (f11-division-polynomial-table-extend (cdr table) value))))

(defthm f11-division-polynomial-table-extend-is-append-singleton
  (equal (f11-division-polynomial-table-extend table value)
         (append table (list value))))

(defun f11-division-polynomial-table-nat (n a b)
  (declare (xargs :guard (natp n) :verify-guards nil :measure (nfix n)))
  (if (zp n) (list (f11-division-polynomial-base 0 a b))
    (let ((old (f11-division-polynomial-table-nat (1- n) a b)))
      (f11-division-polynomial-table-extend
       old (f11-division-polynomial-recurrence-step n old a b)))))
(defun f11-division-polynomial-table (n a b)
  (f11-division-polynomial-table-nat (nfix n) (gfield::f11-fix a)
                                      (gfield::f11-fix b)))
(defun f11-division-polynomial (n a b)
  (nth (nfix n) (f11-division-polynomial-table n a b)))

; These predicates stage the concrete relational specification needed by the
; later generic/F11 semantic-instance boundary.  This executable-substrate book
; proves neither generated-table satisfaction nor uniqueness for them.
(defun f11-division-polynomial-sequence-entries-p (k table a b)
  (and (equal (nth k table)
              (f11-division-polynomial-recurrence-step k table a b))
       (if (zp k) t
         (f11-division-polynomial-sequence-entries-p (1- k) table a b))))
(defun f11-division-polynomial-sequence-p (n table a b)
  (and (true-listp table) (equal (len table) (+ 1 (nfix n)))
       (f11-division-polynomial-sequence-entries-p (nfix n) table a b)))

; Public executable contract.  The semantic functional instance remains open.
(defthm f11-division-polynomial-base-equations
  (and (equal (f11-division-polynomial-base 0 a b) nil)
       (equal (f11-division-polynomial-base 1 a b) '(1))
       (equal (f11-division-polynomial-base 2 a b) '(1)))
  :rule-classes nil)
(defthm f11-division-polynomial-of-nfix
  (equal (f11-division-polynomial (nfix n) a b)
         (f11-division-polynomial n a b)))
(defthm f11-division-polynomial-of-coefficient-fixes
  (equal (f11-division-polynomial n (gfield::f11-fix a) (gfield::f11-fix b))
         (f11-division-polynomial n a b)))
(verify-guards f11-poly-raw-add)
(verify-guards f11-poly-add)
(verify-guards f11-poly-raw-neg)
(verify-guards f11-poly-neg)
(verify-guards f11-poly-sub)
(verify-guards f11-poly-raw-scale)
(verify-guards f11-poly-scale)
(verify-guards f11-poly-raw-mul)
(verify-guards f11-poly-mul)
(verify-guards f11-poly-square)
(verify-guards f11-poly-cube)
(verify-guards f11-natural-coefficient)
(verify-guards f11-division-polynomial-base)
(verify-guards f11-division-polynomial-c)
(verify-guards f11-division-polynomial-recurrence-step)
(verify-guards f11-division-polynomial-table-extend)
(verify-guards f11-division-polynomial-table-nat)
(verify-guards f11-division-polynomial-table)
(verify-guards f11-division-polynomial)
