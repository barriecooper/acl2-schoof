(in-package "GPOLY")

(include-book "../polynomial/generic/finite-field-instance")

; Natural integers enter the coefficient field by repeated addition of one.
; NFIX makes this embedding total on arbitrary ACL2 objects.
(defun finite-field-natural-coefficient (n)
  (declare (xargs :measure (nfix n)))
  (if (zp (nfix n))
      (gfield::finite-field-zero)
    (gfield::finite-field-add
     (gfield::finite-field-one)
     (finite-field-natural-coefficient (1- (nfix n))))))

(defthm finite-field-element-p-of-natural-coefficient
  (gfield::finite-field-element-p
   (finite-field-natural-coefficient n))
  :hints (("Goal" :induct (finite-field-natural-coefficient n)
           :in-theory (enable finite-field-natural-coefficient))))

(defun finite-field-division-polynomial-base-spec (n a b)
  (let* ((n (nfix n))
         (a (gfield::finite-field-fix a))
         (b (gfield::finite-field-fix b))
         (a2 (gfield::finite-field-mul a a))
         (a3 (gfield::finite-field-mul a2 a))
         (b2 (gfield::finite-field-mul b b))
         (ab (gfield::finite-field-mul a b)))
    (cond ((equal n 0) nil)
          ((equal n 1) (list (gfield::finite-field-one)))
          ; Even indices omit the conventional factor 2y.
          ((equal n 2) (list (gfield::finite-field-one)))
          ((equal n 3)
           (finite-field-poly-normalize
            (list (gfield::finite-field-neg a2)
                  (gfield::finite-field-mul
                   (finite-field-natural-coefficient 12) b)
                  (gfield::finite-field-mul
                   (finite-field-natural-coefficient 6) a)
                  (gfield::finite-field-zero)
                  (finite-field-natural-coefficient 3))))
          ((equal n 4)
           (finite-field-poly-normalize
            (list
             (gfield::finite-field-neg
              (gfield::finite-field-add
               (gfield::finite-field-mul
                (finite-field-natural-coefficient 2) a3)
               (gfield::finite-field-mul
                (finite-field-natural-coefficient 16) b2)))
             (gfield::finite-field-neg
              (gfield::finite-field-mul
               (finite-field-natural-coefficient 8) ab))
             (gfield::finite-field-neg
              (gfield::finite-field-mul
               (finite-field-natural-coefficient 10) a2))
             (gfield::finite-field-mul
              (finite-field-natural-coefficient 40) b)
             (gfield::finite-field-mul
              (finite-field-natural-coefficient 10) a)
             (gfield::finite-field-zero)
             (finite-field-natural-coefficient 2))))
          (t nil))))

; The first implementation is deliberately transparent.  It is kept distinct
; from the mathematical specification so a later recurrence/fast evaluator can
; replace this body only after proving the same correspondence contract.
(defun finite-field-division-polynomial-base (n a b)
  (finite-field-division-polynomial-base-spec (nfix n)
                                               (gfield::finite-field-fix a)
                                               (gfield::finite-field-fix b)))

(defthm finite-field-division-polynomial-base-correct
  (equal (finite-field-division-polynomial-base n a b)
         (finite-field-division-polynomial-base-spec n a b)))

(defthm finite-field-division-polynomial-base-of-nfix
  (equal (finite-field-division-polynomial-base (nfix n) a b)
         (finite-field-division-polynomial-base n a b)))

(defthm finite-field-division-polynomial-base-of-coefficient-fixes
  (equal (finite-field-division-polynomial-base
          n (gfield::finite-field-fix a) (gfield::finite-field-fix b))
         (finite-field-division-polynomial-base n a b)))

(defthm finite-field-canonical-polynomial-p-of-division-polynomial-base
  (finite-field-canonical-polynomial-p
   (finite-field-division-polynomial-base n a b))
  :hints (("Goal" :cases ((equal (nfix n) 0)
                           (equal (nfix n) 1)
                           (equal (nfix n) 2)
                           (equal (nfix n) 3)
                           (equal (nfix n) 4))
           :in-theory (enable finite-field-division-polynomial-base
                              finite-field-division-polynomial-base-spec
                              finite-field-canonical-polynomial-p))))

(defthm finite-field-polynomial-p-of-division-polynomial-base
  (finite-field-polynomial-p
   (finite-field-division-polynomial-base n a b))
  :hints (("Goal"
           :use finite-field-canonical-polynomial-p-of-division-polynomial-base
           :in-theory (enable finite-field-canonical-polynomial-p
                              finite-field-polynomial-p))))

(defthm finite-field-division-polynomial-base-equations
  (and (equal (finite-field-division-polynomial-base 0 a b) nil)
       (equal (finite-field-division-polynomial-base 1 a b)
              (list (gfield::finite-field-one)))
       (equal (finite-field-division-polynomial-base 2 a b)
              (list (gfield::finite-field-one))))
  :rule-classes nil)

(defthm finite-field-division-polynomial-base-index-3
  (equal
   (finite-field-division-polynomial-base 3 a b)
   (let* ((a (gfield::finite-field-fix a))
          (b (gfield::finite-field-fix b))
          (a2 (gfield::finite-field-mul a a)))
     (finite-field-poly-normalize
      (list (gfield::finite-field-neg a2)
            (gfield::finite-field-mul
             (finite-field-natural-coefficient 12) b)
            (gfield::finite-field-mul
             (finite-field-natural-coefficient 6) a)
            (gfield::finite-field-zero)
            (finite-field-natural-coefficient 3)))))
  :hints (("Goal"
           :in-theory (enable finite-field-division-polynomial-base
                              finite-field-division-polynomial-base-spec))))

(defthm finite-field-division-polynomial-base-index-4
  (equal
   (finite-field-division-polynomial-base 4 a b)
   (let* ((a (gfield::finite-field-fix a))
          (b (gfield::finite-field-fix b))
          (a2 (gfield::finite-field-mul a a))
          (a3 (gfield::finite-field-mul a2 a))
          (b2 (gfield::finite-field-mul b b))
          (ab (gfield::finite-field-mul a b)))
     (finite-field-poly-normalize
      (list
       (gfield::finite-field-neg
        (gfield::finite-field-add
         (gfield::finite-field-mul
          (finite-field-natural-coefficient 2) a3)
         (gfield::finite-field-mul
          (finite-field-natural-coefficient 16) b2)))
       (gfield::finite-field-neg
        (gfield::finite-field-mul
         (finite-field-natural-coefficient 8) ab))
       (gfield::finite-field-neg
        (gfield::finite-field-mul
         (finite-field-natural-coefficient 10) a2))
       (gfield::finite-field-mul
        (finite-field-natural-coefficient 40) b)
       (gfield::finite-field-mul
        (finite-field-natural-coefficient 10) a)
       (gfield::finite-field-zero)
       (finite-field-natural-coefficient 2)))))
  :hints (("Goal"
           :in-theory (enable finite-field-division-polynomial-base
                              finite-field-division-polynomial-base-spec))))

(defthm finite-field-division-polynomial-base-when-unsupported-index
  (implies (not (member-equal (nfix n) '(0 1 2 3 4)))
           (equal (finite-field-division-polynomial-base n a b) nil))
  :hints (("Goal"
           :in-theory (enable finite-field-division-polynomial-base
                              finite-field-division-polynomial-base-spec))))

(verify-guards finite-field-natural-coefficient)
(verify-guards finite-field-division-polynomial-base-spec)
(verify-guards finite-field-division-polynomial-base)
