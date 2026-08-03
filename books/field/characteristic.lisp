(in-package "GFIELD")

(include-book "natural-scalar")

; Every positive scalar through BOUND is non-annihilating on field one.
(defun no-smaller-positive-annihilator-p (bound)
  (declare (xargs :measure (nfix bound)))
  (if (zp (nfix bound))
      t
    (and (not (equal (field-nat-mul (nfix bound) (field-one))
                     (field-zero)))
         (no-smaller-positive-annihilator-p (1- (nfix bound))))))

; A field characteristic is the least positive additive period of field one.
(defun field-characteristic-p (p)
  (and (posp p)
       (equal (field-nat-mul p (field-one)) (field-zero))
       (no-smaller-positive-annihilator-p (1- p))))

(defthm no-smaller-positive-annihilator-p-of-nfix
  (equal (no-smaller-positive-annihilator-p (nfix bound))
         (no-smaller-positive-annihilator-p bound)))

(defthm no-smaller-positive-annihilator-p-of-zero
  (no-smaller-positive-annihilator-p 0))

(defthm no-smaller-positive-annihilator-p-of-successor
  (equal (no-smaller-positive-annihilator-p (+ 1 (nfix bound)))
         (and (not (equal (field-nat-mul (+ 1 (nfix bound)) (field-one))
                          (field-zero)))
              (no-smaller-positive-annihilator-p bound))))

(defthm no-smaller-positive-annihilator-p-implies-nonzero
  (implies (and (no-smaller-positive-annihilator-p bound)
                (posp n)
                (<= n (nfix bound)))
           (not (equal (field-nat-mul n (field-one))
                       (field-zero))))
  :hints (("Goal"
           :induct (no-smaller-positive-annihilator-p bound)
           :in-theory (enable no-smaller-positive-annihilator-p))))

(defthm posp-when-field-characteristic-p
  (implies (field-characteristic-p p) (posp p))
  :hints (("Goal" :in-theory (enable field-characteristic-p))))

(defthm field-nat-mul-of-characteristic-and-one
  (implies (field-characteristic-p p)
           (equal (field-nat-mul p (field-one)) (field-zero)))
  :hints (("Goal" :in-theory (enable field-characteristic-p))))

(defthm field-characteristic-is-least-positive-annihilator
  (implies (and (field-characteristic-p p)
                (posp n)
                (< n p))
           (not (equal (field-nat-mul n (field-one))
                       (field-zero))))
  :hints (("Goal"
           :use ((:instance no-smaller-positive-annihilator-p-implies-nonzero
                            (bound (1- p))))
           :in-theory (enable field-characteristic-p))))

(defthm field-nat-mul-of-characteristic
  (implies (field-characteristic-p p)
           (equal (field-nat-mul p x) (field-zero)))
  :hints (("Goal"
           :use ((:instance field-nat-mul-of-mul-right
                            (n p) (x x) (y (field-one)))
                 (:instance field-nat-mul-of-characteristic-and-one))
           :in-theory (disable field-characteristic-p
                               no-smaller-positive-annihilator-p
                               field-nat-mul-of-mul-right
                               field-nat-mul-of-characteristic-and-one))))

(defthm field-characteristic-unique
  (implies (and (field-characteristic-p p)
                (field-characteristic-p q))
           (equal p q))
  :rule-classes nil
  :hints (("Goal"
           :cases ((< p q) (< q p))
           :use ((:instance field-characteristic-is-least-positive-annihilator
                            (p q) (n p))
                 (:instance field-characteristic-is-least-positive-annihilator
                            (p p) (n q))
                 (:instance field-nat-mul-of-characteristic-and-one (p p))
                 (:instance field-nat-mul-of-characteristic-and-one (p q))))))

(verify-guards no-smaller-positive-annihilator-p)
(verify-guards field-characteristic-p)
