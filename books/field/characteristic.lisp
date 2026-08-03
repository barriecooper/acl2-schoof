(in-package "GFIELD")

(include-book "natural-scalar")

; A field's characteristic is its least positive additive period.  This
; contextual predicate adds no constraint to the unrestricted field kernel.
(defun-sk field-characteristic-p (p)
  (forall n
    (and (posp p)
         (equal (field-nat-mul p (field-one))
                (field-zero))
         (implies (and (posp n)
                       (< n p))
                  (not (equal (field-nat-mul n (field-one))
                              (field-zero)))))))

(defthm posp-when-field-characteristic-p
  (implies (field-characteristic-p p)
           (posp p))
  :hints (("Goal" :use ((:instance field-characteristic-p-necc (n 0))))))

(defthm field-nat-mul-of-characteristic-and-one
  (implies (field-characteristic-p p)
           (equal (field-nat-mul p (field-one))
                  (field-zero)))
  :hints (("Goal" :use ((:instance field-characteristic-p-necc (n 0))))))

(defthm field-characteristic-is-least-positive-annihilator
  (implies (and (field-characteristic-p p)
                (posp n)
                (< n p))
           (not (equal (field-nat-mul n (field-one))
                       (field-zero))))
  :hints (("Goal" :use ((:instance field-characteristic-p-necc
                                   (n n))))))

(defthm field-nat-mul-of-characteristic
  (implies (field-characteristic-p p)
           (equal (field-nat-mul p x)
                  (field-zero)))
  :hints (("Goal"
           :use ((:instance field-nat-mul-of-mul-right
                            (n p) (x x) (y (field-one)))
                 (:instance field-nat-mul-of-characteristic-and-one))
           :in-theory (disable field-nat-mul-of-mul-right
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
