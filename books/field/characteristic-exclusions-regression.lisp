(in-package "GFIELD")

(include-book "characteristic-exclusions")
(include-book "examples/f11")

(defun f7-regression-nat-sum (x n)
  (declare (xargs :measure (nfix n)))
  (let ((n (nfix n)))
    (if (zp n) (f7-zero)
      (f7-add (f7-fix x) (f7-regression-nat-sum x (1- n))))))

(local (defthm f7-regression-two-nonzero
         (not (equal (f7-regression-nat-sum (f7-one) 2) (f7-zero)))
         :hints (("Goal" :in-theory (enable f7-regression-nat-sum
                                             f7-one f7-zero f7-add f7-fix
                                             pfield::add pfield::fep-fix)))))
(local (defthm f7-regression-three-nonzero
         (not (equal (f7-regression-nat-sum (f7-one) 3) (f7-zero)))
         :hints (("Goal" :in-theory (enable f7-regression-nat-sum
                                             f7-one f7-zero f7-add f7-fix
                                             pfield::add pfield::fep-fix)))))

(defthm f7-nat-sum-two-of-field-one-nonzero
  (not (equal (f7-regression-nat-sum (f7-one) 2) (f7-zero)))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                        field-nat-sum-two-of-field-one-nonzero
                        (additive-field-fix f7-fix)
                        (additive-field-zero f7-zero)
                        (additive-field-one f7-one)
                        (additive-field-add f7-add)
                        (field-nat-sum f7-regression-nat-sum)))
          ("Subgoal 1" :use f7-regression-two-nonzero)))

(defthm f7-nat-sum-three-of-field-one-nonzero
  (not (equal (f7-regression-nat-sum (f7-one) 3) (f7-zero)))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                        field-nat-sum-three-of-field-one-nonzero
                        (additive-field-fix f7-fix)
                        (additive-field-zero f7-zero)
                        (additive-field-one f7-one)
                        (additive-field-add f7-add)
                        (field-nat-sum f7-regression-nat-sum)))
          ("Subgoal 1" :use f7-regression-three-nonzero)))

(encapsulate
 ()
 (local (defun f11-regression-nat-sum (x n)
          (declare (xargs :measure (nfix n)))
          (let ((n (nfix n)))
            (if (zp n) (f11-zero)
              (f11-add (f11-fix x)
                       (f11-regression-nat-sum x (1- n)))))))
 (local (defthm f11-regression-two-nonzero
          (not (equal (f11-regression-nat-sum (f11-one) 2) (f11-zero)))
          :hints (("Goal" :in-theory (enable f11-regression-nat-sum
                                              f11-one f11-zero f11-add f11-fix
                                              pfield::add pfield::fep-fix)))))
 (local (defthm f11-regression-three-nonzero
          (not (equal (f11-regression-nat-sum (f11-one) 3) (f11-zero)))
          :hints (("Goal" :in-theory (enable f11-regression-nat-sum
                                              f11-one f11-zero f11-add f11-fix
                                              pfield::add pfield::fep-fix)))))
 (local (defthm f11-nat-sum-two-of-field-one-nonzero
          (not (equal (f11-regression-nat-sum (f11-one) 2) (f11-zero)))
          :rule-classes nil
          :hints (("Goal" :by (:functional-instance
                                field-nat-sum-two-of-field-one-nonzero
                                (additive-field-fix f11-fix)
                                (additive-field-zero f11-zero)
                                (additive-field-one f11-one)
                                (additive-field-add f11-add)
                                (field-nat-sum f11-regression-nat-sum)))
                  ("Subgoal 1" :use f11-regression-two-nonzero))))
 (local (defthm f11-nat-sum-three-of-field-one-nonzero
          (not (equal (f11-regression-nat-sum (f11-one) 3) (f11-zero)))
          :rule-classes nil
          :hints (("Goal" :by (:functional-instance
                                field-nat-sum-three-of-field-one-nonzero
                                (additive-field-fix f11-fix)
                                (additive-field-zero f11-zero)
                                (additive-field-one f11-one)
                                (additive-field-add f11-add)
                                (field-nat-sum f11-regression-nat-sum)))
                  ("Subgoal 1" :use f11-regression-three-nonzero))))
 (local (defthm characteristic-exclusion-focused-executions
          (and (equal (f7-regression-nat-sum 0 0) 0)
               (equal (f7-regression-nat-sum 1 2) 2)
               (equal (f7-regression-nat-sum 1 3) 3)
               (equal (f7-regression-nat-sum 8 2) 2)
               (equal (f7-regression-nat-sum 'bad 3) 0)
               (equal (f11-regression-nat-sum 0 0) 0)
               (equal (f11-regression-nat-sum 1 2) 2)
               (equal (f11-regression-nat-sum 1 3) 3)
               (equal (f11-regression-nat-sum 12 3) 3)
               (equal (f11-regression-nat-sum 'bad 2) 0))
          :rule-classes nil)))
