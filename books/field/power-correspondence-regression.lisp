(in-package "GFIELD")

(include-book "frobenius-exponent")
(include-book "pfield-adapter")
(include-book "examples/f11")

; F7 satisfies the comparison boundary from public equations only.  These
; proofs do not revisit the fast accumulator or its correctness invariant.
(local (defthm f7-pow-of-nfix-for-correspondence
         (equal (f7-pow x (nfix n)) (f7-pow x n))
         :hints (("Goal" :in-theory (enable f7-pow)))))
(local (defthm f7-pow-zero-for-correspondence
         (equal (f7-pow x 0) (f7-one))
         :hints (("Goal" :in-theory (enable f7-pow f7-pow-spec)))))
(local (defthm f7-pow-successor-total-for-correspondence
         (equal (f7-pow x (+ 1 (nfix n)))
                (f7-mul x (f7-pow x n)))
         :hints (("Goal" :in-theory (enable f7-pow f7-pow-spec)))))
(local (defthm f7-mul-fixed-congruence-for-correspondence
         (implies (and (equal (f7-fix x1) (f7-fix x2))
                       (equal (f7-fix y1) (f7-fix y2)))
                  (equal (f7-mul x1 y1) (f7-mul x2 y2)))
         :hints (("Goal" :in-theory (e/d (f7-mul) (f7-fix))))))
(local (defthm f7-add-fixed-congruence-for-correspondence
         (implies (and (equal (f7-fix x1) (f7-fix x2))
                       (equal (f7-fix y1) (f7-fix y2)))
                  (equal (f7-add x1 y1) (f7-add x2 y2)))
         :hints (("Goal" :in-theory (e/d (f7-add) (f7-fix))))))

(defthm f7-pow-correspondence-instance
  (f7-element-p (f7-pow x n))
  :hints (("Goal"
           :by (:functional-instance
                field-element-p-of-field-pow-instance
                (field-element-p f7-element-p)
                (field-fix f7-fix)
                (field-zero f7-zero)
                (field-one f7-one)
                (field-add f7-add)
                (field-mul f7-mul)
                (field-neg f7-neg)
                (field-inv f7-inv)
                (field-pow-instance f7-pow)))
          ("Subgoal 19.2" :use f7-mul-inverse-right)
          ("Subgoal 16.4"
           :use f7-mul-fixed-congruence-for-correspondence)
          ("Subgoal 15.11"
           :use f7-add-fixed-congruence-for-correspondence)
          ("Subgoal 12.2.1'" :in-theory (enable mod))
          ("Subgoal 11.2.1''" :in-theory (enable mod))
          ("Subgoal 11.2.1'" :in-theory (enable mod))))

; The only F7-specific mathematics is Fermat at the fixed residue.  The
; exported endpoint below is transported through the generic certificate.
(local (defthm f7-pow-six-is-pfield-pow
         (equal (f7-pow x 6) (pfield::pow (f7-fix x) 6 7))
         :hints (("Goal" :in-theory
                  (enable f7-pow f7-pow-spec f7-mul
                          pfield::pow-opener pfield::mul)))))

(local (defthm f7-pow-seven-fixed
         (equal (f7-pow x 7) (f7-fix x))
         :hints (("Goal"
                  :cases ((equal (f7-fix x) 0))
                  :use (f7-pow-six-is-pfield-pow
                        (:instance f7-pow-successor-total-for-correspondence
                                   (n 6))
                        (:instance f7-mul-one-right)
                        (:instance pfield::my-fermat-little
                                   (a (f7-fix x)) (p 7)))
                  :in-theory (enable f7-mul f7-fix pfield::mul
                                     pfield::fep-fix pfield::minus1
                                     dm::primep)))))

(defthm f7-pow-of-frobenius-exponent
  (equal (f7-pow x 7) (f7-fix x))
  :rule-classes nil
  :hints (("Goal"
           :by (:functional-instance
                field-pow-instance-of-field-frobenius-exponent
                (field-element-p f7-element-p)
                (field-fix f7-fix)
                (field-zero f7-zero)
                (field-one f7-one)
                (field-add f7-add)
                (field-mul f7-mul)
                (field-neg f7-neg)
                (field-inv f7-inv)
                (field-pow-instance f7-pow)
                (field-frobenius-exponent (lambda () 7))))
          ("Subgoal 20" :use f7-pow-seven-fixed)
          ("Subgoal 19.2" :use f7-mul-inverse-right)
          ("Subgoal 16.4" :use f7-mul-fixed-congruence-for-correspondence)
          ("Subgoal 15.11" :use f7-add-fixed-congruence-for-correspondence)
          ("Subgoal 12.2.1'" :in-theory (enable mod))
          ("Subgoal 11.2.1''" :in-theory (enable mod))
          ("Subgoal 11.2.1'" :in-theory (enable mod))))

; F11 remains a deliberately small production fixture.  A regression-local
; generated power is sufficient to check the second, distinct modulus.
(encapsulate
 ()
 (local (def-pow-instance f11-regression-pow-spec f11-regression-pow-fast
                          f11-regression-pow f11-one f11-mul f11-fix))
 (local (defun f11-regression-inv (x)
          (pfield::inv (f11-fix x) 11)))
 (local (defthm f11-regression-pow-of-nfix
          (equal (f11-regression-pow x (nfix n))
                 (f11-regression-pow x n))
          :hints (("Goal" :in-theory (enable f11-regression-pow)))))
 (local (defthm f11-regression-pow-zero
          (equal (f11-regression-pow x 0) (f11-one))
          :hints (("Goal" :in-theory
                   (enable f11-regression-pow f11-regression-pow-spec)))))
 (local (defthm f11-regression-pow-successor-total
          (equal (f11-regression-pow x (+ 1 (nfix n)))
                 (f11-mul x (f11-regression-pow x n)))
          :hints (("Goal" :in-theory
                   (enable f11-regression-pow f11-regression-pow-spec)))))
 (local (defthm f11-mul-fixed-congruence-for-correspondence
          (implies (and (equal (f11-fix x1) (f11-fix x2))
                        (equal (f11-fix y1) (f11-fix y2)))
                   (equal (f11-mul x1 y1) (f11-mul x2 y2)))
          :hints (("Goal" :in-theory (e/d (f11-mul) (f11-fix))))))
 (local (defthm f11-add-fixed-congruence-for-correspondence
          (implies (and (equal (f11-fix x1) (f11-fix x2))
                        (equal (f11-fix y1) (f11-fix y2)))
                   (equal (f11-add x1 y1) (f11-add x2 y2)))
          :hints (("Goal" :in-theory (e/d (f11-add) (f11-fix))))))

 (local
  (defthm f11-pow-correspondence-instance
   (f11-element-p (f11-regression-pow x n))
   :hints
   (("Goal"
     :by (:functional-instance
          field-element-p-of-field-pow-instance
          (field-element-p f11-element-p)
          (field-fix f11-fix)
          (field-zero f11-zero)
          (field-one f11-one)
          (field-add f11-add)
          (field-mul f11-mul)
          (field-neg f11-neg)
          (field-inv f11-regression-inv)
          (field-pow-instance f11-regression-pow)))
    ("Subgoal 19.2"
     :use ((:instance pfield::mul-of-inv-arg1
                      (x (f11-fix x)) (p 11)))
     :in-theory (e/d (f11-regression-inv f11-mul f11-fix
                                         f11-zero f11-one dm::primep)
                     (pfield::mul-of-inv-arg1)))
    ("Subgoal 16.4" :use f11-mul-fixed-congruence-for-correspondence)
    ("Subgoal 15.11" :use f11-add-fixed-congruence-for-correspondence)
    ("Subgoal 12.2.1'" :in-theory (enable mod))
    ("Subgoal 11.2.1''" :in-theory (enable mod))
    ("Subgoal 11.2.1'" :in-theory (enable mod)))))

 (local
  (defthm f11-regression-pow-ten-is-pfield-pow
    (equal (f11-regression-pow x 10)
           (pfield::pow (f11-fix x) 10 11))
    :hints (("Goal"
             :expand ((f11-regression-pow x 10)
                      (f11-regression-pow-spec (f11-fix x) 10)
                      (f11-regression-pow-spec (f11-fix x) 9)
                      (f11-regression-pow-spec (f11-fix x) 8)
                      (f11-regression-pow-spec (f11-fix x) 7)
                      (f11-regression-pow-spec (f11-fix x) 6)
                      (f11-regression-pow-spec (f11-fix x) 5)
                      (f11-regression-pow-spec (f11-fix x) 4)
                      (f11-regression-pow-spec (f11-fix x) 3)
                      (f11-regression-pow-spec (f11-fix x) 2)
                      (f11-regression-pow-spec (f11-fix x) 1)
                      (f11-regression-pow-spec (f11-fix x) 0)
                      (f11-regression-pow-spec (mod x 11) 10)
                      (f11-regression-pow-spec (mod x 11) 9)
                      (f11-regression-pow-spec (mod x 11) 8)
                      (f11-regression-pow-spec (mod x 11) 7)
                      (f11-regression-pow-spec (mod x 11) 6)
                      (f11-regression-pow-spec (mod x 11) 5)
                      (f11-regression-pow-spec (mod x 11) 4)
                      (f11-regression-pow-spec (mod x 11) 3)
                      (f11-regression-pow-spec (mod x 11) 2)
                      (f11-regression-pow-spec (mod x 11) 1)
                      (f11-regression-pow-spec (mod x 11) 0))
             :in-theory
             (enable f11-mul pfield::pow-opener pfield::mul)))))

 (local
  (defthm f11-regression-pow-eleven-fixed
    (equal (f11-regression-pow x 11) (f11-fix x))
    :hints (("Goal"
             :cases ((equal (f11-fix x) 0))
             :use (f11-regression-pow-ten-is-pfield-pow
                   (:instance f11-regression-pow-successor-total (n 10))
                   (:instance pfield::my-fermat-little
                              (a (f11-fix x)) (p 11)))
             :in-theory (enable f11-mul f11-fix f11-one pfield::mul
                                pfield::fep-fix pfield::minus1
                                dm::primep)))))

 (local
  (defthm f11-regression-pow-of-frobenius-exponent
    (equal (f11-regression-pow x 11) (f11-fix x))
    :rule-classes nil
    :hints
    (("Goal"
      :by (:functional-instance
           field-pow-instance-of-field-frobenius-exponent
           (field-element-p f11-element-p)
           (field-fix f11-fix)
           (field-zero f11-zero)
           (field-one f11-one)
           (field-add f11-add)
           (field-mul f11-mul)
           (field-neg f11-neg)
           (field-inv f11-regression-inv)
           (field-pow-instance f11-regression-pow)
           (field-frobenius-exponent (lambda () 11))))
     ("Subgoal 20" :use f11-regression-pow-eleven-fixed)
     ("Subgoal 19.2"
      :use ((:instance pfield::mul-of-inv-arg1
                       (x (f11-fix x)) (p 11)))
      :in-theory (e/d (f11-regression-inv f11-mul f11-fix
                                          f11-zero f11-one dm::primep)
                      (pfield::mul-of-inv-arg1)))
     ("Subgoal 16.4" :use f11-mul-fixed-congruence-for-correspondence)
     ("Subgoal 15.11" :use f11-add-fixed-congruence-for-correspondence)
     ("Subgoal 12.2.1'" :in-theory (enable mod))
     ("Subgoal 11.2.1''" :in-theory (enable mod))
     ("Subgoal 11.2.1'" :in-theory (enable mod)))))

 (local
  (defthm generated-power-correspondence-executions
    (and (equal (f7-pow 0 7) 0)
         (equal (f7-pow 1 7) 1)
         (equal (f7-pow 3 7) 3)
         (equal (f7-pow 10 7) 3)
         (equal (f7-pow 'bad 7) 0)
         (equal (f11-regression-pow 0 11) 0)
         (equal (f11-regression-pow 1 11) 1)
         (equal (f11-regression-pow 3 11) 3)
         (equal (f11-regression-pow 14 11) 3)
         (equal (f11-regression-pow 'bad 11) 0))
    :rule-classes nil)))
