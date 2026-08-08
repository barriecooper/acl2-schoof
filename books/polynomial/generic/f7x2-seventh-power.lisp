(in-package "GPOLY")
(include-book "f7x2-arithmetic")

; Named straight-line powers expose the repeated-multiplication association.
(defun f7x2-square (value)
  (f7x2-mul value value))

(defun f7x2-fourth-power (value)
  (f7x2-square (f7x2-square value)))

(defun f7x2-seventh-power (value)
  (f7x2-mul value
             (f7x2-mul (f7x2-square value)
                       (f7x2-fourth-power value))))

; Coefficient conjugation is itself fixed, and fixes the projected F7
; coefficients before rebuilding the degree-below-two representative.
(defun f7x2-conjugate (value)
  (f7x2-fix
   (list (f7x2-constant-coefficient value)
         (gfield::f7-neg (f7x2-linear-coefficient value))
         (gfield::f7-zero))))

(defthm f7x2-element-p-of-conjugate
  (f7x2-element-p (f7x2-conjugate value))
  :hints (("Goal" :in-theory (enable f7x2-conjugate))))

(local
 (defthm f7-sub-zero-on-f7-element
   (implies (gfield::f7-element-p x)
            (equal (gfield::f7-sub x (gfield::f7-zero)) x))
   :hints (("Goal" :in-theory
            (enable gfield::f7-element-p gfield::f7-sub gfield::f7-zero
                    gfield::f7-add gfield::f7-neg gfield::f7-fix)))))

(local
 (defthm f7-fix-of-neg-on-f7-element
   (implies (gfield::f7-element-p x)
            (equal (gfield::f7-fix (gfield::f7-neg x))
                   (gfield::f7-neg x)))
   :hints (("Goal" :in-theory
            (enable gfield::f7-element-p gfield::f7-neg
                    gfield::f7-fix)))))

(defthm f7x2-constant-coefficient-of-conjugate
  (equal (f7x2-constant-coefficient (f7x2-conjugate value))
         (f7x2-constant-coefficient value))
  :hints (("Goal"
           :use ((:instance f7x2-constant-coefficient-of-fix
                            (x (list (f7x2-constant-coefficient value)
                                     (gfield::f7-neg
                                      (f7x2-linear-coefficient value))
                                     (gfield::f7-zero))))
                 (:instance f7x2-constant-coefficient-of-three-coefficients
                            (a (f7x2-constant-coefficient value))
                            (b (gfield::f7-neg
                                (f7x2-linear-coefficient value)))
                            (c (gfield::f7-zero)))
                 (:instance f7-sub-zero-on-f7-element
                            (x (f7x2-constant-coefficient value))))
           :in-theory (e/d (f7x2-conjugate)
                           (f7x2-fix f7x2-constant-coefficient
                            f7x2-linear-coefficient)))))

(defthm f7x2-linear-coefficient-of-conjugate
  (equal (f7x2-linear-coefficient (f7x2-conjugate value))
         (gfield::f7-neg (f7x2-linear-coefficient value)))
  :hints (("Goal"
           :use ((:instance f7x2-linear-coefficient-of-fix
                            (x (list (f7x2-constant-coefficient value)
                                     (gfield::f7-neg
                                      (f7x2-linear-coefficient value))
                                     (gfield::f7-zero))))
                 (:instance f7x2-linear-coefficient-of-three-coefficients
                            (a (f7x2-constant-coefficient value))
                            (b (gfield::f7-neg
                                (f7x2-linear-coefficient value)))
                            (c (gfield::f7-zero)))
                 (:instance f7-fix-of-neg-on-f7-element
                            (x (f7x2-linear-coefficient value))))
           :in-theory (e/d (f7x2-conjugate)
                           (f7x2-fix f7x2-constant-coefficient
                            f7x2-linear-coefficient)))))

(local
 (defthm f7-element-exhaustion
   (implies (gfield::f7-element-p x)
            (or (equal x 0) (equal x 1) (equal x 2) (equal x 3)
                (equal x 4) (equal x 5) (equal x 6)))
   :hints (("Goal" :in-theory (enable gfield::f7-element-p)))))

(local
 (defun f7-pair-mul (first second)
   (list (gfield::f7-sub
          (gfield::f7-mul (car first) (car second))
          (gfield::f7-mul (cadr first) (cadr second)))
         (gfield::f7-add
          (gfield::f7-mul (car first) (cadr second))
          (gfield::f7-mul (cadr first) (car second))))))

(local
 (defun f7-pair-seventh (a b)
   (let* ((value (list a b))
          (square (f7-pair-mul value value))
          (fourth (f7-pair-mul square square)))
     (f7-pair-mul value (f7-pair-mul square fourth)))))

(local
 (defthm f7-pair-seventh-scalar-identity
   (implies (and (gfield::f7-element-p a)
                 (gfield::f7-element-p b))
            (equal (f7-pair-seventh a b)
                   (list a (gfield::f7-neg b))))
   :hints (("Goal"
            :use ((:instance f7-element-exhaustion (x a))
                  (:instance f7-element-exhaustion (x b)))
            :in-theory
            (enable f7-pair-seventh f7-pair-mul
                    gfield::f7-element-p gfield::f7-sub
                    gfield::f7-add gfield::f7-mul gfield::f7-neg
                    gfield::f7-fix pfield::add pfield::mul
                    pfield::neg pfield::fep-fix pfield::fep)))))

(local
 (defthm f7x2-seventh-power-coefficient-pair
   (equal (list (f7x2-constant-coefficient
                 (f7x2-seventh-power value))
                (f7x2-linear-coefficient
                 (f7x2-seventh-power value)))
          (f7-pair-seventh (f7x2-constant-coefficient value)
                           (f7x2-linear-coefficient value)))
   :hints (("Goal"
            :in-theory
            (union-theories
             '(f7x2-seventh-power f7x2-fourth-power f7x2-square
               f7-pair-seventh f7-pair-mul
               f7x2-constant-coefficient-of-mul
               f7x2-linear-coefficient-of-mul car-cons cdr-cons)
             (theory 'minimal-theory))))))

(local
 (defthm equal-two-lists-implies-equal-first
   (implies (equal (list x y) (list a b)) (equal x a))
   :rule-classes nil))

(local
 (defthm equal-two-lists-implies-equal-second
   (implies (equal (list x y) (list a b)) (equal y b))
   :rule-classes nil))

(local
 (defthm f7x2-seventh-power-final-coefficient-pair
   (equal (list (f7x2-constant-coefficient
                 (f7x2-seventh-power value))
                (f7x2-linear-coefficient
                 (f7x2-seventh-power value)))
          (list (f7x2-constant-coefficient value)
                (gfield::f7-neg (f7x2-linear-coefficient value))))
   :hints (("Goal"
            :use ((:instance f7x2-seventh-power-coefficient-pair)
                  (:instance f7-pair-seventh-scalar-identity
                             (a (f7x2-constant-coefficient value))
                             (b (f7x2-linear-coefficient value))))
            :in-theory
            (union-theories '(f7x2-seventh-power-coefficient-pair
                              f7-element-p-of-f7x2-constant-coefficient
                              f7-element-p-of-f7x2-linear-coefficient)
                            (theory 'minimal-theory))))))

(local
 (defthm f7x2-pow-seven-constant-coefficient
   (equal (f7x2-constant-coefficient (f7x2-seventh-power value))
          (f7x2-constant-coefficient value))
   :hints (("Goal"
            :use ((:instance equal-two-lists-implies-equal-first
                             (x (f7x2-constant-coefficient
                                 (f7x2-seventh-power value)))
                             (y (f7x2-linear-coefficient
                                 (f7x2-seventh-power value)))
                             (a (f7x2-constant-coefficient value))
                             (b (gfield::f7-neg
                                 (f7x2-linear-coefficient value))))
                  (:instance f7x2-seventh-power-final-coefficient-pair))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm f7x2-pow-seven-linear-coefficient
   (equal (f7x2-linear-coefficient (f7x2-seventh-power value))
          (gfield::f7-neg (f7x2-linear-coefficient value)))
   :hints (("Goal"
            :use ((:instance equal-two-lists-implies-equal-second
                             (x (f7x2-constant-coefficient
                                 (f7x2-seventh-power value)))
                             (y (f7x2-linear-coefficient
                                 (f7x2-seventh-power value)))
                             (a (f7x2-constant-coefficient value))
                             (b (gfield::f7-neg
                                 (f7x2-linear-coefficient value))))
                  (:instance f7x2-seventh-power-final-coefficient-pair))
            :in-theory (theory 'minimal-theory)))))

(defthm f7x2-element-p-of-seventh-power
  (f7x2-element-p (f7x2-seventh-power value))
  :hints (("Goal" :in-theory
           (union-theories
            '(f7x2-seventh-power f7x2-fourth-power f7x2-square
              f7x2-element-p-of-f7x2-mul)
            (theory 'minimal-theory)))))

(defthm f7x2-seventh-power-is-conjugate
  (equal (f7x2-seventh-power value) (f7x2-conjugate value))
  :hints (("Goal"
           :use ((:instance f7x2-coefficient-extensionality
                            (first (f7x2-seventh-power value))
                            (second (f7x2-conjugate value)))
                 (:instance f7x2-element-p-of-seventh-power)
                 (:instance f7x2-element-p-of-conjugate))
           :in-theory
           (union-theories
            '(f7x2-pow-seven-constant-coefficient
              f7x2-pow-seven-linear-coefficient
              f7x2-constant-coefficient-of-conjugate
              f7x2-linear-coefficient-of-conjugate)
            (theory 'minimal-theory)))))


(defthm f7x2-seventh-power-repeated-multiplication
  (equal (f7x2-seventh-power value)
         (f7x2-mul value
                    (f7x2-mul (f7x2-mul value value)
                              (f7x2-mul (f7x2-mul value value)
                                        (f7x2-mul value value)))))
  :hints (("Goal" :in-theory
           (union-theories
            '(f7x2-seventh-power f7x2-fourth-power f7x2-square)
            (theory 'minimal-theory)))))
