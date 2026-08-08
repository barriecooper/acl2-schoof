(in-package "GPOLY")

(include-book "f7x2-seventh-power")
(include-book "f7x2-cardinality")

; This book is deliberately concrete.  It witnesses the proposed two-field
; seam without making that seam part of the generic field architecture.
(defun f7x2-embed-f7 (value)
  (f7x2-fix (list (gfield::f7-fix value))))

(defun f7x2-base-projection (value)
  (gfield::f7-fix (f7x2-constant-coefficient value)))

(defun f7x2-embedded-image-p (value)
  (equal (f7x2-fix value)
         (f7x2-embed-f7 (f7x2-base-projection value))))

(local
 (defthm f7-element-exhaustion-for-frobenius-witness
   (implies (gfield::f7-element-p x)
            (or (equal x 0) (equal x 1) (equal x 2) (equal x 3)
                (equal x 4) (equal x 5) (equal x 6)))
   :hints (("Goal" :in-theory (enable gfield::f7-element-p)))))

(local
 (defthm f7-fix-of-add
   (equal (gfield::f7-fix (gfield::f7-add first second))
          (gfield::f7-add first second))
   :hints (("Goal" :use ((:instance f7-element-p-of-f7-add-for-raw-shape
                                   (x first) (y second))
                          (:instance gfield::f7-fix-when-f7-element-p
                                   (x (gfield::f7-add first second))))))))

(local
 (defthm f7-fix-of-mul
   (equal (gfield::f7-fix (gfield::f7-mul first second))
          (gfield::f7-mul first second))
   :hints (("Goal" :use ((:instance gfield::f7-fix-when-f7-element-p
                                   (x (gfield::f7-mul first second))))))))

(local
 (defthm f7-fix-of-neg
   (equal (gfield::f7-fix (gfield::f7-neg value))
          (gfield::f7-neg value))
   :hints (("Goal" :in-theory (enable gfield::f7-fix gfield::f7-neg)))))

(local
 (defthm f7-mul-fix-left
   (equal (gfield::f7-mul (gfield::f7-fix first) second)
          (gfield::f7-mul first second))
   :hints (("Goal" :in-theory (enable gfield::f7-mul)))))

(local
 (defthm f7-mul-fix-right
   (equal (gfield::f7-mul first (gfield::f7-fix second))
          (gfield::f7-mul first second))
   :hints (("Goal" :in-theory (enable gfield::f7-mul)))))

(local
 (defthm f7-neg-fix
   (equal (gfield::f7-neg (gfield::f7-fix value))
          (gfield::f7-neg value))
   :hints (("Goal" :in-theory (enable gfield::f7-neg)))))

(local
 (defthm f7-add-zero-zero
   (equal (gfield::f7-add (gfield::f7-zero) (gfield::f7-zero))
          (gfield::f7-zero))
   :hints (("Goal" :in-theory (enable gfield::f7-add gfield::f7-zero
                                      gfield::f7-fix pfield::add
                                      pfield::fep-fix pfield::fep)))))

(local
 (defthm f7-neg-zero
   (equal (gfield::f7-neg (gfield::f7-zero)) (gfield::f7-zero))
   :hints (("Goal" :in-theory (enable gfield::f7-neg gfield::f7-zero
                                      gfield::f7-fix pfield::neg
                                      pfield::fep-fix pfield::fep)))))

(local
 (defthm f7-fix-zero
   (equal (gfield::f7-fix (gfield::f7-zero)) (gfield::f7-zero))
   :hints (("Goal" :in-theory (enable gfield::f7-fix gfield::f7-zero)))))

(defthm f7x2-embed-f7-of-fix
  (equal (f7x2-embed-f7 (gfield::f7-fix value))
         (f7x2-embed-f7 value))
  :hints (("Goal" :in-theory (enable f7x2-embed-f7))))

(defthm f7x2-element-p-of-embed-f7
  (f7x2-element-p (f7x2-embed-f7 value))
  :hints (("Goal" :in-theory (enable f7x2-embed-f7))))

(defthm f7x2-constant-coefficient-of-embed-f7
  (equal (f7x2-constant-coefficient (f7x2-embed-f7 value))
         (gfield::f7-fix value))
  :hints (("Goal" :in-theory (enable f7x2-embed-f7))))

(defthm f7x2-linear-coefficient-of-embed-f7
  (equal (f7x2-linear-coefficient (f7x2-embed-f7 value))
         (gfield::f7-zero))
  :hints (("Goal" :in-theory (enable f7x2-embed-f7))))

(defthm f7x2-embed-f7-injective
  (equal (equal (f7x2-embed-f7 first) (f7x2-embed-f7 second))
         (equal (gfield::f7-fix first) (gfield::f7-fix second)))
  :hints (("Goal" :use ((:instance f7x2-constant-coefficient-of-embed-f7
                                   (value first))
                         (:instance f7x2-constant-coefficient-of-embed-f7
                                   (value second))))))

(defthm f7x2-base-projection-of-embed-f7
  (equal (f7x2-base-projection (f7x2-embed-f7 value))
         (gfield::f7-fix value))
  :hints (("Goal" :in-theory (enable f7x2-base-projection))))

(defthm f7x2-embed-f7-zero
  (equal (f7x2-embed-f7 (gfield::f7-zero)) (f7x2-zero))
  :hints (("Goal" :in-theory (enable f7x2-embed-f7 gfield::f7-zero
                                     f7x2-zero))))

(defthm f7x2-embed-f7-one
  (equal (f7x2-embed-f7 (gfield::f7-one)) (f7x2-one))
  :hints (("Goal" :in-theory (enable f7x2-embed-f7 f7x2-one))))

(defthm f7x2-embed-f7-add
  (equal (f7x2-embed-f7 (gfield::f7-add first second))
         (f7x2-add (f7x2-embed-f7 first) (f7x2-embed-f7 second)))
  :hints (("Goal" :use ((:instance f7x2-coefficient-extensionality
                                   (first (f7x2-embed-f7
                                           (gfield::f7-add first second)))
                                   (second (f7x2-add
                                            (f7x2-embed-f7 first)
                                            (f7x2-embed-f7 second)))))
           :in-theory (union-theories
                       '(f7x2-element-p-of-embed-f7
                         f7x2-element-p-of-f7x2-add
                         f7x2-constant-coefficient-of-embed-f7
                         f7x2-linear-coefficient-of-embed-f7
                         f7x2-constant-coefficient-of-add
                         f7x2-linear-coefficient-of-add f7-fix-of-add
                         gfield::f7-add-fix-left gfield::f7-add-fix-right
                         f7-add-zero-zero)
                       (theory 'minimal-theory)))))

(defthm f7x2-embed-f7-neg
  (equal (f7x2-embed-f7 (gfield::f7-neg value))
         (f7x2-neg (f7x2-embed-f7 value)))
  :hints (("Goal" :use ((:instance f7x2-coefficient-extensionality
                                   (first (f7x2-embed-f7
                                           (gfield::f7-neg value)))
                                   (second (f7x2-neg
                                            (f7x2-embed-f7 value)))))
           :in-theory (union-theories
                       '(f7x2-element-p-of-embed-f7
                         f7x2-element-p-of-f7x2-neg
                         f7x2-constant-coefficient-of-embed-f7
                         f7x2-linear-coefficient-of-embed-f7
                         f7x2-constant-coefficient-of-neg
                         f7x2-linear-coefficient-of-neg f7-fix-of-neg
                         f7-neg-fix f7-neg-zero)
                       (theory 'minimal-theory)))))

(defthm f7x2-embed-f7-mul
  (equal (f7x2-embed-f7 (gfield::f7-mul first second))
         (f7x2-mul (f7x2-embed-f7 first) (f7x2-embed-f7 second)))
  :hints (("Goal" :use ((:instance f7x2-coefficient-extensionality
                                   (first (f7x2-embed-f7
                                           (gfield::f7-mul first second)))
                                   (second (f7x2-mul
                                            (f7x2-embed-f7 first)
                                            (f7x2-embed-f7 second)))))
           :in-theory (union-theories
                       '(f7x2-element-p-of-embed-f7
                         f7x2-element-p-of-f7x2-mul
                         f7x2-constant-coefficient-of-embed-f7
                         f7x2-linear-coefficient-of-embed-f7
                         f7x2-constant-coefficient-of-mul
                         f7x2-linear-coefficient-of-mul
                         f7-fix-of-mul
                         f7-mul-fix-left f7-mul-fix-right
                         gfield::f7-mul-zero-left
                         gfield::f7-mul-zero-right
                         f7-add-zero-right-for-raw-mul f7-neg-zero
                         f7-fix-zero gfield::f7-sub)
                       (theory 'minimal-theory)))))

(defthm f7x2-conjugate-of-fix
  (equal (f7x2-conjugate (f7x2-fix value))
         (f7x2-conjugate value))
  :hints (("Goal" :use ((:instance f7x2-coefficient-extensionality
                                   (first (f7x2-conjugate (f7x2-fix value)))
                                   (second (f7x2-conjugate value))))
           :in-theory (disable f7x2-conjugate f7x2-fix))))

(defthm f7x2-conjugate-zero
  (equal (f7x2-conjugate (f7x2-zero)) (f7x2-zero))
  :hints (("Goal" :use ((:instance f7x2-coefficient-extensionality
                                   (first (f7x2-conjugate (f7x2-zero)))
                                   (second (f7x2-zero))))
           :in-theory (disable f7x2-conjugate f7x2-zero))))

(defthm f7x2-conjugate-one
  (equal (f7x2-conjugate (f7x2-one)) (f7x2-one))
  :hints (("Goal" :use ((:instance f7x2-coefficient-extensionality
                                   (first (f7x2-conjugate (f7x2-one)))
                                   (second (f7x2-one))))
           :in-theory (disable f7x2-conjugate f7x2-one))))

(defthm f7x2-conjugate-neg
  (equal (f7x2-conjugate (f7x2-neg value))
         (f7x2-neg (f7x2-conjugate value)))
  :hints (("Goal" :use ((:instance f7x2-coefficient-extensionality
                                   (first (f7x2-conjugate (f7x2-neg value)))
                                   (second (f7x2-neg
                                            (f7x2-conjugate value)))))
           :in-theory (disable f7x2-conjugate f7x2-neg))))

(defthm f7x2-conjugate-involution
  (equal (f7x2-conjugate (f7x2-conjugate value)) (f7x2-fix value))
  :hints (("Goal" :use ((:instance f7x2-coefficient-extensionality
                                   (first (f7x2-conjugate
                                           (f7x2-conjugate value)))
                                   (second (f7x2-fix value))))
           :in-theory (disable f7x2-conjugate f7x2-fix))))

(local
 (defthm f7-self-negating-iff-zero
   (implies (gfield::f7-element-p value)
            (equal (equal value (gfield::f7-neg value))
                   (equal value (gfield::f7-zero))))
   :hints (("Goal" :use ((:instance f7-element-exhaustion-for-frobenius-witness
                                    (x value)))
            :in-theory (enable gfield::f7-element-p gfield::f7-neg
                               gfield::f7-fix pfield::neg pfield::fep-fix
                               pfield::fep)))))

(local
 (defthm linear-zero-implies-conjugate-fixed
   (implies (equal (f7x2-linear-coefficient value) (gfield::f7-zero))
            (equal (f7x2-conjugate value) (f7x2-fix value)))
   :hints (("Goal"
            :use ((:instance f7x2-coefficient-extensionality
                             (first (f7x2-conjugate value))
                             (second (f7x2-fix value))))
            :in-theory (union-theories
                        '(f7x2-element-p-of-conjugate
                          f7x2-element-p-of-f7x2-fix
                          f7x2-constant-coefficient-of-conjugate
                          f7x2-linear-coefficient-of-conjugate
                          f7x2-constant-coefficient-of-fix
                          f7x2-linear-coefficient-of-fix f7-neg-zero)
                        (theory 'minimal-theory))))))

(local
 (defthm equal-values-implies-equal-linear-coefficients
   (implies (equal first second)
            (equal (f7x2-linear-coefficient first)
                   (f7x2-linear-coefficient second)))))

(local
 (defthm conjugate-fixed-implies-linear-zero
   (implies (equal (f7x2-conjugate value) (f7x2-fix value))
            (equal (f7x2-linear-coefficient value) (gfield::f7-zero)))
   :hints (("Goal"
            :use ((:instance f7-self-negating-iff-zero
                             (value (f7x2-linear-coefficient value)))
                  (:instance equal-values-implies-equal-linear-coefficients
                             (first (f7x2-conjugate value))
                             (second (f7x2-fix value))))
            :in-theory (union-theories
                        '(f7x2-linear-coefficient-of-conjugate
                          f7x2-linear-coefficient-of-fix
                          f7-element-p-of-f7x2-linear-coefficient
                          f7-self-negating-iff-zero)
                        (theory 'minimal-theory))))))

(defthm f7x2-conjugate-fixed-iff-linear-coefficient-zero
  (equal (equal (f7x2-conjugate value) (f7x2-fix value))
         (equal (f7x2-linear-coefficient value) (gfield::f7-zero)))
  :hints (("Goal" :use (linear-zero-implies-conjugate-fixed
                          conjugate-fixed-implies-linear-zero))))

(defthm f7x2-conjugate-moves-x
  (and (equal (f7x2-conjugate '(0 1)) '(0 6))
       (not (equal (f7x2-conjugate '(0 1)) (f7x2-fix '(0 1)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable f7x2-conjugate))))
