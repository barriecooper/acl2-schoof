(in-package "GFIELD")

(include-book "kernel")
(include-book "../algebra/finite-bijection")
(local (include-book "arithmetic-5/top" :dir :system))

; A separate finite field model.  Field structure and bounded coding are
; constrained together; this does not strengthen the unrestricted FIELD-*
; context or the field-independent FINITE-* context.
; A canonical-representative field interface.  Local definitions are only
; consistency witnesses; clients replace the constrained symbols by functional
; instantiation.
(encapsulate
 (((finite-field-element-p *) => *) ((finite-field-fix *) => *)
  ((finite-field-zero) => *) ((finite-field-one) => *)
  ((finite-field-add * *) => *) ((finite-field-mul * *) => *)
  ((finite-field-neg *) => *) ((finite-field-inv *) => *)
  ((finite-field-rank *) => *) ((finite-field-unrank *) => *)
  ((finite-field-bound) => *))
 (local (defun finite-field-element-p (x) (booleanp x)))
 (local (defun finite-field-fix (x) (if x t nil)))
 (local (defun finite-field-zero () nil))
 (local (defun finite-field-one () t))
 (local (defun finite-field-add (x y)
          (if (equal (finite-field-fix x) (finite-field-fix y)) nil t)))
 (local (defun finite-field-mul (x y)
          (if (and (finite-field-fix x) (finite-field-fix y)) t nil)))
 (local (defun finite-field-neg (x) (finite-field-fix x)))
 (local (defun finite-field-inv (x) (finite-field-fix x)))
 (local (defun finite-field-rank (x) (if (finite-field-fix x) 1 0)))
 (local (defun finite-field-unrank (k) (equal k 1)))
 (local (defun finite-field-bound () 2))

 (defthm booleanp-of-finite-field-element-p
   (booleanp (finite-field-element-p x)) :rule-classes :type-prescription)
 (defthm finite-field-element-p-of-finite-field-fix (finite-field-element-p (finite-field-fix x)))
 (defthm finite-field-fix-when-finite-field-element-p
   (implies (finite-field-element-p x) (equal (finite-field-fix x) x)))
 (defthm finite-field-fix-idempotent
   (equal (finite-field-fix (finite-field-fix x)) (finite-field-fix x)))
 (defthm finite-field-element-p-of-zero (finite-field-element-p (finite-field-zero)))
 (defthm finite-field-element-p-of-one (finite-field-element-p (finite-field-one)))
 (defthm finite-field-zero-not-equal-finite-field-one
   (not (equal (finite-field-zero) (finite-field-one))))
 (defthm finite-field-fix-of-zero (equal (finite-field-fix (finite-field-zero)) (finite-field-zero)))
 (defthm finite-field-fix-of-one (equal (finite-field-fix (finite-field-one)) (finite-field-one)))
 (defthm finite-field-element-p-of-add (finite-field-element-p (finite-field-add x y)))
 (defthm finite-field-element-p-of-mul (finite-field-element-p (finite-field-mul x y)))
 (defthm finite-field-element-p-of-neg (finite-field-element-p (finite-field-neg x)))
 (defthm finite-field-element-p-of-inv (finite-field-element-p (finite-field-inv x)))
 (defthm finite-field-fix-of-add
   (equal (finite-field-fix (finite-field-add x y)) (finite-field-add x y)))
 (defthm finite-field-fix-of-mul
   (equal (finite-field-fix (finite-field-mul x y)) (finite-field-mul x y)))
 (defthm finite-field-fix-of-neg
   (equal (finite-field-fix (finite-field-neg x)) (finite-field-neg x)))
 (defthm finite-field-fix-of-inv
   (equal (finite-field-fix (finite-field-inv x)) (finite-field-inv x)))
 (defthm finite-field-add-of-fixes
   (equal (finite-field-add (finite-field-fix x) (finite-field-fix y)) (finite-field-add x y)))
 (defthm finite-field-add-fix-left
   (equal (finite-field-add (finite-field-fix x) y) (finite-field-add x y)))
 (defthm finite-field-add-fix-right
   (equal (finite-field-add x (finite-field-fix y)) (finite-field-add x y)))
 (defthm finite-field-mul-fix-left
   (equal (finite-field-mul (finite-field-fix x) y) (finite-field-mul x y)))
 (defthm finite-field-mul-fix-right
   (equal (finite-field-mul x (finite-field-fix y)) (finite-field-mul x y)))
 (defthm finite-field-mul-of-fixes
   (equal (finite-field-mul (finite-field-fix x) (finite-field-fix y)) (finite-field-mul x y)))
 (defthm finite-field-neg-of-fix
   (equal (finite-field-neg (finite-field-fix x)) (finite-field-neg x)))
 (defthm finite-field-inv-of-fix
   (equal (finite-field-inv (finite-field-fix x)) (finite-field-inv x)))
 (defthm finite-field-add-associative
   (equal (finite-field-add (finite-field-add x y) z)
          (finite-field-add x (finite-field-add y z))))
 (defthm finite-field-add-commutative
   (equal (finite-field-add x y) (finite-field-add y x)))
 (defthm finite-field-add-zero-left
   (equal (finite-field-add (finite-field-zero) x) (finite-field-fix x)))
 (defthm finite-field-add-inverse-left
   (equal (finite-field-add (finite-field-neg x) x) (finite-field-zero)))
 (defthm finite-field-add-fixed-congruence
   (implies (and (equal (finite-field-fix x1) (finite-field-fix x2))
                 (equal (finite-field-fix y1) (finite-field-fix y2)))
            (equal (finite-field-add x1 y1) (finite-field-add x2 y2))))
 (defthm finite-field-mul-fixed-congruence
   (implies (and (equal (finite-field-fix x1) (finite-field-fix x2))
                 (equal (finite-field-fix y1) (finite-field-fix y2)))
            (equal (finite-field-mul x1 y1) (finite-field-mul x2 y2))))
 (defthm finite-field-mul-associative
   (equal (finite-field-mul (finite-field-mul x y) z)
          (finite-field-mul x (finite-field-mul y z))))
 (defthm finite-field-mul-commutative
   (equal (finite-field-mul x y) (finite-field-mul y x)))
 (defthm finite-field-mul-one-left
   (equal (finite-field-mul (finite-field-one) x) (finite-field-fix x)))
 (defthm finite-field-mul-left-distributive
   (equal (finite-field-mul x (finite-field-add y z))
          (finite-field-add (finite-field-mul x y) (finite-field-mul x z))))
 (defthm finite-field-inv-of-zero
   (equal (finite-field-inv (finite-field-zero)) (finite-field-zero)))
 (defthm finite-field-mul-inverse-left
   (implies (not (equal (finite-field-fix x) (finite-field-zero)))
            (equal (finite-field-mul (finite-field-inv x) x) (finite-field-one))))

 (defthm posp-of-finite-field-bound
   (posp (finite-field-bound)))
 (defthm natp-of-finite-field-rank
   (natp (finite-field-rank x))
   :rule-classes (:rewrite :type-prescription))
 (defthm finite-field-rank-upper-bound
   (< (finite-field-rank x) (finite-field-bound))
   :rule-classes (:rewrite :linear))
 (defthm finite-field-fix-of-finite-field-unrank
   (equal (finite-field-fix (finite-field-unrank k))
          (finite-field-unrank k)))
 (defthm finite-field-unrank-of-finite-field-rank
   (equal (finite-field-unrank (finite-field-rank x))
          (finite-field-fix x)))
 (defthm finite-field-rank-of-finite-field-unrank-when-bounded
   (implies (and (natp k) (< k (finite-field-bound)))
            (equal (finite-field-rank (finite-field-unrank k)) k))))



(deftheory finite-field-context-instance-theory
  '(booleanp-of-finite-field-element-p
    finite-field-element-p-of-finite-field-fix
    finite-field-fix-when-finite-field-element-p
    finite-field-fix-idempotent
    finite-field-element-p-of-zero
    finite-field-element-p-of-one
    finite-field-zero-not-equal-finite-field-one
    finite-field-fix-of-zero finite-field-fix-of-one
    finite-field-element-p-of-add
    finite-field-element-p-of-mul
    finite-field-element-p-of-neg
    finite-field-element-p-of-inv
    finite-field-fix-of-add finite-field-fix-of-mul
    finite-field-fix-of-neg finite-field-fix-of-inv
    finite-field-add-of-fixes finite-field-add-fix-left
    finite-field-add-fix-right finite-field-mul-fix-left
    finite-field-mul-fix-right finite-field-mul-of-fixes
    finite-field-neg-of-fix finite-field-inv-of-fix
    finite-field-add-associative finite-field-add-commutative
    finite-field-add-zero-left finite-field-add-inverse-left
    finite-field-add-fixed-congruence finite-field-mul-fixed-congruence
    finite-field-mul-associative finite-field-mul-commutative
    finite-field-mul-one-left finite-field-mul-left-distributive
    finite-field-inv-of-zero finite-field-mul-inverse-left
    posp-of-finite-field-bound natp-of-finite-field-rank
    finite-field-rank-upper-bound finite-field-fix-of-finite-field-unrank
    finite-field-unrank-of-finite-field-rank
    finite-field-rank-of-finite-field-unrank-when-bounded))

(defthm finite-field-neg-of-neg
  (equal (finite-field-neg (finite-field-neg x)) (finite-field-fix x))
  :hints (("Goal" :by (:functional-instance field-neg-of-neg
                    (field-element-p finite-field-element-p)
                    (field-fix finite-field-fix)
                    (field-zero finite-field-zero) (field-one finite-field-one)
                    (field-add finite-field-add) (field-mul finite-field-mul)
                    (field-neg finite-field-neg) (field-inv finite-field-inv))
           :in-theory (theory 'minimal-theory))
          (and stable-under-simplificationp
               '(:use (booleanp-of-finite-field-element-p
 finite-field-element-p-of-finite-field-fix finite-field-fix-when-finite-field-element-p
 finite-field-fix-idempotent finite-field-element-p-of-zero finite-field-element-p-of-one
 finite-field-zero-not-equal-finite-field-one finite-field-fix-of-zero finite-field-fix-of-one
 finite-field-element-p-of-add finite-field-element-p-of-mul finite-field-element-p-of-neg
 finite-field-element-p-of-inv finite-field-fix-of-add finite-field-fix-of-mul
 finite-field-fix-of-neg finite-field-fix-of-inv finite-field-add-of-fixes
 finite-field-add-fix-left finite-field-add-fix-right finite-field-mul-of-fixes
 finite-field-mul-fix-left finite-field-mul-fix-right finite-field-neg-of-fix
 finite-field-inv-of-fix finite-field-add-associative finite-field-add-commutative
 finite-field-add-zero-left finite-field-add-inverse-left finite-field-add-fixed-congruence
 finite-field-mul-fixed-congruence finite-field-mul-associative finite-field-mul-commutative
 finite-field-mul-one-left finite-field-mul-left-distributive finite-field-inv-of-zero
 finite-field-mul-inverse-left)
                 :in-theory (theory 'minimal-theory)))))

(defthm finite-field-add-left-cancel
  (equal (equal (finite-field-add common first)
                (finite-field-add common second))
         (equal (finite-field-fix first) (finite-field-fix second)))
  :hints (("Goal" :by (:functional-instance field-add-left-cancel
                    (field-element-p finite-field-element-p)
                    (field-fix finite-field-fix)
                    (field-zero finite-field-zero) (field-one finite-field-one)
                    (field-add finite-field-add) (field-mul finite-field-mul)
                    (field-neg finite-field-neg) (field-inv finite-field-inv))
           :in-theory (theory 'minimal-theory))
          (and stable-under-simplificationp
               '(:use (booleanp-of-finite-field-element-p
 finite-field-element-p-of-finite-field-fix finite-field-fix-when-finite-field-element-p
 finite-field-fix-idempotent finite-field-element-p-of-zero finite-field-element-p-of-one
 finite-field-zero-not-equal-finite-field-one finite-field-fix-of-zero finite-field-fix-of-one
 finite-field-element-p-of-add finite-field-element-p-of-mul finite-field-element-p-of-neg
 finite-field-element-p-of-inv finite-field-fix-of-add finite-field-fix-of-mul
 finite-field-fix-of-neg finite-field-fix-of-inv finite-field-add-of-fixes
 finite-field-add-fix-left finite-field-add-fix-right finite-field-mul-of-fixes
 finite-field-mul-fix-left finite-field-mul-fix-right finite-field-neg-of-fix
 finite-field-inv-of-fix finite-field-add-associative finite-field-add-commutative
 finite-field-add-zero-left finite-field-add-inverse-left finite-field-add-fixed-congruence
 finite-field-mul-fixed-congruence finite-field-mul-associative finite-field-mul-commutative
 finite-field-mul-one-left finite-field-mul-left-distributive finite-field-inv-of-zero
 finite-field-mul-inverse-left)
                 :in-theory (theory 'minimal-theory)))))

(defthm finite-field-rank-of-finite-field-fix
  (equal (finite-field-rank (finite-field-fix x)) (finite-field-rank x))
  :hints (("Goal" :by (:functional-instance finite-rank-of-finite-fix
                    (finite-fix finite-field-fix)
                    (finite-rank finite-field-rank)
                    (finite-unrank finite-field-unrank)
                    (finite-bound finite-field-bound))
           :in-theory (union-theories (theory 'minimal-theory)
                                      (set-difference-theories
                                       (theory 'finite-field-context-instance-theory)
                                       '(finite-field-add-commutative
                                         finite-field-mul-commutative))))))

(defthm equal-of-finite-field-unrank-when-bounded
  (implies (and (natp i) (< i (finite-field-bound))
                (natp j) (< j (finite-field-bound)))
           (equal (equal (finite-field-unrank i) (finite-field-unrank j))
                  (equal i j)))
  :hints (("Goal" :by (:functional-instance equal-of-finite-unrank-when-bounded
                    (finite-fix finite-field-fix)
                    (finite-rank finite-field-rank)
                    (finite-unrank finite-field-unrank)
                    (finite-bound finite-field-bound))
           :in-theory (union-theories (theory 'minimal-theory)
                                      (set-difference-theories
                                       (theory 'finite-field-context-instance-theory)
                                       '(finite-field-add-commutative
                                         finite-field-mul-commutative))))))

(defthm finite-field-ranks-of-zero-and-one-differ
  (not (equal (finite-field-rank (finite-field-zero))
              (finite-field-rank (finite-field-one))))
  :hints (("Goal"
           :use ((:instance finite-field-unrank-of-finite-field-rank
                            (x (finite-field-zero)))
                 (:instance finite-field-unrank-of-finite-field-rank
                            (x (finite-field-one)))
                 (:instance
                  (:theorem (implies (equal a b)
                                     (equal (finite-field-unrank a)
                                            (finite-field-unrank b))))
                  (a (finite-field-rank (finite-field-zero)))
                  (b (finite-field-rank (finite-field-one)))))
           :in-theory (disable finite-field-unrank-of-finite-field-rank))))

(local
 (defthm two-distinct-naturals-below-bound-imply-bound-greater-than-one
   (implies (and (natp a) (natp b) (not (equal a b))
                 (< a bound) (< b bound))
            (< 1 bound))))

(defthm finite-field-bound-greater-than-one
  (< 1 (finite-field-bound))
  :rule-classes (:rewrite :linear)
  :hints (("Goal"
           :use ((:instance
                  two-distinct-naturals-below-bound-imply-bound-greater-than-one
                  (a (finite-field-rank (finite-field-zero)))
                  (b (finite-field-rank (finite-field-one)))
                  (bound (finite-field-bound)))))))
