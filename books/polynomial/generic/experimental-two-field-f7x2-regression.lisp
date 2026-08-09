(in-package "GPOLY")

(include-book "../../field/experimental-two-field-context")
(include-book "f7x2-field")
(include-book "f7x2-frobenius-witness")
(include-book "tools/def-functional-instance" :dir :system)

(defun f7x2-experimental-context-p () t)
(defun f7x2-experimental-q () 7)
(defun f7x2-experimental-nonidentity-witness () '(0 1))

(defun f7x2-natural-pow-linear (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp (nfix exponent))
      (f7x2-one)
    (f7x2-mul (f7x2-fix value)
              (f7x2-natural-pow-linear value (1- (nfix exponent))))))

; The seventh-power branch is a certified repeated-multiplication
; specialization; all other exponents retain the transparent linear rule.
(defun f7x2-natural-pow (value exponent)
  (if (equal (nfix exponent) 7)
      (f7x2-seventh-power value)
    (f7x2-natural-pow-linear value exponent)))

(defthm f7x2-natural-pow-seven-is-seventh-power
  (equal (f7x2-natural-pow value 7) (f7x2-seventh-power value))
  :hints (("Goal" :expand ((f7x2-natural-pow value 7))
           :in-theory (union-theories '(nfix)
                                      (theory 'minimal-theory)))))

(local
 (defthm f7-fix-of-f7x2-base-projection
   (equal (gfield::f7-fix (f7x2-base-projection value))
          (f7x2-base-projection value))
   :hints (("Goal" :in-theory
            (union-theories '(f7x2-base-projection
                               gfield::f7-fix-idempotent)
                            (theory 'minimal-theory))))))


(defthm f7x2-element-p-of-experimental-x
  (f7x2-element-p (f7x2-experimental-nonidentity-witness))
  :hints (("Goal" :in-theory (enable f7x2-experimental-nonidentity-witness
                                      f7x2-element-p))))


(defthm f7x2-experimental-seam-facts
  (and
   (equal (f7x2-embed-f7 (gfield::f7-fix x)) (f7x2-embed-f7 x))
   (f7x2-element-p (f7x2-embed-f7 x))
   (equal (f7x2-fix (f7x2-embed-f7 x)) (f7x2-embed-f7 x))
   (equal (equal (f7x2-embed-f7 x) (f7x2-embed-f7 y))
          (equal (gfield::f7-fix x) (gfield::f7-fix y)))
   (equal (f7x2-embed-f7 (gfield::f7-zero)) (f7x2-zero))
   (equal (f7x2-embed-f7 (gfield::f7-one)) (f7x2-one))
   (equal (f7x2-embed-f7 (gfield::f7-add x y))
          (f7x2-add (f7x2-embed-f7 x) (f7x2-embed-f7 y)))
   (equal (f7x2-embed-f7 (gfield::f7-mul x y))
          (f7x2-mul (f7x2-embed-f7 x) (f7x2-embed-f7 y)))
   (equal (f7x2-embed-f7 (gfield::f7-neg x))
          (f7x2-neg (f7x2-embed-f7 x)))
   (posp (f7x2-experimental-q))
   (equal (f7x2-conjugate x)
          (f7x2-natural-pow x (f7x2-experimental-q)))
   (equal (f7x2-conjugate (f7x2-fix x)) (f7x2-conjugate x))
   (f7x2-element-p (f7x2-conjugate x))
   (equal (f7x2-fix (f7x2-conjugate x)) (f7x2-conjugate x))
   (equal (f7x2-conjugate (f7x2-zero)) (f7x2-zero))
   (equal (f7x2-conjugate (f7x2-one)) (f7x2-one))
   (equal (f7x2-conjugate (f7x2-add x y))
          (f7x2-add (f7x2-conjugate x) (f7x2-conjugate y)))
   (equal (f7x2-conjugate (f7x2-mul x y))
          (f7x2-mul (f7x2-conjugate x) (f7x2-conjugate y)))
   (equal (f7x2-conjugate (f7x2-neg x))
          (f7x2-neg (f7x2-conjugate x)))
   (equal (f7x2-conjugate (f7x2-embed-f7 x)) (f7x2-embed-f7 x))
   (and (f7x2-element-p (f7x2-experimental-nonidentity-witness))
        (not (equal (f7x2-conjugate (f7x2-experimental-nonidentity-witness))
                    (f7x2-fix (f7x2-experimental-nonidentity-witness)))))
   (booleanp (f7x2-embedded-image-p x))
   (equal (f7x2-embedded-image-p x)
          (equal (f7x2-fix x)
                 (f7x2-embed-f7
                  (gfield::f7-fix (f7x2-base-projection x)))))
   (equal (equal (f7x2-conjugate x) (f7x2-fix x))
          (f7x2-embedded-image-p x))
   (equal (f7x2-embedded-image-p (f7x2-fix x))
          (f7x2-embedded-image-p x)))
  :rule-classes nil
  :hints (("Goal"
           :use (f7x2-conjugate-moves-x f7x2-element-p-of-experimental-x)
           :in-theory
           (union-theories
            '(posp f7x2-experimental-q f7x2-experimental-nonidentity-witness
              f7x2-embedded-image-p f7-fix-of-f7x2-base-projection
              f7x2-embed-f7-of-fix f7x2-element-p-of-embed-f7
              f7x2-fix-when-f7x2-element-p f7x2-embed-f7-injective
              f7x2-embed-f7-zero f7x2-embed-f7-one f7x2-embed-f7-add
              f7x2-embed-f7-mul f7x2-embed-f7-neg
              f7x2-natural-pow-seven-is-seventh-power
              f7x2-seventh-power-equals-conjugate f7x2-conjugate-of-fix
              f7x2-element-p-of-conjugate f7x2-conjugate-zero
              f7x2-conjugate-one f7x2-conjugate-add f7x2-conjugate-mul
              f7x2-conjugate-neg f7x2-conjugate-of-embed-f7
              booleanp-of-f7x2-embedded-image-p
              f7x2-conjugate-fixed-iff-embedded-image
              f7x2-embedded-image-p-of-fix)
            (theory 'minimal-theory)))))

(acl2::def-functional-instance
 f7x2-experimental-two-field-consequence
 gfield::two-field-frobenius-fixed-iff-embedded-fixed-projection
 ((gfield::two-field-context-p f7x2-experimental-context-p)
  (gfield::two-field-base-element-p gfield::f7-element-p)
  (gfield::two-field-base-fix gfield::f7-fix)
  (gfield::two-field-base-zero gfield::f7-zero)
  (gfield::two-field-base-one gfield::f7-one)
  (gfield::two-field-base-add gfield::f7-add)
  (gfield::two-field-base-mul gfield::f7-mul)
  (gfield::two-field-base-neg gfield::f7-neg)
  (gfield::two-field-ambient-element-p f7x2-element-p)
  (gfield::two-field-ambient-fix f7x2-fix)
  (gfield::two-field-ambient-zero f7x2-zero)
  (gfield::two-field-ambient-one f7x2-one)
  (gfield::two-field-ambient-add f7x2-add)
  (gfield::two-field-ambient-mul f7x2-mul)
  (gfield::two-field-ambient-neg f7x2-neg)
  (gfield::two-field-embed f7x2-embed-f7)
  (gfield::two-field-q f7x2-experimental-q)
  (gfield::two-field-ambient-pow f7x2-natural-pow)
  (gfield::two-field-frobenius f7x2-conjugate)
  (gfield::two-field-base-projection f7x2-base-projection)
  (gfield::two-field-embedded-image-p f7x2-embedded-image-p)
  (gfield::two-field-nonidentity-witness
   f7x2-experimental-nonidentity-witness))
 :rule-classes nil
 :hints
 (("Goal" :do-not '(preprocess) :in-theory (theory 'minimal-theory))
  (and stable-under-simplificationp
       '(:computed-hint-replacement t
         :use ((:instance f7x2-experimental-seam-facts
                          (x gfield::x) (y gfield::y)))
         :in-theory (theory 'minimal-theory)))
 )
 :by-hint-p t)
