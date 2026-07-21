(in-package "HS")

(include-book "eval")
(include-book
 "workshops/2022/gamboa-primitive-roots/pfield-polynomial"
 :dir :system)

; The two libraries use the same constant-first list layout.  Keep an explicit
; boundary function nevertheless: callers need not depend on that coincidence,
; and a future target representation change stays local to this book.
(defun hs-to-pfield-polynomial (poly)
  (if (consp poly)
      (cons (car poly) (hs-to-pfield-polynomial (cdr poly)))
    nil))

(defthm hs-to-pfield-polynomial-of-nil
  (equal (hs-to-pfield-polynomial nil) nil))

(defthm integer-polynomial-p-of-hs-to-pfield-polynomial
  (implies (field-polynomial-p poly p)
           (acl2::integer-polynomial-p
            (hs-to-pfield-polynomial poly))))

(defthm hs-to-pfield-polynomial-reconstructs-field-polynomial
  (implies (field-polynomial-p poly p)
           (equal (hs-to-pfield-polynomial poly) poly)))

(defthm hs-to-pfield-polynomial-of-poly-normalize
  (equal (hs-to-pfield-polynomial (poly-normalize poly))
         (poly-normalize (hs-to-pfield-polynomial poly))))

(defthm integerp-of-eval-polynomial-of-hs-to-pfield-polynomial
  (implies (and (field-polynomial-p poly p)
                (integerp x))
           (integerp
            (acl2::eval-polynomial (hs-to-pfield-polynomial poly) x)))
  :hints (("Goal"
           :induct (field-polynomial-p poly p)
           :in-theory (enable acl2::eval-polynomial))))

(defthm integerp-of-eval-polynomial-when-field-polynomial-p
  (implies (and (field-polynomial-p poly p)
                (integerp x))
           (integerp (acl2::eval-polynomial poly x)))
  :hints (("Goal"
           :induct (field-polynomial-p poly p)
           :in-theory (enable acl2::eval-polynomial))))

(defthm mod-of-horner-step-when-tail-mods-agree
  (implies (and (integerp coefficient)
                (integerp x)
                (integerp left-tail)
                (integerp right-tail)
                (integerp p)
                (< 0 p)
                (equal (mod left-tail p) (mod right-tail p)))
           (equal (mod (+ coefficient (* x left-tail)) p)
                  (mod (+ coefficient (* x right-tail)) p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance acl2::mod-of-*-of-mod
                            (acl2::x x) (acl2::x1 left-tail) (acl2::z p))
                 (:instance acl2::mod-of-*-of-mod
                            (acl2::x x) (acl2::x1 right-tail) (acl2::z p))
                 (:instance acl2::mod-of-+-of-mod-arg2
                            (acl2::x1 coefficient)
                            (acl2::x2 (* x left-tail))
                            (acl2::y p))
                 (:instance acl2::mod-of-+-of-mod-arg2
                            (acl2::x1 coefficient)
                            (acl2::x2 (* x right-tail))
                            (acl2::y p))))))

(defthm eval-pfield-polynomial-agrees-with-poly-eval
  (implies (and (field-polynomial-p poly p)
                (pfield::fep x p)
                (posp p))
           (equal (pfield::eval-pfield-polynomial poly x p)
                  (poly-eval poly x p)))
  :hints (("Goal"
           :induct (field-polynomial-p poly p)
           :in-theory (enable pfield::eval-pfield-polynomial
                            acl2::eval-polynomial
                            pfield::add
                            pfield::mul))
          ("Subgoal *1/2"
           :use ((:instance mod-of-horner-step-when-tail-mods-agree
                            (coefficient (car poly))
                            (left-tail (acl2::eval-polynomial (cdr poly) x))
                            (right-tail (poly-eval (cdr poly) x p)))))))

(defthm eval-pfield-polynomial-of-hs-to-pfield-polynomial
  (implies (and (field-polynomial-p poly p)
                (pfield::fep x p)
                (posp p))
           (equal (pfield::eval-pfield-polynomial
                   (hs-to-pfield-polynomial poly) x p)
                  (poly-eval poly x p))))

(defthm pfield-polynomial-root-p-of-hs-to-pfield-polynomial
  (implies (and (field-polynomial-p poly p)
                (pfield::fep x p)
                (posp p))
           (iff (pfield::pfield-polynomial-root-p
                 (hs-to-pfield-polynomial poly) x p)
                (equal (poly-eval poly x p) 0)))
  :hints (("Goal"
           :in-theory (enable pfield::pfield-polynomial-root-p))))
