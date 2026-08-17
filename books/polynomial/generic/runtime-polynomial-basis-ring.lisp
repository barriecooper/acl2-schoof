(in-package "GPOLY")

(include-book "runtime-polynomial-basis-operation-congruence")

; These laws are deliberately unconditional.  Descriptor accessors totalize a
; malformed descriptor, and every operation fixes its arbitrary ACL2 operands.

(local
 (defthm runtime-polynomial-basis-add-of-fix-left-local
   (equal (runtime-polynomial-basis-add
           (runtime-polynomial-basis-fix x descriptor) y descriptor)
          (runtime-polynomial-basis-add x y descriptor))
   :hints (("Goal"
            :use ((:instance runtime-polynomial-basis-add-of-fixes)
                  (:instance runtime-polynomial-basis-add-of-fixes
                             (x (runtime-polynomial-basis-fix x descriptor))))
            :in-theory (enable runtime-polynomial-basis-fix-idempotent)))))

(local
 (defthm runtime-polynomial-basis-add-of-fix-right-local
   (equal (runtime-polynomial-basis-add
           x (runtime-polynomial-basis-fix y descriptor) descriptor)
          (runtime-polynomial-basis-add x y descriptor))
   :hints (("Goal"
            :use ((:instance runtime-polynomial-basis-add-of-fixes)
                  (:instance runtime-polynomial-basis-add-of-fixes
                             (y (runtime-polynomial-basis-fix y descriptor))))
            :in-theory (enable runtime-polynomial-basis-fix-idempotent)))))

(local
 (defthm runtime-polynomial-basis-mul-of-fix-left-local
   (equal (runtime-polynomial-basis-mul
           (runtime-polynomial-basis-fix x descriptor) y descriptor)
          (runtime-polynomial-basis-mul x y descriptor))
   :hints (("Goal"
            :use ((:instance runtime-polynomial-basis-mul-of-fixes)
                  (:instance runtime-polynomial-basis-mul-of-fixes
                             (x (runtime-polynomial-basis-fix x descriptor))))
            :in-theory (enable runtime-polynomial-basis-fix-idempotent)))))

(local
 (defthm runtime-polynomial-basis-mul-of-fix-right-local
   (equal (runtime-polynomial-basis-mul
           x (runtime-polynomial-basis-fix y descriptor) descriptor)
          (runtime-polynomial-basis-mul x y descriptor))
   :hints (("Goal"
            :use ((:instance runtime-polynomial-basis-mul-of-fixes)
                  (:instance runtime-polynomial-basis-mul-of-fixes
                             (y (runtime-polynomial-basis-fix y descriptor))))
            :in-theory (enable runtime-polynomial-basis-fix-idempotent)))))

(defthm runtime-polynomial-basis-add-commutative
  (equal (runtime-polynomial-basis-add x y descriptor)
         (runtime-polynomial-basis-add y x descriptor))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-poly-add-commutative
                            (p (runtime-polynomial-basis-p descriptor))))
           :in-theory (enable runtime-polynomial-basis-add))))

(defthm runtime-polynomial-basis-add-associative
  (equal (runtime-polynomial-basis-add
          (runtime-polynomial-basis-add x y descriptor) z descriptor)
         (runtime-polynomial-basis-add
          x (runtime-polynomial-basis-add y z descriptor) descriptor))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-polynomial-basis-add-of-fix-left-local
                            (x (runtime-p-poly-add x y
                                  (runtime-polynomial-basis-p descriptor)))
                            (y z))
                 (:instance runtime-polynomial-basis-add-of-fix-right-local
                            (x x) (y (runtime-p-poly-add y z
                                           (runtime-polynomial-basis-p descriptor))))
                 (:instance runtime-p-poly-add-associative
                            (p (runtime-polynomial-basis-p descriptor))))
           :in-theory (e/d (runtime-polynomial-basis-add)
                           (runtime-polynomial-basis-fix
                            runtime-p-poly-add)))))

(defthm runtime-polynomial-basis-add-zero-left
  (equal (runtime-polynomial-basis-add
          (runtime-polynomial-basis-zero descriptor) x descriptor)
         (runtime-polynomial-basis-fix x descriptor))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-polynomial-basis-add
                                      runtime-polynomial-basis-zero
                                      runtime-polynomial-basis-fix))))

(defthm runtime-polynomial-basis-add-zero-right
  (equal (runtime-polynomial-basis-add
          x (runtime-polynomial-basis-zero descriptor) descriptor)
         (runtime-polynomial-basis-fix x descriptor))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-polynomial-basis-add-commutative
                            (y (runtime-polynomial-basis-zero descriptor)))
                 (:instance runtime-polynomial-basis-add-zero-left))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-polynomial-basis-add-inverse-left
  (equal (runtime-polynomial-basis-add
          (runtime-polynomial-basis-neg x descriptor) x descriptor)
         (runtime-polynomial-basis-zero descriptor))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-polynomial-basis-add-of-fix-left-local
                            (x (runtime-p-poly-neg
                                x (runtime-polynomial-basis-p descriptor)))
                            (y x))
                 (:instance runtime-p-poly-add-inverse-left
                            (p (runtime-polynomial-basis-p descriptor))))
           :in-theory (e/d (runtime-polynomial-basis-add
                            runtime-polynomial-basis-neg
                            runtime-polynomial-basis-zero)
                           (runtime-polynomial-basis-fix
                            runtime-p-poly-add runtime-p-poly-neg)))))

(defthm runtime-polynomial-basis-add-inverse-right
  (equal (runtime-polynomial-basis-add
          x (runtime-polynomial-basis-neg x descriptor) descriptor)
         (runtime-polynomial-basis-zero descriptor))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-polynomial-basis-add-commutative
                            (y (runtime-polynomial-basis-neg x descriptor)))
                 (:instance runtime-polynomial-basis-add-inverse-left))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-polynomial-basis-sub-is-add-neg
  (equal (runtime-polynomial-basis-sub x y descriptor)
         (runtime-polynomial-basis-add
          x (runtime-polynomial-basis-neg y descriptor) descriptor))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-polynomial-basis-sub))))

(defthm runtime-polynomial-basis-mul-commutative
  (equal (runtime-polynomial-basis-mul x y descriptor)
         (runtime-polynomial-basis-mul y x descriptor))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-poly-mul-commutative
                            (p (runtime-polynomial-basis-p descriptor))))
           :in-theory (enable runtime-polynomial-basis-mul))))

(defthm runtime-polynomial-basis-mul-associative
  (equal (runtime-polynomial-basis-mul
          (runtime-polynomial-basis-mul x y descriptor) z descriptor)
         (runtime-polynomial-basis-mul
          x (runtime-polynomial-basis-mul y z descriptor) descriptor))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-polynomial-basis-mul-of-fix-left-local
                            (x (runtime-p-poly-mul x y
                                  (runtime-polynomial-basis-p descriptor)))
                            (y z))
                 (:instance runtime-polynomial-basis-mul-of-fix-right-local
                            (x x) (y (runtime-p-poly-mul y z
                                           (runtime-polynomial-basis-p descriptor))))
                 (:instance runtime-p-poly-mul-associative
                            (p (runtime-polynomial-basis-p descriptor))))
           :in-theory (e/d (runtime-polynomial-basis-mul)
                           (runtime-polynomial-basis-fix
                            runtime-p-poly-mul)))))

(defthm runtime-polynomial-basis-mul-one-left
  (equal (runtime-polynomial-basis-mul
          (runtime-polynomial-basis-one descriptor) x descriptor)
         (runtime-polynomial-basis-fix x descriptor))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-polynomial-basis-mul-of-fixes
                            (x (runtime-p-polynomial-one
                                (runtime-polynomial-basis-p descriptor)))
                            (y x))
                 (:instance runtime-p-poly-mul-one-left
                            (p (runtime-polynomial-basis-p descriptor))))
           :in-theory (enable runtime-polynomial-basis-one
                              runtime-polynomial-basis-mul
                              runtime-polynomial-basis-fix))))

(defthm runtime-polynomial-basis-mul-one-right
  (equal (runtime-polynomial-basis-mul
          x (runtime-polynomial-basis-one descriptor) descriptor)
         (runtime-polynomial-basis-fix x descriptor))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-polynomial-basis-mul-commutative
                            (y (runtime-polynomial-basis-one descriptor)))
                 (:instance runtime-polynomial-basis-mul-one-left))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-polynomial-basis-mul-left-distributive
  (equal (runtime-polynomial-basis-mul
          x (runtime-polynomial-basis-add y z descriptor) descriptor)
         (runtime-polynomial-basis-add
          (runtime-polynomial-basis-mul x y descriptor)
          (runtime-polynomial-basis-mul x z descriptor) descriptor))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-polynomial-basis-mul-of-fix-right-local
                            (x x)
                            (y (runtime-p-poly-add
                                y z (runtime-polynomial-basis-p descriptor))))
                 (:instance runtime-polynomial-basis-add-of-fixes
                            (x (runtime-p-poly-mul
                                x y (runtime-polynomial-basis-p descriptor)))
                            (y (runtime-p-poly-mul
                                x z (runtime-polynomial-basis-p descriptor))))
                 (:instance runtime-p-poly-mul-left-distributive
                            (p (runtime-polynomial-basis-p descriptor))))
           :in-theory (e/d (runtime-polynomial-basis-add
                            runtime-polynomial-basis-mul)
                           (runtime-polynomial-basis-fix
                            runtime-p-poly-add runtime-p-poly-mul)))))

(defthm runtime-polynomial-basis-mul-right-distributive
  (equal (runtime-polynomial-basis-mul
          (runtime-polynomial-basis-add x y descriptor) z descriptor)
         (runtime-polynomial-basis-add
          (runtime-polynomial-basis-mul x z descriptor)
          (runtime-polynomial-basis-mul y z descriptor) descriptor))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-polynomial-basis-mul-commutative
                            (x (runtime-polynomial-basis-add x y descriptor))
                            (y z))
                 (:instance runtime-polynomial-basis-mul-left-distributive
                            (x z) (y x) (z y))
                 (:instance runtime-polynomial-basis-mul-commutative
                            (x z) (y x))
                 (:instance runtime-polynomial-basis-mul-commutative
                            (x z) (y y)))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-polynomial-basis-commutative-ring-laws
  (and (equal (runtime-polynomial-basis-add x y descriptor)
              (runtime-polynomial-basis-add y x descriptor))
       (equal (runtime-polynomial-basis-add
               (runtime-polynomial-basis-add x y descriptor) z descriptor)
              (runtime-polynomial-basis-add
               x (runtime-polynomial-basis-add y z descriptor) descriptor))
       (equal (runtime-polynomial-basis-add
               (runtime-polynomial-basis-zero descriptor) x descriptor)
              (runtime-polynomial-basis-fix x descriptor))
       (equal (runtime-polynomial-basis-add
               x (runtime-polynomial-basis-zero descriptor) descriptor)
              (runtime-polynomial-basis-fix x descriptor))
       (equal (runtime-polynomial-basis-add
               (runtime-polynomial-basis-neg x descriptor) x descriptor)
              (runtime-polynomial-basis-zero descriptor))
       (equal (runtime-polynomial-basis-add
               x (runtime-polynomial-basis-neg x descriptor) descriptor)
              (runtime-polynomial-basis-zero descriptor))
       (equal (runtime-polynomial-basis-mul x y descriptor)
              (runtime-polynomial-basis-mul y x descriptor))
       (equal (runtime-polynomial-basis-mul
               (runtime-polynomial-basis-mul x y descriptor) z descriptor)
              (runtime-polynomial-basis-mul
               x (runtime-polynomial-basis-mul y z descriptor) descriptor))
       (equal (runtime-polynomial-basis-mul
               (runtime-polynomial-basis-one descriptor) x descriptor)
              (runtime-polynomial-basis-fix x descriptor))
       (equal (runtime-polynomial-basis-mul
               x (runtime-polynomial-basis-one descriptor) descriptor)
              (runtime-polynomial-basis-fix x descriptor))
       (equal (runtime-polynomial-basis-mul
               x (runtime-polynomial-basis-add y z descriptor) descriptor)
              (runtime-polynomial-basis-add
               (runtime-polynomial-basis-mul x y descriptor)
               (runtime-polynomial-basis-mul x z descriptor) descriptor))
       (equal (runtime-polynomial-basis-mul
               (runtime-polynomial-basis-add x y descriptor) z descriptor)
              (runtime-polynomial-basis-add
               (runtime-polynomial-basis-mul x z descriptor)
               (runtime-polynomial-basis-mul y z descriptor) descriptor)))
  :rule-classes nil
  :hints (("Goal"
           :use (runtime-polynomial-basis-add-commutative
                 runtime-polynomial-basis-add-associative
                 runtime-polynomial-basis-add-zero-left
                 runtime-polynomial-basis-add-zero-right
                 runtime-polynomial-basis-add-inverse-left
                 runtime-polynomial-basis-add-inverse-right
                 runtime-polynomial-basis-mul-commutative
                 runtime-polynomial-basis-mul-associative
                 runtime-polynomial-basis-mul-one-left
                 runtime-polynomial-basis-mul-one-right
                 runtime-polynomial-basis-mul-left-distributive
                 runtime-polynomial-basis-mul-right-distributive)
           :in-theory (theory 'minimal-theory))))
