(in-package "GPOLY")

(include-book "runtime-polynomial-basis")
(include-book "runtime-p-monic-remainder-operations")

(local
 (defthm runtime-polynomial-basis-modulus-normalized-local
   (equal (runtime-p-normalize
           (runtime-polynomial-basis-modulus descriptor)
           (runtime-polynomial-basis-p descriptor))
          (runtime-polynomial-basis-modulus descriptor))
   :hints (("Goal"
            :in-theory (enable runtime-polynomial-basis-modulus
                               runtime-polynomial-basis-p
                               runtime-polynomial-basis-descriptor-fix
                               runtime-polynomial-basis-default-descriptor
                               runtime-polynomial-basis-descriptor-p)))))

(local
 (defthm consp-of-runtime-polynomial-basis-modulus-local
   (consp (runtime-polynomial-basis-modulus descriptor))
   :hints (("Goal"
            :in-theory (enable runtime-polynomial-basis-modulus
                               runtime-polynomial-basis-descriptor-fix
                               runtime-polynomial-basis-default-descriptor
                               runtime-polynomial-basis-descriptor-p)))))

(defthm runtime-polynomial-basis-add-of-fixes
  (equal (runtime-polynomial-basis-add
          (runtime-polynomial-basis-fix x descriptor)
          (runtime-polynomial-basis-fix y descriptor) descriptor)
         (runtime-polynomial-basis-add x y descriptor))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-monic-remainder-of-poly-add
                            (left x) (right y)
                            (g (runtime-polynomial-basis-modulus descriptor))
                            (p (runtime-polynomial-basis-p descriptor))))
           :in-theory (enable runtime-polynomial-basis-add
                              runtime-polynomial-basis-fix))))

(defthm runtime-polynomial-basis-neg-of-fix
  (equal (runtime-polynomial-basis-neg
          (runtime-polynomial-basis-fix x descriptor) descriptor)
         (runtime-polynomial-basis-neg x descriptor))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-monic-remainder-of-poly-neg
                            (value x)
                            (g (runtime-polynomial-basis-modulus descriptor))
                            (p (runtime-polynomial-basis-p descriptor))))
           :in-theory (enable runtime-polynomial-basis-neg
                              runtime-polynomial-basis-fix))))

(defthm runtime-polynomial-basis-sub-of-fixes
  (equal (runtime-polynomial-basis-sub
          (runtime-polynomial-basis-fix x descriptor)
          (runtime-polynomial-basis-fix y descriptor) descriptor)
         (runtime-polynomial-basis-sub x y descriptor))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-polynomial-basis-add-of-fixes
                            (y (runtime-polynomial-basis-neg y descriptor)))
                 (:instance runtime-polynomial-basis-neg-of-fix (x y))
                 (:instance runtime-polynomial-basis-fix-idempotent
                            (x (runtime-p-poly-neg
                                y (runtime-polynomial-basis-p descriptor)))))
           :in-theory (e/d (runtime-polynomial-basis-sub
                            runtime-polynomial-basis-neg)
                           (runtime-polynomial-basis-add
                            runtime-polynomial-basis-fix)))))

(defthm runtime-polynomial-basis-mul-of-fixes
  (equal (runtime-polynomial-basis-mul
          (runtime-polynomial-basis-fix x descriptor)
          (runtime-polynomial-basis-fix y descriptor) descriptor)
         (runtime-polynomial-basis-mul x y descriptor))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-monic-remainder-of-poly-mul
                            (left x) (right y)
                            (g (runtime-polynomial-basis-modulus descriptor))
                            (p (runtime-polynomial-basis-p descriptor))))
           :in-theory (enable runtime-polynomial-basis-mul
                              runtime-polynomial-basis-fix))))
