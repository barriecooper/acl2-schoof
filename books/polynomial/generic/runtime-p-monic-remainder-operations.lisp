(in-package "GPOLY")

(include-book "runtime-p-monic-remainder-coset")

; The following reconstruction rearrangements are proof plumbing.  The public
; boundary is the three remainder compatibility theorems at the end.
(local
 (encapsulate
  ()
  (defthm runtime-p-add-four-rearrange-local
    (equal (runtime-p-poly-add
            (runtime-p-poly-add a b p) (runtime-p-poly-add c d p) p)
           (runtime-p-poly-add
            (runtime-p-poly-add b d p) (runtime-p-poly-add a c p) p))
    :rule-classes nil
    :hints (("Goal"
             :use ((:instance runtime-p-poly-add-associative
                              (x (runtime-p-poly-add a b p)) (y c) (z d))
                   (:instance runtime-p-poly-add-associative
                              (x a) (y b)
                              (z (runtime-p-poly-add c d p)))
                   (:instance runtime-p-poly-add-associative
                              (x b) (y d) (z c))
                   (:instance runtime-p-poly-add-associative
                              (x a) (y (runtime-p-poly-add b d p)) (z c))
                   (:instance runtime-p-poly-add-commutative
                              (x a) (y (runtime-p-poly-add b d p)))
                   (:instance runtime-p-poly-add-associative
                              (x b) (y d) (z a))
                   (:instance runtime-p-poly-add-commutative (x c) (y d))
                   (:instance runtime-p-poly-add-associative
                              (x (runtime-p-poly-add b d p)) (y a) (z c)))
             :in-theory (disable runtime-p-poly-add))))

  (defthm runtime-p-additive-inverse-unique-local
    (implies (equal (runtime-p-poly-add a b p) nil)
             (equal (runtime-p-normalize a p)
                    (runtime-p-poly-neg b p)))
    :hints (("Goal"
             :use ((:instance runtime-p-poly-add-associative
                              (x a) (y b) (z (runtime-p-poly-neg b p)))
                   (:instance runtime-p-poly-add-inverse-right (x b))
                   (:instance runtime-p-poly-add-zero-left
                              (x (runtime-p-poly-neg b p)))
                   (:instance runtime-p-poly-add-zero-right (x a))
                   (:instance runtime-p-normalize-when-canonical
                              (xs (runtime-p-poly-neg b p)))
                   (:instance runtime-p-canonical-polynomial-p-of-poly-neg
                              (x b)))
             :in-theory (theory 'minimal-theory))))

  (defthm runtime-p-poly-neg-of-add-local
    (equal (runtime-p-poly-neg (runtime-p-poly-add x y p) p)
           (runtime-p-poly-add (runtime-p-poly-neg x p)
                               (runtime-p-poly-neg y p) p))
    :hints (("Goal"
             :use ((:instance runtime-p-add-four-rearrange-local
                              (a (runtime-p-poly-neg x p))
                              (b (runtime-p-poly-neg y p)) (c x) (d y))
                   (:instance runtime-p-poly-add-inverse-left (x x))
                   (:instance runtime-p-poly-add-inverse-left (x y))
                   (:instance runtime-p-additive-inverse-unique-local
                              (a (runtime-p-poly-add
                                  (runtime-p-poly-neg x p)
                                  (runtime-p-poly-neg y p) p))
                              (b (runtime-p-poly-add x y p))))
             :in-theory (disable runtime-p-poly-add runtime-p-poly-neg))))

  (defthm runtime-p-poly-mul-swap-last-local
    (equal (runtime-p-poly-mul (runtime-p-poly-mul q g p) x p)
           (runtime-p-poly-mul (runtime-p-poly-mul q x p) g p))
    :rule-classes nil
    :hints (("Goal"
             :use ((:instance runtime-p-poly-mul-associative
                              (x q) (y g) (z x))
                   (:instance runtime-p-poly-mul-commutative (x g) (y x))
                   (:instance runtime-p-poly-mul-associative
                              (x q) (y x) (z g)))
             :in-theory (disable runtime-p-poly-mul))))

  (defthm runtime-p-poly-mul-normalize-left-local
    (equal (runtime-p-poly-mul (runtime-p-normalize x p) y p)
           (runtime-p-poly-mul x y p))
    :hints (("Goal" :in-theory (enable runtime-p-poly-mul))))

  (defthm runtime-p-poly-mul-normalize-right-local
    (equal (runtime-p-poly-mul x (runtime-p-normalize y p) p)
           (runtime-p-poly-mul x y p))
    :hints (("Goal" :in-theory (enable runtime-p-poly-mul))))

  (defthm runtime-p-poly-mul-inner-commute-local
    (equal (runtime-p-poly-mul q (runtime-p-poly-mul g x p) p)
           (runtime-p-poly-mul q (runtime-p-poly-mul x g p) p))
    :rule-classes nil
    :hints (("Goal"
             :use ((:instance runtime-p-poly-mul-commutative (x g) (y x)))
             :in-theory (disable runtime-p-poly-mul))))

  (defthm runtime-p-add-remainders-reconstruction-local
    (equal
     (runtime-p-poly-add left right p)
     (runtime-p-poly-add
      (runtime-p-poly-add
       (runtime-p-monic-remainder left g p)
       (runtime-p-monic-remainder right g p) p)
      (runtime-p-poly-mul
       (runtime-p-poly-add
        (runtime-p-monic-quotient left g p)
        (runtime-p-monic-quotient right g p) p)
       (runtime-p-normalize g p) p) p))
    :rule-classes nil
    :hints
    (("Goal"
      :use ((:instance runtime-p-monic-projection-reconstruction (f left))
            (:instance runtime-p-monic-projection-reconstruction (f right))
            (:instance runtime-p-poly-add-of-normalizes (x left) (y right))
            (:instance runtime-p-add-four-rearrange-local
                       (a (runtime-p-poly-mul
                           (runtime-p-monic-quotient left g p)
                           (runtime-p-normalize g p) p))
                       (b (runtime-p-monic-remainder left g p))
                       (c (runtime-p-poly-mul
                           (runtime-p-monic-quotient right g p)
                           (runtime-p-normalize g p) p))
                       (d (runtime-p-monic-remainder right g p)))
            (:instance runtime-p-poly-mul-right-distributive
                       (x (runtime-p-monic-quotient left g p))
                       (y (runtime-p-monic-quotient right g p))
                       (z (runtime-p-normalize g p)))
            (:instance runtime-p-poly-add-associative
                       (x (runtime-p-poly-mul
                           (runtime-p-monic-quotient left g p)
                           (runtime-p-normalize g p) p))
                       (y (runtime-p-monic-remainder left g p))
                       (z (runtime-p-poly-add
                           (runtime-p-poly-mul
                            (runtime-p-monic-quotient right g p)
                            (runtime-p-normalize g p) p)
                           (runtime-p-monic-remainder right g p) p)))
            (:instance runtime-p-poly-add-associative
                       (x (runtime-p-monic-remainder left g p))
                       (y (runtime-p-poly-mul
                           (runtime-p-monic-quotient right g p)
                           (runtime-p-normalize g p) p))
                       (z (runtime-p-monic-remainder right g p)))
            (:instance runtime-p-poly-add-commutative
                       (x (runtime-p-monic-remainder left g p))
                       (y (runtime-p-poly-mul
                           (runtime-p-monic-quotient right g p)
                           (runtime-p-normalize g p) p)))
            (:instance runtime-p-poly-add-associative
                       (x (runtime-p-poly-mul
                           (runtime-p-monic-quotient left g p)
                           (runtime-p-normalize g p) p))
                       (y (runtime-p-poly-mul
                           (runtime-p-monic-quotient right g p)
                           (runtime-p-normalize g p) p))
                       (z (runtime-p-poly-add
                           (runtime-p-monic-remainder left g p)
                           (runtime-p-monic-remainder right g p) p)))
            (:instance runtime-p-poly-add-commutative
                       (x (runtime-p-poly-mul
                           (runtime-p-poly-add
                            (runtime-p-monic-quotient left g p)
                            (runtime-p-monic-quotient right g p) p)
                           (runtime-p-normalize g p) p))
                       (y (runtime-p-poly-add
                           (runtime-p-monic-remainder left g p)
                           (runtime-p-monic-remainder right g p) p))))
      :in-theory (disable runtime-p-monic-quotient
                          runtime-p-monic-remainder runtime-p-normalize
                          runtime-p-poly-add runtime-p-poly-mul))))

  (defthm runtime-p-neg-remainder-reconstruction-local
    (equal
     (runtime-p-poly-neg value p)
     (runtime-p-poly-add
      (runtime-p-poly-neg (runtime-p-monic-remainder value g p) p)
      (runtime-p-poly-mul
       (runtime-p-poly-neg (runtime-p-monic-quotient value g p) p)
       (runtime-p-normalize g p) p) p))
    :rule-classes nil
    :hints
    (("Goal"
      :use ((:instance runtime-p-monic-projection-reconstruction (f value))
            (:instance runtime-p-poly-neg-of-normalize (x value))
            (:instance runtime-p-poly-neg-of-add-local
                       (x (runtime-p-poly-mul
                           (runtime-p-monic-quotient value g p)
                           (runtime-p-normalize g p) p))
                       (y (runtime-p-monic-remainder value g p)))
            (:instance runtime-p-poly-mul-neg-left
                       (x (runtime-p-monic-quotient value g p))
                       (y (runtime-p-normalize g p)))
            (:instance runtime-p-poly-add-commutative
                       (x (runtime-p-poly-mul
                           (runtime-p-poly-neg
                            (runtime-p-monic-quotient value g p) p)
                           (runtime-p-normalize g p) p))
                       (y (runtime-p-poly-neg
                           (runtime-p-monic-remainder value g p) p))))
      :in-theory (disable runtime-p-monic-quotient
                          runtime-p-monic-remainder runtime-p-normalize
                          runtime-p-poly-add runtime-p-poly-neg
                          runtime-p-poly-mul))))

  (defthm runtime-p-mul-left-projection-local
    (equal
     (runtime-p-poly-mul left right p)
     (runtime-p-poly-mul
      (runtime-p-poly-add
       (runtime-p-poly-mul (runtime-p-monic-quotient left g p)
                           (runtime-p-normalize g p) p)
       (runtime-p-monic-remainder left g p) p)
      right p))
    :rule-classes nil
    :hints (("Goal"
             :use ((:instance runtime-p-monic-projection-reconstruction
                              (f left))
                   (:instance runtime-p-poly-mul-normalize-left-local
                              (x left) (y right)))
             :in-theory (disable runtime-p-monic-quotient
                                 runtime-p-monic-remainder runtime-p-normalize
                                 runtime-p-poly-add runtime-p-poly-mul))))

  (defthm runtime-p-mul-left-distributed-local
    (equal
     (runtime-p-poly-mul
      (runtime-p-poly-add
       (runtime-p-poly-mul (runtime-p-monic-quotient left g p)
                           (runtime-p-normalize g p) p)
       (runtime-p-monic-remainder left g p) p)
      right p)
     (runtime-p-poly-add
      (runtime-p-poly-mul
       (runtime-p-poly-mul (runtime-p-monic-quotient left g p)
                           (runtime-p-normalize g p) p)
       right p)
      (runtime-p-poly-mul (runtime-p-monic-remainder left g p) right p) p))
    :rule-classes nil
    :hints (("Goal" :by (:instance runtime-p-poly-mul-right-distributive
                                    (x (runtime-p-poly-mul
                                        (runtime-p-monic-quotient left g p)
                                        (runtime-p-normalize g p) p))
                                    (y (runtime-p-monic-remainder left g p))
                                    (z right)))))

  (defthm runtime-p-mul-left-remainder-reconstruction-local
    (equal
     (runtime-p-poly-mul left right p)
     (runtime-p-poly-add
      (runtime-p-poly-mul
       (runtime-p-poly-mul (runtime-p-monic-quotient left g p)
                           (runtime-p-normalize g p) p)
       right p)
      (runtime-p-poly-mul (runtime-p-monic-remainder left g p) right p) p))
    :rule-classes nil
    :hints (("Goal"
             :use (runtime-p-mul-left-projection-local
                   runtime-p-mul-left-distributed-local)
             :in-theory (theory 'minimal-theory))))

  (defthm runtime-p-mul-left-remainder-multiple-local
    (equal
     (runtime-p-poly-mul left right p)
     (runtime-p-poly-add
      (runtime-p-poly-mul (runtime-p-monic-remainder left g p) right p)
      (runtime-p-poly-mul
       (runtime-p-poly-mul
        (runtime-p-monic-quotient left g p) right p)
       (runtime-p-normalize g p) p) p))
    :rule-classes nil
    :hints (("Goal"
             :use (runtime-p-mul-left-remainder-reconstruction-local
                   (:instance runtime-p-poly-mul-swap-last-local
                              (q (runtime-p-monic-quotient left g p))
                              (g (runtime-p-normalize g p)) (x right))
                   (:instance runtime-p-poly-add-commutative
                              (x (runtime-p-poly-mul
                                  (runtime-p-poly-mul
                                   (runtime-p-monic-quotient left g p)
                                   (runtime-p-normalize g p) p)
                                  right p))
                              (y (runtime-p-poly-mul
                                  (runtime-p-monic-remainder left g p)
                                  right p)))
                   (:instance runtime-p-poly-add-commutative
                              (x (runtime-p-poly-mul
                                  (runtime-p-monic-quotient left g p)
                                  (runtime-p-poly-mul
                                   right (runtime-p-normalize g p) p) p))
                              (y (runtime-p-poly-mul
                                  (runtime-p-monic-remainder left g p)
                                  right p))))
             :in-theory (theory 'minimal-theory))))))

(defthm runtime-p-monic-remainder-of-poly-add
  (implies
   (and (consp (runtime-p-normalize g p))
        (equal (runtime-p-poly-leading-coefficient
                (runtime-p-normalize g p) p)
               (runtime-p-one p)))
   (equal
    (runtime-p-monic-remainder (runtime-p-poly-add left right p) g p)
    (runtime-p-monic-remainder
     (runtime-p-poly-add
      (runtime-p-monic-remainder left g p)
      (runtime-p-monic-remainder right g p) p)
     g p)))
  :rule-classes nil
  :hints (("Goal"
           :use (runtime-p-add-remainders-reconstruction-local
                 (:instance runtime-p-monic-remainder-of-poly-add-modulus-multiple
                            (f (runtime-p-poly-add
                                (runtime-p-monic-remainder left g p)
                                (runtime-p-monic-remainder right g p) p))
                            (q (runtime-p-poly-add
                                (runtime-p-monic-quotient left g p)
                                (runtime-p-monic-quotient right g p) p))))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-p-monic-remainder-of-poly-neg
  (implies
   (and (consp (runtime-p-normalize g p))
        (equal (runtime-p-poly-leading-coefficient
                (runtime-p-normalize g p) p)
               (runtime-p-one p)))
   (equal
    (runtime-p-monic-remainder (runtime-p-poly-neg value p) g p)
    (runtime-p-monic-remainder
     (runtime-p-poly-neg (runtime-p-monic-remainder value g p) p) g p)))
  :rule-classes nil
  :hints (("Goal"
           :use (runtime-p-neg-remainder-reconstruction-local
                 (:instance runtime-p-monic-remainder-of-poly-add-modulus-multiple
                            (f (runtime-p-poly-neg
                                (runtime-p-monic-remainder value g p) p))
                            (q (runtime-p-poly-neg
                                (runtime-p-monic-quotient value g p) p))))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-p-monic-remainder-of-poly-mul-left-remainder
  (implies
   (and (consp (runtime-p-normalize g p))
        (equal (runtime-p-poly-leading-coefficient
                (runtime-p-normalize g p) p)
               (runtime-p-one p)))
   (equal
    (runtime-p-monic-remainder (runtime-p-poly-mul left right p) g p)
    (runtime-p-monic-remainder
     (runtime-p-poly-mul (runtime-p-monic-remainder left g p) right p)
     g p)))
  :rule-classes nil
  :hints (("Goal"
           :use (runtime-p-mul-left-remainder-multiple-local
                 (:instance runtime-p-monic-remainder-of-poly-add-modulus-multiple
                            (f (runtime-p-poly-mul
                                (runtime-p-monic-remainder left g p) right p))
                            (q (runtime-p-poly-mul
                                (runtime-p-monic-quotient left g p) right p))))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-p-monic-remainder-of-poly-mul-right-remainder
  (implies
   (and (consp (runtime-p-normalize g p))
        (equal (runtime-p-poly-leading-coefficient
                (runtime-p-normalize g p) p)
               (runtime-p-one p)))
   (equal
    (runtime-p-monic-remainder (runtime-p-poly-mul left right p) g p)
    (runtime-p-monic-remainder
     (runtime-p-poly-mul left (runtime-p-monic-remainder right g p) p)
     g p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-monic-remainder-of-poly-mul-left-remainder
                            (left right) (right left))
                 (:instance runtime-p-poly-mul-commutative
                            (x left) (y right))
                 (:instance runtime-p-poly-mul-commutative
                            (x (runtime-p-monic-remainder right g p))
                            (y left)))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-p-monic-remainder-of-poly-mul
  (implies
   (and (consp (runtime-p-normalize g p))
        (equal (runtime-p-poly-leading-coefficient
                (runtime-p-normalize g p) p)
               (runtime-p-one p)))
   (equal
    (runtime-p-monic-remainder (runtime-p-poly-mul left right p) g p)
    (runtime-p-monic-remainder
     (runtime-p-poly-mul
      (runtime-p-monic-remainder left g p)
      (runtime-p-monic-remainder right g p) p)
     g p)))
  :rule-classes nil
  :hints (("Goal"
           :use (runtime-p-monic-remainder-of-poly-mul-left-remainder
                 (:instance runtime-p-monic-remainder-of-poly-mul-right-remainder
                            (left (runtime-p-monic-remainder left g p))))
           :in-theory (theory 'minimal-theory))))
