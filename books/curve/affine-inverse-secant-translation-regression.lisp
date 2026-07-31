(in-package "GFIELD")

(include-book "affine-inverse-secant-translation")

(defthm affine-inverse-secant-ordinate-coincidence-client-regression
  (implies
   (and (affine-opposite-y-infinity-relation-p a b infinity)
        (affine-distinct-x-secant-relation-p b c witness output)
        (equal (affine-coordinates-x output) (affine-coordinates-x a)))
   (equal (affine-coordinates-y output) (affine-coordinates-y a)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance
                          affine-inverse-secant-coincident-x-implies-ordinate-equality
                          (r witness) (u output)))
           :in-theory (theory 'minimal-theory))))

(defthm affine-inverse-secant-outer-distinct-x-client-regression
  (implies
   (and (affine-opposite-y-infinity-relation-p a b infinity)
        (affine-distinct-x-secant-relation-p b c witness output)
        (not (equal (affine-coordinates-x output)
                    (affine-coordinates-x a))))
   (affine-distinct-x-secant-relation-p
    a output (field-neg (field-fix witness)) c))
  :rule-classes nil
  :hints (("Goal" :use ((:instance
                          affine-inverse-secant-translation-outer-distinct-x
                          (r witness) (u output)))
           :in-theory (theory 'minimal-theory))))

(defthm affine-inverse-secant-outer-doubling-client-regression
  (implies
   (and (short-weierstrass-characteristic-p)
        (affine-opposite-y-infinity-relation-p a b infinity)
        (affine-distinct-x-secant-relation-p b c witness output)
        (equal (affine-coordinates-x output) (affine-coordinates-x a)))
   (affine-doubling-relation-p
    a (field-neg (field-fix witness)) c))
  :rule-classes nil
  :hints (("Goal" :use ((:instance
                          affine-inverse-secant-translation-outer-doubling
                          (r witness) (u output)))
           :in-theory (theory 'minimal-theory))))

(defthm affine-inverse-secant-translation-client-regression
  (implies
   (and (short-weierstrass-characteristic-p)
        (affine-opposite-y-infinity-relation-p a b infinity)
        (affine-distinct-x-secant-relation-p b c witness output))
   (or (affine-distinct-x-secant-relation-p
        a output (field-neg (field-fix witness)) c)
       (affine-doubling-relation-p
        a (field-neg (field-fix witness)) c)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance affine-inverse-secant-translation
                                    (r witness) (u output)))
           :in-theory (theory 'minimal-theory))))
