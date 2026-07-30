(in-package "GFIELD")

(include-book "curve-addition-structural-interface")

(defthm classifier-symmetry-client-regression
  (equal (affine-pair-classify q p) (affine-pair-classify p q))
  :hints (("Goal" :use (:instance affine-pair-classify-symmetric
                                   (first p) (second q))
                   :in-theory (theory 'minimal-theory))))

(defthm fixed-classifier-consequences-client-regression
  (and
   (implies (equal (affine-pair-classify p q) :opposite-y)
            (equal (affine-coordinates-y (affine-coordinates-fix q))
                   (field-neg
                    (affine-coordinates-y (affine-coordinates-fix p)))))
   (implies (equal (affine-pair-classify p q) :same-point-non-opposite)
            (equal (affine-coordinates-fix p)
                   (affine-coordinates-fix q))))
  :hints (("Goal"
           :use ((:instance affine-pair-classify-opposite-y-implies-fixed-coordinates
                            (first p) (second q))
                 (:instance affine-pair-classify-same-point-non-opposite-implies-fixed-equal
                            (first p) (second q)))
           :in-theory (theory 'minimal-theory))))

(defthm outer-impossibility-client-regression
  (implies
   (and (short-weierstrass-affine-point-p p)
        (short-weierstrass-affine-point-p q)
        (short-weierstrass-affine-point-p r)
        (equal (affine-pair-classify p q) :distinct-x))
   (not (equal (affine-pair-classify r (affine-distinct-x-output p q))
               :same-x-other)))
  :hints (("Goal"
           :use ((:instance affine-pair-classify-distinct-x-output-not-same-x-other
                            (first p) (second q) (third r))
                 (:instance affine-pair-classify-symmetric
                            (first r)
                            (second (affine-distinct-x-output p q))))
           :in-theory (theory 'minimal-theory))))

(defthm infinity-associativity-client-regression
  (implies
   (and (short-weierstrass-curve-point-p p)
        (short-weierstrass-curve-point-p q))
   (equal
    (curve-point-pair-output-point
     (curve-point-pair-output-point p (curve-point-infinity)) q)
    (curve-point-pair-output-point
     p (curve-point-pair-output-point (curve-point-infinity) q))))
  :hints (("Goal"
           :use
           ((:instance curve-point-pair-output-point-associative-when-infinity-input
                       (a p) (b (curve-point-infinity)) (c q))
            short-weierstrass-curve-point-p-of-infinity
            curve-point-infinity-representation)
           :in-theory (theory 'minimal-theory))))

(defthm opposite-y-chain-endpoint-client-regression
  (implies
   (and (equal (affine-pair-classify p q) :opposite-y)
        (equal (affine-pair-classify q r) :opposite-y))
   (equal (affine-coordinates-fix p)
          (affine-coordinates-fix r)))
  :hints
  (("Goal"
    :use
    (:instance affine-pair-classify-opposite-y-chain-implies-fixed-endpoints-equal
               (a p) (b q) (c r))
    :in-theory (theory 'minimal-theory))))

(defthm both-inner-opposite-y-associativity-client-regression
  (implies
   (and (short-weierstrass-affine-point-p p)
        (short-weierstrass-affine-point-p q)
        (short-weierstrass-affine-point-p r)
        (equal (affine-pair-classify p q) :opposite-y)
        (equal (affine-pair-classify q r) :opposite-y))
   (equal
    (curve-point-pair-output-point
     (curve-point-pair-output-point
      (curve-point-affine-coordinates p)
      (curve-point-affine-coordinates q))
     (curve-point-affine-coordinates r))
    (curve-point-pair-output-point
     (curve-point-affine-coordinates p)
     (curve-point-pair-output-point
      (curve-point-affine-coordinates q)
      (curve-point-affine-coordinates r)))))
  :hints
  (("Goal"
    :use
    (:instance curve-point-pair-output-point-associative-when-both-inner-opposite-y
               (a p) (b q) (c r))
    :in-theory (theory 'minimal-theory))))

(defthm repeated-doubling-fixed-triple-client-regression
  (implies
   (and (equal (affine-pair-classify p q) :same-point-non-opposite)
        (equal (affine-pair-classify q r) :same-point-non-opposite))
   (and (equal (affine-coordinates-fix p) (affine-coordinates-fix q))
        (equal (affine-coordinates-fix q) (affine-coordinates-fix r))
        (equal (affine-coordinates-fix p) (affine-coordinates-fix r))))
  :hints
  (("Goal"
    :use
    (:instance affine-pair-classify-repeated-doubling-implies-fixed-triple
               (a p) (b q) (c r))
    :in-theory (theory 'minimal-theory))))

(defthm both-inner-doubling-associativity-client-regression
  (implies
   (and (short-weierstrass-affine-point-p p)
        (short-weierstrass-affine-point-p q)
        (short-weierstrass-affine-point-p r)
        (equal (affine-pair-classify p q) :same-point-non-opposite)
        (equal (affine-pair-classify q r) :same-point-non-opposite))
   (equal
    (curve-point-pair-output-point
     (curve-point-pair-output-point
      (curve-point-affine-coordinates p)
      (curve-point-affine-coordinates q))
     (curve-point-affine-coordinates r))
    (curve-point-pair-output-point
     (curve-point-affine-coordinates p)
     (curve-point-pair-output-point
      (curve-point-affine-coordinates q)
      (curve-point-affine-coordinates r)))))
  :hints
  (("Goal"
    :use
    (:instance curve-point-pair-output-point-associative-when-both-inner-doubling
               (a p) (b q) (c r))
    :in-theory (theory 'minimal-theory))))
