(in-package "GPOLY")
(include-book "xgcd")

; This is transparent post-processing of the raw XGCD triple.  The inverse of
; the raw gcd's total leading coefficient is exactly the scalar used by
; POLY-MONIC-NORMALIZE; no division or Euclidean recursion occurs here.
(defund poly-monic-extended-euclidean-gcd (first second)
  (mv-let (gcd s coefficient-t)
    (poly-extended-euclidean-gcd first second)
    (let ((scale (gfield::field-inv (poly-leading-coefficient gcd))))
      (mv (poly-monic-normalize gcd)
          (poly-scale scale s)
          (poly-scale scale coefficient-t)))))

(defthm poly-monic-extended-euclidean-gcd-is-scaled-xgcd
  (equal
   (poly-monic-extended-euclidean-gcd first second)
   (mv-let (gcd s coefficient-t)
     (poly-extended-euclidean-gcd first second)
     (let ((scale (gfield::field-inv (poly-leading-coefficient gcd))))
       (mv (poly-monic-normalize gcd)
           (poly-scale scale s)
           (poly-scale scale coefficient-t)))))
  :hints (("Goal" :in-theory (enable poly-monic-extended-euclidean-gcd))))

(defthm poly-monic-extended-euclidean-gcd-gcd-is-monic-euclidean-gcd
  (equal (mv-nth 0 (poly-monic-extended-euclidean-gcd first second))
         (poly-monic-euclidean-gcd first second))
  :hints
  (("Goal"
    :use ((:instance
           poly-extended-euclidean-gcd-gcd-is-poly-euclidean-gcd)
          (:instance poly-monic-euclidean-gcd-is-monic-normalize)
          (:instance poly-monic-extended-euclidean-gcd-is-scaled-xgcd))
    :in-theory
    (disable poly-monic-extended-euclidean-gcd
             poly-monic-euclidean-gcd poly-monic-normalize
             poly-extended-euclidean-gcd poly-euclidean-gcd
             poly-scale poly-leading-coefficient))))

(defthm poly-monic-extended-euclidean-gcd-gcd-canonical
  (canonical-polynomial-p
   (mv-nth 0 (poly-monic-extended-euclidean-gcd first second)))
  :hints (("Goal" :use ((:instance
                          canonical-polynomial-p-of-poly-monic-euclidean-gcd))
           :in-theory (disable canonical-polynomial-p
                               poly-monic-extended-euclidean-gcd
                               poly-monic-extended-euclidean-gcd-is-scaled-xgcd
                               poly-monic-euclidean-gcd-is-monic-normalize))))

(defthm poly-monic-extended-euclidean-gcd-first-coefficient-canonical
  (canonical-polynomial-p
   (mv-nth 1 (poly-monic-extended-euclidean-gcd first second)))
  :hints (("Goal" :use ((:instance
                          poly-monic-extended-euclidean-gcd-is-scaled-xgcd)
                         (:instance canonical-polynomial-p-of-poly-scale))
           :in-theory (disable canonical-polynomial-p poly-scale
                               poly-monic-extended-euclidean-gcd))))

(defthm poly-monic-extended-euclidean-gcd-second-coefficient-canonical
  (canonical-polynomial-p
   (mv-nth 2 (poly-monic-extended-euclidean-gcd first second)))
  :hints (("Goal" :use ((:instance
                          poly-monic-extended-euclidean-gcd-is-scaled-xgcd)
                         (:instance canonical-polynomial-p-of-poly-scale))
           :in-theory (disable canonical-polynomial-p poly-scale
                               poly-monic-extended-euclidean-gcd))))

(defthm normalize-of-poly-monic-extended-euclidean-gcd-gcd
  (equal (normalize
          (mv-nth 0 (poly-monic-extended-euclidean-gcd first second)))
         (mv-nth 0 (poly-monic-extended-euclidean-gcd first second)))
  :hints (("Goal" :use ((:instance normalize-when-canonical
                                   (xs (mv-nth 0
                                        (poly-monic-extended-euclidean-gcd
                                         first second))))
                          (:instance
                           poly-monic-extended-euclidean-gcd-gcd-canonical))
           :in-theory (disable normalize poly-monic-extended-euclidean-gcd
                               poly-monic-extended-euclidean-gcd-is-scaled-xgcd))))

(defthm normalize-of-poly-monic-extended-euclidean-gcd-first-coefficient
  (equal (normalize
          (mv-nth 1 (poly-monic-extended-euclidean-gcd first second)))
         (mv-nth 1 (poly-monic-extended-euclidean-gcd first second)))
  :hints (("Goal" :use ((:instance normalize-when-canonical
                                   (xs (mv-nth 1
                                        (poly-monic-extended-euclidean-gcd
                                         first second))))
                          (:instance
                           poly-monic-extended-euclidean-gcd-first-coefficient-canonical))
           :in-theory (disable normalize poly-monic-extended-euclidean-gcd
                               poly-monic-extended-euclidean-gcd-is-scaled-xgcd))))

(defthm normalize-of-poly-monic-extended-euclidean-gcd-second-coefficient
  (equal (normalize
          (mv-nth 2 (poly-monic-extended-euclidean-gcd first second)))
         (mv-nth 2 (poly-monic-extended-euclidean-gcd first second)))
  :hints (("Goal" :use ((:instance normalize-when-canonical
                                   (xs (mv-nth 2
                                        (poly-monic-extended-euclidean-gcd
                                         first second))))
                          (:instance
                           poly-monic-extended-euclidean-gcd-second-coefficient-canonical))
           :in-theory (disable normalize poly-monic-extended-euclidean-gcd
                               poly-monic-extended-euclidean-gcd-is-scaled-xgcd))))

(local
 (defthm poly-mul-of-poly-scale-left
   (equal (poly-mul (poly-scale scalar coefficient) input)
          (poly-scale scalar (poly-mul coefficient input)))
   :hints
   (("Goal"
     :use ((:instance poly-mul-associative
                      (x (const scalar)) (y coefficient) (z input))
           (:instance poly-mul-const-left (a scalar) (p coefficient))
           (:instance poly-mul-const-left
                      (a scalar) (p (poly-mul coefficient input))))
     :in-theory (disable poly-mul-const-left poly-scale poly-mul)))))

(local
 (defthm field-inv-of-negative-one
   (equal (gfield::field-inv
           (gfield::field-neg (gfield::field-one)))
          (gfield::field-neg (gfield::field-one)))
   :hints
   (("Goal"
     :use ((:instance gfield::field-multiplicative-inverse-unique
                      (x (gfield::field-neg (gfield::field-one)))
                      (y (gfield::field-neg (gfield::field-one)))))))))

(defthm poly-monic-extended-euclidean-gcd-bezout
  (equal
   (poly-add
    (poly-mul
     (mv-nth 1 (poly-monic-extended-euclidean-gcd first second)) first)
    (poly-mul
     (mv-nth 2 (poly-monic-extended-euclidean-gcd first second)) second))
   (poly-monic-euclidean-gcd first second))
  :hints
  (("Goal"
    :use ((:instance poly-extended-euclidean-gcd-bezout)
          (:instance poly-scale-of-poly-add
                     (a (gfield::field-inv
                         (poly-leading-coefficient
                          (mv-nth 0
                           (poly-extended-euclidean-gcd first second)))))
                     (x (poly-mul
                         (mv-nth 1
                          (poly-extended-euclidean-gcd first second)) first))
                     (y (poly-mul
                         (mv-nth 2
                          (poly-extended-euclidean-gcd first second)) second))))
    :in-theory (e/d (poly-monic-extended-euclidean-gcd
                     poly-monic-euclidean-gcd poly-monic-normalize)
                    (poly-extended-euclidean-gcd-bezout
                     poly-mul poly-add poly-scale
                     poly-leading-coefficient)))))

(defthm poly-monic-extended-euclidean-gcd-bezout-when-one
  (implies
   (equal (poly-monic-euclidean-gcd first second) (polynomial-one))
   (equal
    (poly-add
     (poly-mul
      (mv-nth 1 (poly-monic-extended-euclidean-gcd first second)) first)
     (poly-mul
      (mv-nth 2 (poly-monic-extended-euclidean-gcd first second)) second))
    (polynomial-one)))
  :hints (("Goal" :use poly-monic-extended-euclidean-gcd-bezout)))

; Exact total-boundary regressions.  FIELD-INV(0)=0 and POLY-SCALE(0,_)=NIL,
; so the zero raw gcd produces exactly (MV NIL NIL NIL), unlike raw XGCD.
(defthm poly-monic-extended-euclidean-gcd-regression-boundaries
  (let ((one (polynomial-one)))
    (and
     (equal (poly-monic-extended-euclidean-gcd nil nil) (mv nil nil nil))
     (equal (poly-monic-extended-euclidean-gcd one nil) (mv one one nil))
     (equal (poly-monic-extended-euclidean-gcd nil one) (mv one nil one))
     (equal (poly-monic-extended-euclidean-gcd
             'malformed-first 'malformed-second)
            (mv nil nil nil))
     (equal (poly-monic-extended-euclidean-gcd
             (cons (gfield::field-one) 'malformed-tail) nil)
            (mv one one nil))
     (equal (poly-monic-extended-euclidean-gcd
             (list (gfield::field-one) (gfield::field-zero)) nil)
            (mv one one nil))
     (equal (poly-monic-extended-euclidean-gcd
             (list 'malformed-coefficient (gfield::field-zero)) nil)
            (mv (poly-monic-normalize (list 'malformed-coefficient))
                (const
                 (gfield::field-inv
                  (poly-leading-coefficient (list 'malformed-coefficient))))
                nil))))
  :hints (("Goal" :in-theory (enable poly-monic-extended-euclidean-gcd
                                      poly-extended-euclidean-gcd))))

(defthm poly-monic-extended-euclidean-gcd-regression-negative-unit
  (let* ((minus-one (gfield::field-neg (gfield::field-one)))
         (negative-one (list minus-one)))
    (and
     (equal (poly-extended-euclidean-gcd nil negative-one)
            (mv negative-one nil (polynomial-one)))
     (equal (poly-monic-extended-euclidean-gcd nil negative-one)
            (mv (polynomial-one) nil
                (const (gfield::field-inv minus-one))))))
  :hints (("Goal"
           :use ((:instance
                  poly-monic-euclidean-gcd-regression-raw-negative-unit))
           :in-theory (enable poly-monic-extended-euclidean-gcd
                              poly-extended-euclidean-gcd))))

(defthm poly-monic-extended-euclidean-gcd-regression-polynomials
  (let* ((one (polynomial-one))
         (x (monomial (gfield::field-one) 1))
         (linear (poly-add x one))
         (quadratic (poly-mul linear linear)))
    (and
     (equal (poly-monic-extended-euclidean-gcd quadratic linear)
            (mv linear nil one))
     (equal (poly-monic-extended-euclidean-gcd linear one)
            (mv one nil one))
     (equal (poly-monic-extended-euclidean-gcd
             (poly-add (poly-mul x x) one) x)
            (mv one one (poly-neg x)))))
  :hints (("Goal" :in-theory (enable poly-monic-extended-euclidean-gcd))))

(defthm poly-monic-extended-euclidean-gcd-regression-nonmonic-linear
  (let* ((minus-one (gfield::field-neg (gfield::field-one)))
         (linear (poly-add (monomial (gfield::field-one) 1)
                           (polynomial-one)))
         (negative-linear (poly-scale minus-one linear)))
    (equal (poly-monic-extended-euclidean-gcd negative-linear nil)
           (mv linear (const (gfield::field-inv minus-one)) nil)))
  :hints (("Goal"
           :use ((:instance
                  poly-monic-euclidean-gcd-regression-raw-negative-unit))
           :in-theory (enable poly-monic-extended-euclidean-gcd
                              poly-extended-euclidean-gcd))))

; This multi-step case distinguishes the raw negative-unit gcd from the monic
; result and makes the common rescaling visible in both nonzero coefficients.
(defthm poly-monic-extended-euclidean-gcd-regression-rescales-both
  (let* ((minus-one (gfield::field-neg (gfield::field-one)))
         (x (monomial (gfield::field-one) 1))
         (first (poly-scale
                 minus-one (poly-add (poly-mul x x) (polynomial-one))))
         (second (poly-scale minus-one x)))
    (and
     (equal (poly-extended-euclidean-gcd first second)
            (mv (list minus-one) (polynomial-one) (poly-neg x)))
     (equal (poly-monic-extended-euclidean-gcd first second)
            (mv (polynomial-one) (list minus-one) x))))
  :hints (("Goal" :in-theory (enable poly-monic-extended-euclidean-gcd
                                      poly-extended-euclidean-gcd))))

(defthm poly-monic-extended-euclidean-gcd-regression-reconstruction
  (let* ((minus-one (gfield::field-neg (gfield::field-one)))
         (linear (poly-add (monomial (gfield::field-one) 1)
                           (polynomial-one)))
         (first (poly-scale minus-one linear))
         (result (poly-monic-extended-euclidean-gcd first nil)))
    (and (equal (mv-nth 0 result)
                (poly-monic-euclidean-gcd first nil))
         (equal (poly-add (poly-mul (mv-nth 1 result) first)
                          (poly-mul (mv-nth 2 result) nil))
                (mv-nth 0 result))))
  :hints (("Goal" :use ((:instance
                          poly-monic-extended-euclidean-gcd-bezout)))))
