(in-package "GPOLY")

(include-book "runtime-p-monic-divmod")
(local (include-book "arithmetic-5/top" :dir :system))

; A descriptor is deliberately plain data.  Structural validity says only that
; P is an admitted runtime modulus and that MODULUS is already normalized,
; monic, and of positive degree.  It says nothing about primality or
; irreducibility.
(defun runtime-polynomial-basis-descriptor-p (descriptor)
  (declare (xargs :guard t))
  (and (true-listp descriptor)
       (equal (len descriptor) 3)
       (eq (car descriptor) :polynomial-basis)
       (integerp (cadr descriptor))
       (<= 2 (cadr descriptor))
       (equal (caddr descriptor)
              (runtime-p-normalize (caddr descriptor) (cadr descriptor)))
       (consp (caddr descriptor))
       (< 0 (runtime-p-poly-degree (caddr descriptor) (cadr descriptor)))
       (equal (runtime-p-poly-leading-coefficient
               (caddr descriptor) (cadr descriptor))
              (runtime-p-one (cadr descriptor)))))

(defun runtime-polynomial-basis-default-descriptor ()
  (declare (xargs :guard t))
  (list :polynomial-basis 2 (list 0 1)))

(defun runtime-polynomial-basis-descriptor-fix (descriptor)
  (declare (xargs :guard t))
  (if (runtime-polynomial-basis-descriptor-p descriptor)
      descriptor
    (runtime-polynomial-basis-default-descriptor)))

(defun runtime-polynomial-basis-p (descriptor)
  (declare (xargs :guard t))
  (cadr (runtime-polynomial-basis-descriptor-fix descriptor)))

(defun runtime-polynomial-basis-modulus (descriptor)
  (declare (xargs :guard t))
  (caddr (runtime-polynomial-basis-descriptor-fix descriptor)))

(defun runtime-polynomial-basis-degree (descriptor)
  (declare (xargs :guard t))
  (runtime-p-poly-degree (runtime-polynomial-basis-modulus descriptor)
                         (runtime-polynomial-basis-p descriptor)))

(defun runtime-polynomial-basis-fix (x descriptor)
  (declare (xargs :guard t))
  (runtime-p-monic-remainder x
    (runtime-polynomial-basis-modulus descriptor)
    (runtime-polynomial-basis-p descriptor)))

(defun runtime-polynomial-basis-element-p (x descriptor)
  (declare (xargs :guard t))
  (and (runtime-p-canonical-polynomial-p
        x (runtime-polynomial-basis-p descriptor))
       (or (not (consp x))
           (< (runtime-p-poly-degree x (runtime-polynomial-basis-p descriptor))
              (runtime-polynomial-basis-degree descriptor)))))

(defun runtime-polynomial-basis-equal (x y descriptor)
  (declare (xargs :guard t))
  (equal (runtime-polynomial-basis-fix x descriptor)
         (runtime-polynomial-basis-fix y descriptor)))

(defun runtime-polynomial-basis-zero (descriptor)
  (declare (ignore descriptor) (xargs :guard t)) nil)

(defun runtime-polynomial-basis-one (descriptor)
  (declare (xargs :guard t))
  (runtime-polynomial-basis-fix
   (runtime-p-polynomial-one (runtime-polynomial-basis-p descriptor))
   descriptor))

(defun runtime-polynomial-basis-add (x y descriptor)
  (declare (xargs :guard t))
  (runtime-polynomial-basis-fix
   (runtime-p-poly-add x y (runtime-polynomial-basis-p descriptor)) descriptor))

(defun runtime-polynomial-basis-neg (x descriptor)
  (declare (xargs :guard t))
  (runtime-polynomial-basis-fix
   (runtime-p-poly-neg x (runtime-polynomial-basis-p descriptor)) descriptor))

(defun runtime-polynomial-basis-sub (x y descriptor)
  (declare (xargs :guard t))
  (runtime-polynomial-basis-add x
    (runtime-polynomial-basis-neg y descriptor) descriptor))

(defun runtime-polynomial-basis-mul (x y descriptor)
  (declare (xargs :guard t))
  (runtime-polynomial-basis-fix
   (runtime-p-poly-mul x y (runtime-polynomial-basis-p descriptor)) descriptor))

; Canonical polynomials are variable length.  Coding uses a separate exact
; width vector padded with coefficient zero.
(defun runtime-polynomial-basis-vector-aux (width polynomial p)
  (declare (xargs :guard t :measure (nfix width)))
  (if (zp (nfix width)) nil
    (cons (if (consp polynomial)
              (runtime-p-coefficient-fix (car polynomial) p)
            (runtime-p-zero p))
          (runtime-polynomial-basis-vector-aux
           (1- (nfix width))
           (if (consp polynomial) (cdr polynomial) nil) p))))

(defun runtime-polynomial-basis-vector (x descriptor)
  (declare (xargs :guard t))
  (runtime-polynomial-basis-vector-aux
   (runtime-polynomial-basis-degree descriptor)
   (runtime-polynomial-basis-fix x descriptor)
   (runtime-polynomial-basis-p descriptor)))

(defun runtime-polynomial-basis-reconstruct (vector descriptor)
  (declare (xargs :guard t))
  (runtime-p-normalize vector (runtime-polynomial-basis-p descriptor)))

(defun runtime-polynomial-basis-bound (descriptor)
  (declare (xargs :guard t))
  (runtime-p-coding-bound (runtime-polynomial-basis-degree descriptor)
                          (runtime-polynomial-basis-p descriptor)))

(defun runtime-polynomial-basis-rank (x descriptor)
  (declare (xargs :guard t))
  (runtime-p-rank (runtime-polynomial-basis-vector x descriptor)
                  (runtime-polynomial-basis-p descriptor)))

(defun runtime-polynomial-basis-unrank (k descriptor)
  (declare (xargs :guard t))
  (runtime-polynomial-basis-reconstruct
   (runtime-p-unrank (runtime-polynomial-basis-degree descriptor) k
                     (runtime-polynomial-basis-p descriptor))
   descriptor))

(verify-guards runtime-polynomial-basis-descriptor-p)
(verify-guards runtime-polynomial-basis-descriptor-fix)
(verify-guards runtime-polynomial-basis-fix)
(verify-guards runtime-polynomial-basis-element-p)
(verify-guards runtime-polynomial-basis-add)
(verify-guards runtime-polynomial-basis-neg)
(verify-guards runtime-polynomial-basis-sub)
(verify-guards runtime-polynomial-basis-mul)
(verify-guards runtime-polynomial-basis-rank)
(verify-guards runtime-polynomial-basis-unrank)

(defthm runtime-polynomial-basis-descriptor-p-of-default
  (runtime-polynomial-basis-descriptor-p
   (runtime-polynomial-basis-default-descriptor))
  :hints (("Goal" :in-theory (enable runtime-polynomial-basis-descriptor-p
                                      runtime-polynomial-basis-default-descriptor
                                      runtime-p-poly-degree
                                      runtime-p-poly-leading-coefficient))))

(defthm runtime-polynomial-basis-descriptor-p-of-fix
  (runtime-polynomial-basis-descriptor-p
   (runtime-polynomial-basis-descriptor-fix descriptor)))

(defthm runtime-polynomial-basis-descriptor-fix-when-valid
  (implies (runtime-polynomial-basis-descriptor-p descriptor)
           (equal (runtime-polynomial-basis-descriptor-fix descriptor)
                  descriptor)))

(defthm runtime-polynomial-basis-descriptor-fix-idempotent
  (equal (runtime-polynomial-basis-descriptor-fix
          (runtime-polynomial-basis-descriptor-fix descriptor))
         (runtime-polynomial-basis-descriptor-fix descriptor)))

(defthm runtime-polynomial-basis-p-lower-bound
  (<= 2 (runtime-polynomial-basis-p descriptor))
  :rule-classes :linear)

(defthm runtime-polynomial-basis-degree-positive
  (< 0 (runtime-polynomial-basis-degree descriptor))
  :rule-classes :linear)

(defthm natp-of-runtime-polynomial-basis-degree
  (natp (runtime-polynomial-basis-degree descriptor))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal"
           :use ((:instance integerp-of-runtime-p-poly-degree
                            (poly (runtime-polynomial-basis-modulus descriptor))
                            (p (runtime-polynomial-basis-p descriptor)))
                 (:instance runtime-polynomial-basis-degree-positive))
           :in-theory (enable runtime-polynomial-basis-degree))))

(defthm runtime-polynomial-basis-modulus-monic
  (equal (runtime-p-poly-leading-coefficient
          (runtime-polynomial-basis-modulus descriptor)
          (runtime-polynomial-basis-p descriptor))
         (runtime-p-one (runtime-polynomial-basis-p descriptor))))

(defthm runtime-p-canonical-polynomial-p-of-runtime-polynomial-basis-fix
  (runtime-p-canonical-polynomial-p
   (runtime-polynomial-basis-fix x descriptor)
   (runtime-polynomial-basis-p descriptor))
  :hints (("Goal"
           :use ((:instance runtime-p-canonical-polynomial-p-of-monic-remainder
                            (f x)
                            (g (runtime-polynomial-basis-modulus descriptor))
                            (p (runtime-polynomial-basis-p descriptor))))
           :in-theory (e/d (runtime-polynomial-basis-fix)
                           (runtime-p-monic-remainder
                            runtime-p-canonical-polynomial-p)))))

(defthm runtime-polynomial-basis-fix-degree-bound
  (or (not (consp (runtime-polynomial-basis-fix x descriptor)))
      (< (runtime-p-poly-degree
          (runtime-polynomial-basis-fix x descriptor)
          (runtime-polynomial-basis-p descriptor))
         (runtime-polynomial-basis-degree descriptor)))
  :hints (("Goal"
           :use ((:instance runtime-p-monic-remainder-bound
                            (f x)
                            (g (runtime-polynomial-basis-modulus descriptor))
                            (p (runtime-polynomial-basis-p descriptor))))
           :in-theory (e/d (runtime-polynomial-basis-fix
                            runtime-polynomial-basis-degree)
                           (runtime-p-monic-remainder
                            runtime-p-poly-degree)))))

(defthm runtime-polynomial-basis-element-p-of-fix
  (runtime-polynomial-basis-element-p
   (runtime-polynomial-basis-fix x descriptor) descriptor)
  :hints (("Goal" :use
           (runtime-p-canonical-polynomial-p-of-runtime-polynomial-basis-fix
            runtime-polynomial-basis-fix-degree-bound)
           :in-theory (union-theories
                       '(runtime-polynomial-basis-element-p)
                       (theory 'minimal-theory)))))

(defthm runtime-polynomial-basis-fix-when-element-p
  (implies (runtime-polynomial-basis-element-p x descriptor)
           (equal (runtime-polynomial-basis-fix x descriptor) x))
  :hints (("Goal"
           :use ((:instance runtime-p-monic-divmod-inactive
                            (f x)
                            (g (runtime-polynomial-basis-modulus descriptor))
                            (p (runtime-polynomial-basis-p descriptor))))
           :in-theory (enable runtime-polynomial-basis-element-p
                              runtime-polynomial-basis-fix
                              runtime-polynomial-basis-degree))))

(defthm runtime-polynomial-basis-fix-idempotent
  (equal (runtime-polynomial-basis-fix
          (runtime-polynomial-basis-fix x descriptor) descriptor)
         (runtime-polynomial-basis-fix x descriptor))
  :hints (("Goal"
           :use ((:instance runtime-polynomial-basis-fix-when-element-p
                            (x (runtime-polynomial-basis-fix x descriptor)))
                 (:instance runtime-polynomial-basis-element-p-of-fix))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-polynomial-basis-element-p-of-zero
  (runtime-polynomial-basis-element-p
   (runtime-polynomial-basis-zero descriptor) descriptor)
  :hints (("Goal" :in-theory (enable runtime-polynomial-basis-element-p
                                      runtime-polynomial-basis-zero
                                      runtime-p-canonical-polynomial-p
                                      runtime-p-coefficient-list-p))))

(defthm runtime-polynomial-basis-element-p-of-add
  (runtime-polynomial-basis-element-p
   (runtime-polynomial-basis-add x y descriptor) descriptor)
  :hints (("Goal" :use
           ((:instance runtime-polynomial-basis-element-p-of-fix
                       (x (runtime-p-poly-add
                           x y (runtime-polynomial-basis-p descriptor)))))
           :in-theory (union-theories '(runtime-polynomial-basis-add)
                                      (theory 'minimal-theory)))))
(defthm runtime-polynomial-basis-element-p-of-neg
  (runtime-polynomial-basis-element-p
   (runtime-polynomial-basis-neg x descriptor) descriptor)
  :hints (("Goal" :use
           ((:instance runtime-polynomial-basis-element-p-of-fix
                       (x (runtime-p-poly-neg
                           x (runtime-polynomial-basis-p descriptor)))))
           :in-theory (union-theories '(runtime-polynomial-basis-neg)
                                      (theory 'minimal-theory)))))
(defthm runtime-polynomial-basis-element-p-of-sub
  (runtime-polynomial-basis-element-p
   (runtime-polynomial-basis-sub x y descriptor) descriptor)
  :hints (("Goal" :use
           ((:instance runtime-polynomial-basis-element-p-of-add
                       (x x)
                       (y (runtime-polynomial-basis-neg y descriptor))))
           :in-theory (union-theories '(runtime-polynomial-basis-sub)
                                      (theory 'minimal-theory)))))
(defthm runtime-polynomial-basis-element-p-of-mul
  (runtime-polynomial-basis-element-p
   (runtime-polynomial-basis-mul x y descriptor) descriptor)
  :hints (("Goal" :use
           ((:instance runtime-polynomial-basis-element-p-of-fix
                       (x (runtime-p-poly-mul
                           x y (runtime-polynomial-basis-p descriptor)))))
           :in-theory (union-theories '(runtime-polynomial-basis-mul)
                                      (theory 'minimal-theory)))))

(defthm len-of-runtime-polynomial-basis-vector-aux
  (equal (len (runtime-polynomial-basis-vector-aux width polynomial p))
         (nfix width)))

(defthm runtime-p-coefficient-list-p-of-runtime-polynomial-basis-vector-aux
  (runtime-p-coefficient-list-p
   (runtime-polynomial-basis-vector-aux width polynomial p) p)
  :hints (("Goal" :induct
           (runtime-polynomial-basis-vector-aux width polynomial p)
           :in-theory (enable runtime-polynomial-basis-vector-aux
                              runtime-p-coefficient-list-p))))

(defthm runtime-p-vector-p-of-runtime-polynomial-basis-vector
  (runtime-p-vector-p
   (runtime-polynomial-basis-vector x descriptor)
   (runtime-polynomial-basis-degree descriptor)
   (runtime-polynomial-basis-p descriptor))
  :hints (("Goal" :in-theory (enable runtime-polynomial-basis-vector
                                      runtime-p-vector-p))))

(defthm runtime-polynomial-basis-rank-bound
  (< (runtime-polynomial-basis-rank x descriptor)
     (runtime-polynomial-basis-bound descriptor))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use
           ((:instance runtime-p-rank-upper-bound
                       (coefficients (runtime-polynomial-basis-vector x descriptor))
                       (width (runtime-polynomial-basis-degree descriptor))
                       (p (runtime-polynomial-basis-p descriptor))))
           :in-theory (enable runtime-polynomial-basis-rank
                              runtime-polynomial-basis-bound))))

(defthm runtime-polynomial-basis-bound-is-p-to-the-m
  (equal (runtime-polynomial-basis-bound descriptor)
         (expt (runtime-polynomial-basis-p descriptor)
               (runtime-polynomial-basis-degree descriptor)))
  :hints (("Goal" :in-theory (enable runtime-polynomial-basis-bound
                                      runtime-p-coding-bound
                                      runtime-polynomial-basis-p))))

(defthm posp-of-runtime-polynomial-basis-bound
  (posp (runtime-polynomial-basis-bound descriptor))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal"
           :use ((:instance runtime-polynomial-basis-p-lower-bound)
                 (:instance natp-of-runtime-polynomial-basis-degree))
           :in-theory (enable runtime-polynomial-basis-bound
                              runtime-p-coding-bound))))

; The coding proof is representation-only.  In particular, none of the
; following lemmas mentions polynomial addition, negation, or multiplication.
(local
 (defthm runtime-polynomial-basis-vector-aux-of-normalize-when-exact
   (implies (and (runtime-p-coefficient-list-p coefficients p)
                 (equal (len coefficients) (nfix width)))
            (equal (runtime-polynomial-basis-vector-aux
                    width (runtime-p-normalize coefficients p) p)
                   coefficients))
   :hints (("Goal"
            :induct (runtime-polynomial-basis-vector-aux
                     width coefficients p)
            :in-theory (enable runtime-polynomial-basis-vector-aux
                               runtime-p-normalize
                               runtime-p-fix-coefficients
                               runtime-p-trim-trailing-zeros
                               runtime-p-coefficient-list-p)))))

(local
 (defthm runtime-p-normalize-of-runtime-polynomial-basis-vector-aux
   (implies (and (runtime-p-canonical-polynomial-p polynomial p)
                 (<= (len polynomial) (nfix width)))
            (equal (runtime-p-normalize
                    (runtime-polynomial-basis-vector-aux width polynomial p) p)
                   polynomial))
   :hints (("Goal"
            :induct (runtime-polynomial-basis-vector-aux width polynomial p)
            :in-theory (enable runtime-polynomial-basis-vector-aux
                               runtime-p-normalize
                               runtime-p-fix-coefficients
                               runtime-p-trim-trailing-zeros
                               runtime-p-canonical-polynomial-p
                               runtime-p-coefficient-list-p)))))

(local
 (defthm len-of-runtime-polynomial-basis-fix-at-most-degree
   (<= (len (runtime-polynomial-basis-fix x descriptor))
       (runtime-polynomial-basis-degree descriptor))
   :rule-classes :linear
   :hints (("Goal"
            :cases ((consp (runtime-polynomial-basis-fix x descriptor)))
            :nonlinearp t
            :use ((:instance
                   runtime-p-poly-degree-when-canonical-nonzero
                   (poly (runtime-polynomial-basis-fix x descriptor))
                   (p (runtime-polynomial-basis-p descriptor)))
                  (:instance runtime-polynomial-basis-fix-degree-bound)
                  (:instance
                   runtime-p-canonical-polynomial-p-of-runtime-polynomial-basis-fix)
                  (:instance integerp-of-runtime-p-poly-degree
                             (poly (runtime-polynomial-basis-fix x descriptor))
                             (p (runtime-polynomial-basis-p descriptor)))
                  (:instance integerp-of-runtime-p-poly-degree
                             (poly (runtime-polynomial-basis-modulus descriptor))
                             (p (runtime-polynomial-basis-p descriptor)))
                  (:instance runtime-polynomial-basis-degree-positive))
            :in-theory (union-theories
                        '(len runtime-polynomial-basis-degree)
                        (theory 'minimal-theory))))))

(defthm runtime-polynomial-basis-reconstruct-of-vector
  (equal (runtime-polynomial-basis-reconstruct
          (runtime-polynomial-basis-vector x descriptor) descriptor)
         (runtime-polynomial-basis-fix x descriptor))
  :hints (("Goal"
           :use ((:instance
                  runtime-p-normalize-of-runtime-polynomial-basis-vector-aux
                  (width (runtime-polynomial-basis-degree descriptor))
                  (polynomial (runtime-polynomial-basis-fix x descriptor))
                 (p (runtime-polynomial-basis-p descriptor)))
                 (:instance len-of-runtime-polynomial-basis-fix-at-most-degree)
                 (:instance
                  runtime-p-canonical-polynomial-p-of-runtime-polynomial-basis-fix)
                 (:instance natp-of-runtime-polynomial-basis-degree))
           :in-theory
           (union-theories
            '(runtime-polynomial-basis-reconstruct
              runtime-polynomial-basis-vector nfix natp)
            (theory 'minimal-theory)))))

(local
 (defthm len-of-runtime-p-fix-coefficients
   (equal (len (runtime-p-fix-coefficients xs p))
          (len xs))
   :hints (("Goal" :induct (runtime-p-fix-coefficients xs p)
            :in-theory (enable runtime-p-fix-coefficients)))))

(local
 (defthm len-of-runtime-p-trim-trailing-zeros-upper-bound
   (<= (len (runtime-p-trim-trailing-zeros xs p)) (len xs))
   :rule-classes :linear
   :hints (("Goal" :induct (runtime-p-trim-trailing-zeros xs p)
            :in-theory (enable runtime-p-trim-trailing-zeros)))))

(local
 (defthm len-of-runtime-p-normalize-upper-bound
   (<= (len (runtime-p-normalize xs p)) (len xs))
   :rule-classes :linear
   :hints (("Goal"
            :use ((:instance len-of-runtime-p-trim-trailing-zeros-upper-bound
                             (xs (runtime-p-fix-coefficients xs p))))
            :in-theory (enable runtime-p-normalize)))))

(defthm runtime-polynomial-basis-element-p-of-reconstruct-when-vector-p
  (implies
   (runtime-p-vector-p vector (runtime-polynomial-basis-degree descriptor)
                       (runtime-polynomial-basis-p descriptor))
   (runtime-polynomial-basis-element-p
    (runtime-polynomial-basis-reconstruct vector descriptor) descriptor))
  :hints
  (("Goal"
    :cases ((consp (runtime-p-normalize
                    vector (runtime-polynomial-basis-p descriptor))))
    :use ((:instance runtime-p-canonical-polynomial-p-of-normalize
                     (xs vector) (p (runtime-polynomial-basis-p descriptor)))
          (:instance runtime-p-poly-degree-when-canonical-nonzero
                     (poly (runtime-p-normalize
                            vector (runtime-polynomial-basis-p descriptor)))
                     (p (runtime-polynomial-basis-p descriptor)))
          (:instance len-of-runtime-p-normalize-upper-bound
                     (xs vector) (p (runtime-polynomial-basis-p descriptor)))
          (:instance runtime-polynomial-basis-degree-positive))
    :in-theory (enable runtime-polynomial-basis-element-p
                       runtime-polynomial-basis-reconstruct
                       runtime-p-vector-p))))

(defthm runtime-polynomial-basis-vector-of-reconstruct
  (implies
   (runtime-p-vector-p vector (runtime-polynomial-basis-degree descriptor)
                       (runtime-polynomial-basis-p descriptor))
   (equal (runtime-polynomial-basis-vector
           (runtime-polynomial-basis-reconstruct vector descriptor) descriptor)
          vector))
  :hints (("Goal"
           :use ((:instance
                  runtime-polynomial-basis-vector-aux-of-normalize-when-exact
                  (coefficients vector)
                  (width (runtime-polynomial-basis-degree descriptor))
                  (p (runtime-polynomial-basis-p descriptor)))
                 (:instance runtime-polynomial-basis-fix-when-element-p
                            (x (runtime-polynomial-basis-reconstruct
                                vector descriptor)))
                 (:instance
                  runtime-polynomial-basis-element-p-of-reconstruct-when-vector-p))
           :in-theory
           (union-theories
            '(runtime-polynomial-basis-vector
              runtime-polynomial-basis-reconstruct runtime-p-vector-p)
            (theory 'minimal-theory)))))

(defthm runtime-polynomial-basis-element-p-of-unrank
  (runtime-polynomial-basis-element-p
   (runtime-polynomial-basis-unrank k descriptor) descriptor)
  :hints (("Goal"
           :use ((:instance
                  runtime-polynomial-basis-element-p-of-reconstruct-when-vector-p
                  (vector
                   (runtime-p-unrank
                    (runtime-polynomial-basis-degree descriptor) k
                    (runtime-polynomial-basis-p descriptor))))
                 (:instance runtime-p-vector-p-of-unrank
                            (width (runtime-polynomial-basis-degree descriptor))
                            (p (runtime-polynomial-basis-p descriptor))))
           :in-theory
           (union-theories '(runtime-polynomial-basis-unrank)
                           (theory 'minimal-theory)))))

(defthm runtime-polynomial-basis-fix-of-unrank
  (equal (runtime-polynomial-basis-fix
          (runtime-polynomial-basis-unrank k descriptor) descriptor)
         (runtime-polynomial-basis-unrank k descriptor))
  :hints (("Goal" :use
           ((:instance runtime-polynomial-basis-fix-when-element-p
                       (x (runtime-polynomial-basis-unrank k descriptor)))
            (:instance runtime-polynomial-basis-element-p-of-unrank))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-polynomial-basis-vector-of-unrank
  (equal (runtime-polynomial-basis-vector
          (runtime-polynomial-basis-unrank k descriptor) descriptor)
         (runtime-p-unrank (runtime-polynomial-basis-degree descriptor) k
                           (runtime-polynomial-basis-p descriptor)))
  :hints (("Goal"
           :use ((:instance runtime-polynomial-basis-vector-of-reconstruct
                            (vector
                             (runtime-p-unrank
                              (runtime-polynomial-basis-degree descriptor) k
                              (runtime-polynomial-basis-p descriptor))))
                 (:instance runtime-p-vector-p-of-unrank
                            (width (runtime-polynomial-basis-degree descriptor))
                            (p (runtime-polynomial-basis-p descriptor))))
           :in-theory
           (union-theories '(runtime-polynomial-basis-unrank)
                           (theory 'minimal-theory)))))

(defthm runtime-polynomial-basis-unrank-of-rank
  (equal (runtime-polynomial-basis-unrank
          (runtime-polynomial-basis-rank x descriptor) descriptor)
         (runtime-polynomial-basis-fix x descriptor))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-unrank-of-rank
                            (coefficients
                             (runtime-polynomial-basis-vector x descriptor))
                            (width (runtime-polynomial-basis-degree descriptor))
                            (p (runtime-polynomial-basis-p descriptor)))
                 (:instance runtime-polynomial-basis-reconstruct-of-vector)
                 (:instance
                  runtime-p-vector-p-of-runtime-polynomial-basis-vector))
           :in-theory
           (union-theories
            '(runtime-polynomial-basis-unrank runtime-polynomial-basis-rank)
            (theory 'minimal-theory)))))

(defthm runtime-polynomial-basis-rank-of-unrank-when-bounded
  (implies (and (natp k)
                (< k (runtime-polynomial-basis-bound descriptor)))
           (equal (runtime-polynomial-basis-rank
                   (runtime-polynomial-basis-unrank k descriptor) descriptor)
                  k))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-rank-of-unrank
                            (width (runtime-polynomial-basis-degree descriptor))
                            (p (runtime-polynomial-basis-p descriptor))))
           :in-theory
           (union-theories
            '(runtime-polynomial-basis-rank runtime-polynomial-basis-bound
              runtime-polynomial-basis-vector-of-unrank)
            (theory 'minimal-theory)))))

(defthm runtime-polynomial-basis-rank-of-fix
  (equal (runtime-polynomial-basis-rank
          (runtime-polynomial-basis-fix x descriptor) descriptor)
         (runtime-polynomial-basis-rank x descriptor))
  :hints (("Goal"
           :use ((:instance runtime-polynomial-basis-fix-idempotent))
           :in-theory
           (union-theories
            '(runtime-polynomial-basis-rank runtime-polynomial-basis-vector)
            (theory 'minimal-theory)))))
