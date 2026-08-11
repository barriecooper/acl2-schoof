(in-package "GPOLY")

(include-book "quotient-coordinate")
(include-book "../polynomial/generic/power")
(include-book "kestrel/arithmetic-light/expt" :dir :system)

; Transparent repeated multiplication in the quotient-coordinate commutative
; ring.  The public operation totalizes both arguments: N is read through
; NFIX and the base is fixed before the logical recursion starts.
(defun quotient-coordinate-pow-spec (base n a b modulus)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (quotient-coordinate-one modulus)
    (quotient-coordinate-mul
     base
     (quotient-coordinate-pow-spec base (1- n) a b modulus)
     a b modulus)))

(defun quotient-coordinate-pow (base n a b modulus)
  (quotient-coordinate-pow-spec
   (quotient-coordinate-fix base modulus) (nfix n) a b modulus))

(defthm quotient-coordinate-p-of-pow-spec
  (quotient-coordinate-p
   (quotient-coordinate-pow-spec base n a b modulus) modulus)
  :hints (("Goal" :induct (quotient-coordinate-pow-spec base n a b modulus)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(quotient-coordinate-pow-spec
                         quotient-coordinate-operations-closed)))))

(defthm quotient-coordinate-p-of-pow
  (quotient-coordinate-p
   (quotient-coordinate-pow base n a b modulus) modulus)
  :hints (("Goal" :in-theory (enable quotient-coordinate-pow))))

(defthm quotient-coordinate-pow-of-fix
  (equal (quotient-coordinate-pow
          (quotient-coordinate-fix base modulus) n a b modulus)
         (quotient-coordinate-pow base n a b modulus))
  :hints (("Goal" :use ((:instance quotient-coordinate-fix-idempotent
                          (coordinate base)))
           :in-theory (e/d (quotient-coordinate-pow)
                           (quotient-coordinate-fix)))))

(defthm quotient-coordinate-pow-of-nfix
  (equal (quotient-coordinate-pow base (nfix n) a b modulus)
         (quotient-coordinate-pow base n a b modulus))
  :hints (("Goal" :in-theory (enable quotient-coordinate-pow))))

(defthm quotient-coordinate-pow-zero
  (equal (quotient-coordinate-pow base 0 a b modulus)
         (quotient-coordinate-one modulus))
  :hints (("Goal" :in-theory
           (enable quotient-coordinate-pow quotient-coordinate-pow-spec))))

(local
 (defthm quotient-coordinate-mul-left-fix-for-power
   (equal (quotient-coordinate-mul
           (quotient-coordinate-fix left modulus) right a b modulus)
          (quotient-coordinate-mul left right a b modulus))
   :hints (("Goal" :use ((:instance quotient-coordinate-fix-idempotent
                           (coordinate left)))
            :in-theory (e/d (quotient-coordinate-mul)
                            (quotient-coordinate-fix))))))

(defthm quotient-coordinate-pow-spec-successor
  (equal (quotient-coordinate-pow-spec base (+ 1 (nfix n)) a b modulus)
         (quotient-coordinate-mul
          base (quotient-coordinate-pow-spec base (nfix n) a b modulus)
          a b modulus))
  :hints (("Goal"
           :expand ((quotient-coordinate-pow-spec
                     base (+ 1 (nfix n)) a b modulus))
           :in-theory (e/d (nfix zp)
                           (quotient-coordinate-mul
                            quotient-coordinate-fix)))))

(defthm quotient-coordinate-pow-successor
  (equal (quotient-coordinate-pow base (+ 1 (nfix n)) a b modulus)
         (quotient-coordinate-mul
          base (quotient-coordinate-pow base n a b modulus) a b modulus))
  :hints (("Goal" :use ((:instance quotient-coordinate-pow-spec-successor
                          (base (quotient-coordinate-fix base modulus))))
           :in-theory (e/d (quotient-coordinate-pow
                            quotient-coordinate-mul-left-fix-for-power)
                           (quotient-coordinate-mul quotient-coordinate-fix
                            quotient-coordinate-pow-spec))
           :do-not-induct t)))

(defthm quotient-coordinate-pow-one
  (equal (quotient-coordinate-pow base 1 a b modulus)
         (quotient-coordinate-fix base modulus))
  :hints (("Goal" :use ((:instance quotient-coordinate-pow-successor (n 0))))))

; Proof-only commutative-monoid normal forms.  Keeping multiplication disabled
; prevents the rank-two implementation from obscuring these small inductions.
(local
 (defthm quotient-coordinate-mul-move-left-for-power
   (equal (quotient-coordinate-mul
           x (quotient-coordinate-mul a c curve-a curve-b modulus)
           curve-a curve-b modulus)
          (quotient-coordinate-mul
           a (quotient-coordinate-mul x c curve-a curve-b modulus)
           curve-a curve-b modulus))
   :hints (("Goal"
            :use ((:instance quotient-coordinate-mul-associative
                             (x x) (z a) (w c) (a curve-a) (b curve-b))
                  (:instance quotient-coordinate-mul-associative
                             (x a) (z x) (w c) (a curve-a) (b curve-b))
                  (:instance quotient-coordinate-mul-commutative
                             (x x) (z a) (a curve-a) (b curve-b)))
            :in-theory (disable quotient-coordinate-mul
                                quotient-coordinate-mul-associative
                                quotient-coordinate-mul-commutative)))))

(local
 (defthm quotient-coordinate-mul-power-interchange
   (equal
    (quotient-coordinate-mul
     x (quotient-coordinate-mul
        a (quotient-coordinate-mul x c curve-a curve-b modulus)
        curve-a curve-b modulus)
     curve-a curve-b modulus)
    (quotient-coordinate-mul
     x (quotient-coordinate-mul
        x (quotient-coordinate-mul a c curve-a curve-b modulus)
        curve-a curve-b modulus)
     curve-a curve-b modulus))
   :hints (("Goal"
            :use ((:instance quotient-coordinate-mul-move-left-for-power)
                  (:instance quotient-coordinate-mul-associative
                             (x x) (z a)
                             (w (quotient-coordinate-mul
                                 x c curve-a curve-b modulus))
                             (a curve-a) (b curve-b))
                  (:instance quotient-coordinate-mul-associative
                             (x x) (z x)
                             (w (quotient-coordinate-mul
                                 a c curve-a curve-b modulus))
                             (a curve-a) (b curve-b)))
            :in-theory (disable quotient-coordinate-mul
                                quotient-coordinate-mul-associative
                                quotient-coordinate-mul-commutative)))))

(defthm quotient-coordinate-pow-add-reversed
  (equal (quotient-coordinate-pow
          z (+ (nfix m) (nfix n)) a b modulus)
         (quotient-coordinate-mul
          (quotient-coordinate-pow z n a b modulus)
          (quotient-coordinate-pow z m a b modulus) a b modulus))
  :rule-classes nil
  :hints (("Goal" :induct (quotient-coordinate-pow-spec z n a b modulus)
           :in-theory
           (e/d (quotient-coordinate-pow quotient-coordinate-pow-spec
                  quotient-coordinate-mul-associative
                  quotient-coordinate-mul-move-left-for-power
                  quotient-coordinate-mul-power-interchange)
                (quotient-coordinate-mul quotient-coordinate-fix
                 quotient-coordinate-one quotient-coordinate
                 poly-remainder poly-divmod)))))

(defthm quotient-coordinate-pow-add
  (equal (quotient-coordinate-pow
          z (+ (nfix m) (nfix n)) a b modulus)
         (quotient-coordinate-mul
          (quotient-coordinate-pow z m a b modulus)
          (quotient-coordinate-pow z n a b modulus) a b modulus))
  :hints (("Goal"
           :use (quotient-coordinate-pow-add-reversed
                 (:instance quotient-coordinate-mul-commutative
                            (x (quotient-coordinate-pow z n a b modulus))
                            (z (quotient-coordinate-pow z m a b modulus))))
           :in-theory (disable quotient-coordinate-mul
                               quotient-coordinate-mul-commutative))))

(local (defun quotient-coordinate-power-induct (n)
         (if (zp n) nil
           (quotient-coordinate-power-induct (1- n)))))

(local
 (defthm quotient-coordinate-positive-exponent-products
   (implies (and (natp m) (natp n) (< 0 n))
            (and (equal n (+ 1 (nfix (1- n))))
                 (equal (* m n)
                        (+ (nfix m) (* (nfix m) (nfix (1- n)))))))
   :rule-classes nil))

(local (defthm quotient-coordinate-times-zero
         (equal (* m 0) 0)))

(local
 (defthm quotient-coordinate-pow-of-pow-when-natp
   (implies (and (natp m) (natp n))
            (equal
             (quotient-coordinate-pow
              (quotient-coordinate-pow z m a b modulus) n a b modulus)
             (quotient-coordinate-pow z (* m n) a b modulus)))
   :hints (("Goal" :induct (quotient-coordinate-power-induct n)
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(quotient-coordinate-power-induct
               quotient-coordinate-pow-successor
               quotient-coordinate-pow-zero
               quotient-coordinate-pow-add
               nfix natp zp)))
           ("Subgoal *1/2"
            :use (quotient-coordinate-positive-exponent-products
                  (:instance quotient-coordinate-pow-successor
                             (base (quotient-coordinate-pow z m a b modulus))
                             (n (1- n)))
                  (:instance quotient-coordinate-pow-add
                             (m m) (n (* m (1- n)))))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(quotient-coordinate-pow-successor
                              quotient-coordinate-pow-add nfix natp zp)))
           ("Subgoal *1/1"
            :use ((:instance quotient-coordinate-pow-zero
                             (base z)))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(quotient-coordinate-pow-zero
                              quotient-coordinate-times-zero
                              nfix natp zp))))))

(defthm quotient-coordinate-pow-of-pow
  (equal
   (quotient-coordinate-pow
    (quotient-coordinate-pow z m a b modulus) n a b modulus)
   (quotient-coordinate-pow z (* (nfix m) (nfix n)) a b modulus))
  :hints (("Goal"
           :use ((:instance quotient-coordinate-pow-of-pow-when-natp
                            (m (nfix m)) (n (nfix n)))))))

(defthm quotient-coordinate-pow-of-product
  (equal
   (quotient-coordinate-pow
    (quotient-coordinate-mul x z a b modulus) n a b modulus)
   (quotient-coordinate-mul
    (quotient-coordinate-pow x n a b modulus)
    (quotient-coordinate-pow z n a b modulus) a b modulus))
  :hints (("Goal" :induct (quotient-coordinate-pow-spec x n a b modulus)
           :in-theory
           (e/d (quotient-coordinate-pow quotient-coordinate-pow-spec
                  quotient-coordinate-mul-power-interchange)
                (quotient-coordinate-mul quotient-coordinate-fix
                 quotient-coordinate-one quotient-coordinate
                 poly-remainder poly-divmod)))))

(defthm quotient-coordinate-pow-of-one-coordinate
  (equal (quotient-coordinate-pow
          (quotient-coordinate-one modulus) n a b modulus)
         (quotient-coordinate-one modulus))
  :hints (("Goal"
           :induct (quotient-coordinate-pow-spec
                    (quotient-coordinate-one modulus) n a b modulus)
           :in-theory
           (e/d (quotient-coordinate-pow quotient-coordinate-pow-spec)
                (quotient-coordinate-mul quotient-coordinate-fix
                 quotient-coordinate-one quotient-coordinate
                 poly-remainder poly-divmod)))))

(defthm quotient-coordinate-pow-of-zero-coordinate
  (equal (quotient-coordinate-pow
          (quotient-coordinate-zero modulus) n a b modulus)
         (if (zp n)
             (quotient-coordinate-one modulus)
           (quotient-coordinate-zero modulus)))
  :hints (("Goal"
           :induct (quotient-coordinate-pow-spec
                    (quotient-coordinate-zero modulus) n a b modulus)
           :in-theory
           (e/d (quotient-coordinate-pow quotient-coordinate-pow-spec
                  quotient-coordinate-mul-zero-left)
                (quotient-coordinate-mul quotient-coordinate-fix
                 quotient-coordinate-zero quotient-coordinate-one
                 quotient-coordinate poly-remainder poly-divmod)))))

(local
 (defthm quotient-coordinate-embed-polynomial-one
   (equal (quotient-coordinate-embed (polynomial-one) modulus)
          (quotient-coordinate-one modulus))
   :hints (("Goal"
            :use ((:instance poly-remainder-idempotent
                             (dividend (polynomial-one))))
            :in-theory (e/d (quotient-coordinate-embed
                             quotient-coordinate-one
                             quotient-coordinate
                             poly-reduced-one-definition)
                            (poly-remainder poly-divmod))))))

(local
 (defthm quotient-coordinate-positive-exponent-predecessor
   (implies (and (natp n) (< 0 n))
            (and (natp (1- n))
                 (equal n (+ 1 (nfix (1- n))))))
   :rule-classes nil))

(local
 (defthm quotient-coordinate-pow-of-embed-when-natp
   (implies (natp n)
            (equal
             (quotient-coordinate-pow
              (quotient-coordinate-embed polynomial modulus) n a b modulus)
             (quotient-coordinate-embed (poly-pow polynomial n) modulus)))
   :hints (("Goal" :induct (quotient-coordinate-power-induct n)
            :in-theory (union-theories
                        (theory 'minimal-theory)
                        '(quotient-coordinate-power-induct natp zp)))
           ("Subgoal *1/2"
            :use (quotient-coordinate-positive-exponent-predecessor
                  (:instance quotient-coordinate-pow-successor
                             (base (quotient-coordinate-embed polynomial modulus))
                             (n (1- n)))
                  (:instance poly-pow-successor
                             (f polynomial) (n (1- n)))
                  (:instance quotient-coordinate-embed-mul
                             (x polynomial)
                             (z (poly-pow polynomial (1- n)))))
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(nfix natp zp)))
           ("Subgoal *1/1"
            :use ((:instance quotient-coordinate-pow-zero
                             (base (quotient-coordinate-embed polynomial modulus)))
                  (:instance poly-pow-zero (f polynomial))
                  quotient-coordinate-embed-polynomial-one)
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(nfix natp zp))))))

(defthm quotient-coordinate-pow-of-embed
  (equal
   (quotient-coordinate-pow
    (quotient-coordinate-embed polynomial modulus) n a b modulus)
   (quotient-coordinate-embed (poly-pow polynomial n) modulus))
  :hints (("Goal"
           :use ((:instance quotient-coordinate-pow-of-embed-when-natp
                            (n (nfix n))))
           :in-theory (enable quotient-coordinate-pow-of-nfix
                              poly-pow-of-nfix))))

(defthm quotient-coordinate-pow-y-two
  (equal
   (quotient-coordinate-pow (quotient-coordinate-y modulus) 2 a b modulus)
   (quotient-coordinate-embed
    (list (gfield::field-fix b) (gfield::field-fix a)
          (gfield::field-zero) (gfield::field-one)) modulus))
  :hints (("Goal"
           :use ((:instance quotient-coordinate-pow-successor
                            (base (quotient-coordinate-y modulus)) (n 1))
                 (:instance quotient-coordinate-pow-one
                            (base (quotient-coordinate-y modulus)))
                 quotient-coordinate-y-squared)
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(nfix quotient-coordinate-fix-when-p
                             quotient-coordinate-operations-closed)))))

(defthm quotient-coordinate-pow-y-even
  (equal
   (quotient-coordinate-pow
    (quotient-coordinate-y modulus) (* 2 (nfix n)) a b modulus)
   (quotient-coordinate-pow
    (quotient-coordinate-embed
     (list (gfield::field-fix b) (gfield::field-fix a)
           (gfield::field-zero) (gfield::field-one)) modulus)
    n a b modulus))
  :hints (("Goal"
           :use ((:instance quotient-coordinate-pow-of-pow
                            (z (quotient-coordinate-y modulus))
                            (m 2)))
           :in-theory (enable quotient-coordinate-pow-y-two))))

(defthm quotient-coordinate-pow-y-odd
  (equal
   (quotient-coordinate-pow
    (quotient-coordinate-y modulus) (+ 1 (* 2 (nfix n))) a b modulus)
   (quotient-coordinate-mul
    (quotient-coordinate-y modulus)
    (quotient-coordinate-pow
     (quotient-coordinate-embed
      (list (gfield::field-fix b) (gfield::field-fix a)
            (gfield::field-zero) (gfield::field-one)) modulus)
     n a b modulus)
    a b modulus))
  :hints (("Goal"
           :use ((:instance quotient-coordinate-pow-add
                            (z (quotient-coordinate-y modulus))
                            (m 1) (n (* 2 (nfix n))))
                 (:instance quotient-coordinate-pow-y-even)
                 (:instance quotient-coordinate-pow-one
                            (base (quotient-coordinate-y modulus))))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(nfix quotient-coordinate-fix-when-p
                             quotient-coordinate-operations-closed)))))

; Cardinality-indexed power.  The name records the intended Schoof action;
; homomorphism properties require characteristic/prime-power metadata and are
; deliberately not asserted by this universally quantified book.
(defun quotient-coordinate-frobenius (coordinate q a b modulus)
  (quotient-coordinate-pow coordinate q a b modulus))

(defun quotient-coordinate-frobenius-iterate (coordinate q iterations a b modulus)
  (quotient-coordinate-pow coordinate
                           (expt (nfix q) (nfix iterations)) a b modulus))

(defthm quotient-coordinate-p-of-frobenius
  (quotient-coordinate-p
   (quotient-coordinate-frobenius coordinate q a b modulus) modulus))

(defthm quotient-coordinate-frobenius-of-zero
  (equal (quotient-coordinate-frobenius
          (quotient-coordinate-zero modulus) q a b modulus)
         (if (zp q)
             (quotient-coordinate-one modulus)
           (quotient-coordinate-zero modulus)))
  :hints (("Goal" :in-theory (enable quotient-coordinate-frobenius))))

(defthm quotient-coordinate-frobenius-of-one
  (equal (quotient-coordinate-frobenius
          (quotient-coordinate-one modulus) q a b modulus)
         (quotient-coordinate-one modulus))
  :hints (("Goal" :in-theory (enable quotient-coordinate-frobenius))))

(defthm quotient-coordinate-frobenius-of-product
  (equal
   (quotient-coordinate-frobenius
    (quotient-coordinate-mul x z a b modulus) q a b modulus)
   (quotient-coordinate-mul
    (quotient-coordinate-frobenius x q a b modulus)
    (quotient-coordinate-frobenius z q a b modulus) a b modulus))
  :hints (("Goal"
           :use ((:instance quotient-coordinate-pow-of-product (n q)))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(quotient-coordinate-frobenius)))))

(defthm quotient-coordinate-frobenius-of-embed
  (equal
   (quotient-coordinate-frobenius
    (quotient-coordinate-embed polynomial modulus) q a b modulus)
   (quotient-coordinate-embed (poly-pow polynomial q) modulus))
  :hints (("Goal"
           :use ((:instance quotient-coordinate-pow-of-embed (n q)))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(quotient-coordinate-frobenius)))))

(defthm quotient-coordinate-frobenius-iterate-exponent
  (equal (quotient-coordinate-frobenius-iterate
          coordinate q iterations a b modulus)
         (quotient-coordinate-pow
          coordinate (expt (nfix q) (nfix iterations)) a b modulus))
  :hints (("Goal" :in-theory (enable quotient-coordinate-frobenius-iterate))))

(defthm quotient-coordinate-frobenius-iterate-zero
  (equal (quotient-coordinate-frobenius-iterate
          coordinate q 0 a b modulus)
         (quotient-coordinate-fix coordinate modulus))
  :hints (("Goal" :in-theory (enable quotient-coordinate-frobenius-iterate))))

(defthm quotient-coordinate-frobenius-iterate-one
  (equal (quotient-coordinate-frobenius-iterate coordinate q 1 a b modulus)
         (quotient-coordinate-frobenius coordinate q a b modulus))
  :hints (("Goal" :in-theory (enable quotient-coordinate-frobenius-iterate
                                      quotient-coordinate-frobenius))))

(defthm quotient-coordinate-frobenius-iterate-successor
  (equal
   (quotient-coordinate-frobenius-iterate
    coordinate q (+ 1 (nfix iterations)) a b modulus)
   (quotient-coordinate-frobenius
    (quotient-coordinate-frobenius-iterate
     coordinate q iterations a b modulus)
    q a b modulus))
  :hints (("Goal"
           :in-theory (enable quotient-coordinate-frobenius-iterate
                              quotient-coordinate-frobenius
                              quotient-coordinate-pow-of-pow expt))))

(defthm quotient-coordinate-frobenius-iterate-compose
  (equal
   (quotient-coordinate-frobenius-iterate
    coordinate q (+ (nfix m) (nfix n)) a b modulus)
   (quotient-coordinate-frobenius-iterate
    (quotient-coordinate-frobenius-iterate
     coordinate q m a b modulus)
    q n a b modulus))
  :hints (("Goal"
           :in-theory (enable quotient-coordinate-frobenius-iterate
                              quotient-coordinate-pow-of-pow
                              acl2::expt-of-+))))

(verify-guards quotient-coordinate-pow-spec)
(verify-guards quotient-coordinate-pow)
(verify-guards quotient-coordinate-frobenius)
(verify-guards quotient-coordinate-frobenius-iterate)

(in-theory (disable quotient-coordinate-pow-spec))
