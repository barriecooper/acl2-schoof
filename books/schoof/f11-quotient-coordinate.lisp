(in-package "GPOLY")

(include-book "quotient-coordinate-trace-predicate")
(include-book "../polynomial/generic/f11-production-reduced-ring")

; Concrete specialization of the transparent production representation.  A
; coordinate is still the pair (u . v), denoting u+y*v; only polynomial
; reduction and coefficient arithmetic have been specialized to F11.
(defun f11-quotient-coordinate (u v modulus)
  (cons (f11-poly-remainder u modulus)
        (f11-poly-remainder v modulus)))

(defun f11-quotient-coordinate-u (coordinate)
  (if (consp coordinate) (car coordinate) nil))
(defun f11-quotient-coordinate-v (coordinate)
  (if (consp coordinate) (cdr coordinate) nil))

(defun f11-quotient-coordinate-fix (coordinate modulus)
  (f11-quotient-coordinate (f11-quotient-coordinate-u coordinate)
                           (f11-quotient-coordinate-v coordinate) modulus))
(defun f11-quotient-coordinate-zero (modulus)
  (f11-quotient-coordinate nil nil modulus))
(defun f11-quotient-coordinate-one (modulus)
  (f11-quotient-coordinate (f11-poly-reduced-one modulus) nil modulus))
(defun f11-quotient-coordinate-x (modulus)
  (f11-quotient-coordinate '(0 1) nil modulus))
(defun f11-quotient-coordinate-y (modulus)
  (f11-quotient-coordinate nil (f11-poly-reduced-one modulus) modulus))

; Embed an arbitrary ascending F11 polynomial with zero y-component.
(defun f11-quotient-coordinate-embed (polynomial modulus)
  (f11-quotient-coordinate polynomial nil modulus))

(defun f11-quotient-coordinate-add (left right modulus)
  (let ((left (f11-quotient-coordinate-fix left modulus))
        (right (f11-quotient-coordinate-fix right modulus)))
    (f11-quotient-coordinate
     (f11-poly-reduced-add (f11-quotient-coordinate-u left)
                           (f11-quotient-coordinate-u right) modulus)
     (f11-poly-reduced-add (f11-quotient-coordinate-v left)
                           (f11-quotient-coordinate-v right) modulus)
     modulus)))
(defun f11-quotient-coordinate-neg (coordinate modulus)
  (let ((coordinate (f11-quotient-coordinate-fix coordinate modulus)))
    (f11-quotient-coordinate
     (f11-poly-reduced-neg (f11-quotient-coordinate-u coordinate) modulus)
     (f11-poly-reduced-neg (f11-quotient-coordinate-v coordinate) modulus)
     modulus)))
(defun f11-quotient-coordinate-sub (left right modulus)
  (f11-quotient-coordinate-add
   left (f11-quotient-coordinate-neg right modulus) modulus))
(defun f11-quotient-coordinate-curve-cubic (a b modulus)
  (f11-poly-remainder
   (list (gfield::f11-fix b) (gfield::f11-fix a) 0 1) modulus))
(defun f11-quotient-coordinate-mul (left right a b modulus)
  (let* ((left (f11-quotient-coordinate-fix left modulus))
         (right (f11-quotient-coordinate-fix right modulus))
         (u1 (f11-quotient-coordinate-u left))
         (v1 (f11-quotient-coordinate-v left))
         (u2 (f11-quotient-coordinate-u right))
         (v2 (f11-quotient-coordinate-v right))
         (cubic (f11-quotient-coordinate-curve-cubic a b modulus)))
    (f11-quotient-coordinate
     (f11-poly-reduced-add
      (f11-poly-reduced-mul u1 u2 modulus)
      (f11-poly-reduced-mul
       cubic (f11-poly-reduced-mul v1 v2 modulus) modulus)
      modulus)
     (f11-poly-reduced-add (f11-poly-reduced-mul u1 v2 modulus)
                           (f11-poly-reduced-mul v1 u2 modulus) modulus)
     modulus)))

; Transparent constant-first Horner evaluation in the quotient-coordinate
; algebra.  Atomic polynomial tails are the zero polynomial, coefficients are
; fixed by the embedding, and every arithmetic step uses the fixed public
; quotient-coordinate operations.
(defun f11-quotient-coordinate-eval (polynomial coordinate a b modulus)
  (if (atom polynomial)
      (f11-quotient-coordinate-zero modulus)
    (f11-quotient-coordinate-add
     (f11-quotient-coordinate-embed (list (gfield::f11-fix (car polynomial)))
                                    modulus)
     (f11-quotient-coordinate-mul
      coordinate
      (f11-quotient-coordinate-eval (cdr polynomial) coordinate a b modulus)
      a b modulus)
     modulus)))


(verify-guards f11-quotient-coordinate)
(verify-guards f11-quotient-coordinate-u)
(verify-guards f11-quotient-coordinate-v)
(verify-guards f11-quotient-coordinate-fix)
(verify-guards f11-quotient-coordinate-zero)
(verify-guards f11-quotient-coordinate-one)
(verify-guards f11-quotient-coordinate-x)
(verify-guards f11-quotient-coordinate-y)
(verify-guards f11-quotient-coordinate-embed)
(verify-guards f11-quotient-coordinate-add)
(verify-guards f11-quotient-coordinate-neg)
(verify-guards f11-quotient-coordinate-sub)
(verify-guards f11-quotient-coordinate-curve-cubic)
(verify-guards f11-quotient-coordinate-mul)
(verify-guards f11-quotient-coordinate-eval)


(defthm f11-quotient-coordinate-embed-exact
  (equal (f11-quotient-coordinate-embed polynomial modulus)
         (cons (f11-poly-remainder polynomial modulus) nil)))

(defthm f11-quotient-coordinate-embed-zero
  (equal (f11-quotient-coordinate-embed nil modulus)
         (f11-quotient-coordinate-zero modulus)))

(defthm f11-quotient-coordinate-embed-add
  (equal (f11-quotient-coordinate-add
          (f11-quotient-coordinate-embed left modulus)
          (f11-quotient-coordinate-embed right modulus) modulus)
         (f11-quotient-coordinate-embed (f11-poly-add left right) modulus))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance f11-poly-remainder-of-poly-add-remainders)
                 (:instance f11-poly-remainder-idempotent (dividend left))
                 (:instance f11-poly-remainder-idempotent (dividend right))
                 (:instance f11-poly-remainder-idempotent
                            (dividend (f11-poly-add left right)))
                 (:instance f11-poly-remainder-zero-dividend))
           :in-theory (e/d (f11-quotient-coordinate-add
                              f11-quotient-coordinate-embed
                              f11-quotient-coordinate-fix
                              f11-quotient-coordinate-u
                              f11-quotient-coordinate-v
                              f11-quotient-coordinate
                              f11-poly-reduced-add)
                             (f11-poly-remainder f11-poly-divmod
                              f11-poly-add f11-poly-raw-add)))))

(local
 (defthm f11-poly-zero-operation-forms-for-coordinate
   (and (equal (f11-poly-add nil nil) nil)
        (equal (f11-poly-add polynomial nil) (f11-normalize polynomial))
        (equal (f11-poly-mul nil polynomial) nil)
        (equal (f11-poly-mul polynomial nil) nil))
   :hints (("Goal" :in-theory
            (enable f11-poly-add f11-poly-raw-add
                    f11-poly-mul f11-poly-raw-mul
                    f11-poly-scale f11-poly-raw-scale
                    f11-normalize f11-fix-coefficients
                    f11-trim-trailing-zeros)))))

(defthm f11-quotient-coordinate-embed-mul
  (equal (f11-quotient-coordinate-mul
          (f11-quotient-coordinate-embed left modulus)
          (f11-quotient-coordinate-embed right modulus) a b modulus)
         (f11-quotient-coordinate-embed (f11-poly-mul left right) modulus))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance f11-poly-remainder-of-poly-mul-remainders)
                 (:instance f11-poly-remainder-idempotent (dividend left))
                 (:instance f11-poly-remainder-idempotent (dividend right))
                 (:instance f11-poly-remainder-idempotent
                            (dividend (f11-poly-mul left right)))
                 (:instance f11-poly-remainder-idempotent
                            (dividend (f11-poly-remainder
                                       (f11-poly-mul left right) modulus)))
                 (:instance f11-poly-remainder-of-normalize-dividend
                            (dividend (f11-poly-remainder
                                       (f11-poly-mul left right) modulus)))
                 (:instance f11-poly-remainder-zero-dividend))
           :in-theory (e/d (f11-quotient-coordinate-mul
                              f11-quotient-coordinate-embed
                              f11-quotient-coordinate-fix
                              f11-quotient-coordinate-u
                              f11-quotient-coordinate-v
                              f11-quotient-coordinate
                              f11-poly-reduced-add
                              f11-poly-reduced-mul)
                             (f11-poly-remainder f11-poly-divmod
                              f11-poly-add f11-poly-mul
                              f11-poly-raw-add f11-poly-raw-mul)))))

(defthm f11-quotient-coordinate-x-is-embed-x
  (equal (f11-quotient-coordinate-x modulus)
         (f11-quotient-coordinate-embed '(0 1) modulus)))

(local
 (defthm f11-normalize-idempotent-for-coordinate
   (equal (f11-normalize (f11-normalize polynomial))
          (f11-normalize polynomial))
   :hints (("Goal" :induct (f11-trim-trailing-zeros polynomial)
            :in-theory (enable f11-normalize f11-fix-coefficients
                               f11-trim-trailing-zeros
                               gfield::f11-fix)))))

(local
 (defthm f11-raw-scale-zero-for-coordinate
   (equal (f11-normalize (f11-poly-raw-scale 0 polynomial)) nil)
   :hints (("Goal" :induct (f11-poly-raw-scale 0 polynomial)
            :in-theory (enable f11-poly-raw-scale f11-normalize
                               f11-fix-coefficients f11-trim-trailing-zeros
                               gfield::f11-fix gfield::f11-mul)))))

(local
 (defthm f11-raw-scale-one-for-coordinate
   (equal (f11-poly-raw-scale 1 polynomial)
          (f11-fix-coefficients polynomial))
   :hints (("Goal" :induct (f11-poly-raw-scale 1 polynomial)
            :in-theory (enable f11-poly-raw-scale f11-fix-coefficients
                               gfield::f11-fix gfield::f11-mul)))))

(local
 (defthm f11-raw-add-nil-right-for-coordinate
   (equal (f11-poly-raw-add polynomial nil)
          (f11-fix-coefficients polynomial))
   :hints (("Goal" :in-theory (enable f11-poly-raw-add)))))

(local
 (defthm f11-normalize-of-fix-coefficients-for-coordinate
   (equal (f11-normalize (f11-fix-coefficients polynomial))
          (f11-normalize polynomial))
   :hints (("Goal" :in-theory
            (enable f11-normalize f11-fix-coefficients
                    f11-trim-trailing-zeros gfield::f11-fix)))))

(local
 (defthm f11-fix-coefficients-of-normalize-for-coordinate
   (equal (f11-fix-coefficients (f11-normalize polynomial))
          (f11-normalize polynomial))
   :hints (("Goal" :induct (f11-trim-trailing-zeros polynomial)
            :in-theory
            (enable f11-normalize f11-fix-coefficients
                    f11-trim-trailing-zeros gfield::f11-fix)))))

(local
 (defthm f11-normalize-cons-reconstruction-for-coordinate
   (implies (consp polynomial)
            (equal (f11-normalize
                    (cons (car polynomial)
                          (f11-normalize (cdr polynomial))))
                   (f11-normalize polynomial)))
   :hints (("Goal"
            :use ((:instance f11-normalize-idempotent-for-coordinate
                             (polynomial (cdr polynomial))))
            :in-theory
            (enable f11-normalize f11-fix-coefficients
                    f11-trim-trailing-zeros gfield::f11-fix)))))

(local
 (defthm f11-raw-add-zero-scale-tail-for-coordinate
   (equal (f11-poly-raw-add
           (f11-poly-raw-scale 0
                               (cdr (f11-fix-coefficients polynomial)))
           (f11-fix-coefficients polynomial))
          (f11-fix-coefficients polynomial))
   :hints (("Goal" :induct (f11-fix-coefficients polynomial)
            :in-theory
            (enable f11-poly-raw-add f11-poly-raw-scale
                    f11-fix-coefficients gfield::f11-add
                    gfield::f11-mul gfield::f11-fix)))))

(local
 (defthm f11-normalized-cons-form-for-coordinate
   (implies (consp (f11-normalize polynomial))
            (equal (cons (gfield::f11-fix
                          (car (f11-normalize polynomial)))
                         (f11-fix-coefficients
                          (cdr (f11-normalize polynomial))))
                   (f11-normalize polynomial)))
   :hints (("Goal"
            :use ((:instance f11-fix-coefficients-of-normalize-for-coordinate))
            :expand ((f11-fix-coefficients (f11-normalize polynomial)))
            :in-theory (disable f11-normalize gfield::f11-fix
                                f11-fix-coefficients-of-normalize-for-coordinate)))))

(local
 (defthm f11-raw-add-zero-scale-normalized-for-coordinate
   (equal (f11-poly-raw-add
           (f11-poly-raw-scale 0 (cdr (f11-normalize polynomial)))
           (f11-normalize polynomial))
          (f11-normalize polynomial))
   :hints (("Goal"
            :use ((:instance f11-raw-add-zero-scale-tail-for-coordinate
                             (polynomial (f11-normalize polynomial))))
            :in-theory (disable f11-poly-raw-add f11-poly-raw-scale
                                f11-normalize f11-fix-coefficients)))))

(local
 (defthm f11-normalize-zero-prefix-for-coordinate
   (implies (consp (f11-normalize polynomial))
            (equal (f11-normalize (cons 0 (f11-normalize polynomial)))
                   (cons 0 (f11-normalize polynomial))))
   :hints (("Goal"
            :use ((:instance f11-normalize-idempotent-for-coordinate))
            :in-theory
            (enable f11-normalize f11-fix-coefficients
                    f11-trim-trailing-zeros gfield::f11-fix)))))

(local
 (defthm f11-poly-mul-x-for-coordinate
   (equal (f11-poly-mul '(0 1) (f11-normalize polynomial))
          (if (consp (f11-normalize polynomial))
              (cons 0 (f11-normalize polynomial))
            nil))
   :hints (("Goal"
            :use ((:instance f11-raw-scale-zero-for-coordinate
                             (polynomial (f11-normalize polynomial)))
                  (:instance f11-raw-add-zero-scale-tail-for-coordinate
                             (polynomial (f11-normalize polynomial)))
                  (:instance f11-normalize-zero-prefix-for-coordinate)
                  (:instance f11-normalized-cons-form-for-coordinate))
            :in-theory (e/d (f11-poly-mul f11-poly-raw-mul
                                          f11-poly-scale f11-poly-raw-scale)
                                         (f11-normalize gfield::f11-fix))))))

(local
 (defthm f11-poly-add-constant-shift-for-coordinate
   (equal (f11-poly-add
           (list (gfield::f11-fix coefficient))
           (if (consp polynomial) (cons 0 polynomial) nil))
          (f11-normalize (cons coefficient polynomial)))
   :hints (("Goal" :cases ((consp polynomial))
            :use ((:instance f11-normalize-idempotent-for-coordinate)
                  (:instance f11-fix-coefficients-of-normalize-for-coordinate)
                  (:instance f11-normalize-of-fix-coefficients-for-coordinate
                             (polynomial (f11-normalize polynomial))))
            :in-theory
            (enable f11-poly-add f11-poly-raw-add
                    f11-normalize f11-fix-coefficients
                    f11-trim-trailing-zeros gfield::f11-fix
                    gfield::f11-add)))))

(local
 (defthm f11-poly-horner-reconstruction
   (implies (consp polynomial)
            (equal (f11-poly-add
                    (list (gfield::f11-fix (car polynomial)))
                    (f11-poly-mul '(0 1) (f11-normalize (cdr polynomial))))
                   (f11-normalize polynomial)))
   :hints (("Goal"
            :use ((:instance f11-poly-mul-x-for-coordinate
                             (polynomial (cdr polynomial)))
                  (:instance f11-poly-add-constant-shift-for-coordinate
                             (coefficient (car polynomial))
                             (polynomial (f11-normalize (cdr polynomial))))
                  (:instance f11-normalize-cons-reconstruction-for-coordinate))
            :in-theory (disable f11-poly-add f11-poly-mul
                                f11-normalize)))))

(local
 (defthm f11-normalize-atom-for-eval
   (implies (not (consp polynomial))
            (equal (f11-normalize polynomial) nil))
   :hints (("Goal" :in-theory
            (enable f11-normalize f11-fix-coefficients
                    f11-trim-trailing-zeros)))))

(local
 (defthm f11-quotient-coordinate-embed-add-for-eval
   (equal (f11-quotient-coordinate-add
           (f11-quotient-coordinate-embed left modulus)
           (f11-quotient-coordinate-embed right modulus) modulus)
          (f11-quotient-coordinate-embed (f11-poly-add left right) modulus))
   :hints (("Goal" :use f11-quotient-coordinate-embed-add
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm f11-quotient-coordinate-embed-mul-for-eval
   (equal (f11-quotient-coordinate-mul
           (f11-quotient-coordinate-embed left modulus)
           (f11-quotient-coordinate-embed right modulus) a b modulus)
          (f11-quotient-coordinate-embed (f11-poly-mul left right) modulus))
   :hints (("Goal" :use f11-quotient-coordinate-embed-mul
            :in-theory (theory 'minimal-theory)))))

(defthm f11-quotient-coordinate-eval-at-universal-x-embed
  (equal (f11-quotient-coordinate-eval
          polynomial (f11-quotient-coordinate-x modulus) a b modulus)
         (f11-quotient-coordinate-embed (f11-normalize polynomial) modulus))
  :rule-classes nil
  :hints (("Goal"
           :induct (f11-quotient-coordinate-eval
                    polynomial (f11-quotient-coordinate-x modulus) a b modulus)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(f11-quotient-coordinate-eval
              f11-quotient-coordinate-x-is-embed-x
              f11-quotient-coordinate-embed-add-for-eval
              f11-quotient-coordinate-embed-mul-for-eval
              f11-quotient-coordinate-embed-zero
              f11-normalize-atom-for-eval
              f11-poly-horner-reconstruction)))))

(defthm f11-quotient-coordinate-embed-of-normalize
  (equal (f11-quotient-coordinate-embed (f11-normalize polynomial) modulus)
         (f11-quotient-coordinate-embed polynomial modulus))
  :hints (("Goal"
           :use (f11-quotient-coordinate-embed-exact
                 (:instance f11-quotient-coordinate-embed-exact
                            (polynomial (f11-normalize polynomial)))
                 (:instance f11-poly-remainder-of-normalize-dividend
                            (dividend polynomial)))
           :in-theory (theory 'minimal-theory))))

(defthm f11-quotient-coordinate-embed-of-remainder
  (equal (f11-quotient-coordinate-embed
          (f11-poly-remainder polynomial modulus) modulus)
         (f11-quotient-coordinate-embed polynomial modulus))
  :hints (("Goal"
           :use (f11-quotient-coordinate-embed-exact
                 (:instance f11-quotient-coordinate-embed-exact
                            (polynomial (f11-poly-remainder
                                         polynomial modulus)))
                 (:instance f11-poly-remainder-idempotent
                            (dividend polynomial)))
           :in-theory (theory 'minimal-theory))))

(defthm f11-quotient-coordinate-eval-at-universal-x
  (equal (f11-quotient-coordinate-eval
          polynomial (f11-quotient-coordinate-x modulus) a b modulus)
         (f11-quotient-coordinate-embed
          (f11-poly-remainder polynomial modulus) modulus))
  :rule-classes nil
  :hints (("Goal"
           :use (f11-quotient-coordinate-eval-at-universal-x-embed
                 f11-quotient-coordinate-embed-of-normalize
                 f11-quotient-coordinate-embed-of-remainder)
           :in-theory (theory 'minimal-theory))))

(defthm f11-quotient-coordinate-modulus-eval-at-universal-x
  (equal (f11-quotient-coordinate-eval
          modulus (f11-quotient-coordinate-x modulus) a b modulus)
         (f11-quotient-coordinate-zero modulus))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance f11-quotient-coordinate-eval-at-universal-x
                            (polynomial modulus))
                 (:instance f11-poly-remainder-self))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(f11-quotient-coordinate-embed-zero)))))

(defun f11-quotient-coordinate-pow-spec (base n a b modulus)
  (declare (xargs :guard (natp n)))
  (if (zp n) (f11-quotient-coordinate-one modulus)
    (f11-quotient-coordinate-mul
     base (f11-quotient-coordinate-pow-spec base (1- n) a b modulus)
     a b modulus)))
(defun f11-quotient-coordinate-pow (base n a b modulus)
  (f11-quotient-coordinate-pow-spec
   (f11-quotient-coordinate-fix base modulus) (nfix n) a b modulus))
(defun f11-quotient-coordinate-cardinality-power (coordinate q a b modulus)
  (f11-quotient-coordinate-pow coordinate q a b modulus))
(defun f11-quotient-coordinate-cardinality-power-iterate
  (coordinate q iterations a b modulus)
  (f11-quotient-coordinate-pow
   coordinate (expt (nfix q) (nfix iterations)) a b modulus))

(defun f11-quotient-coordinate-cross-add-p
  (x1 y1 x2 y2 x3 y3 a b modulus)
  (let ((d (f11-quotient-coordinate-sub x2 x1 modulus))
        (n (f11-quotient-coordinate-sub y2 y1 modulus)))
    (and
     (equal (f11-quotient-coordinate-mul
             (f11-quotient-coordinate-mul d d a b modulus)
             (f11-quotient-coordinate-add
              x1 (f11-quotient-coordinate-add x2 x3 modulus) modulus)
             a b modulus)
            (f11-quotient-coordinate-mul n n a b modulus))
     (equal (f11-quotient-coordinate-mul
             d (f11-quotient-coordinate-add y1 y3 modulus) a b modulus)
            (f11-quotient-coordinate-mul
             n (f11-quotient-coordinate-sub x1 x3 modulus) a b modulus)))))
(defun f11-quotient-coordinate-cross-opposite-p (x1 y1 x2 y2 modulus)
  (and (equal (f11-quotient-coordinate-fix x1 modulus)
              (f11-quotient-coordinate-fix x2 modulus))
       (equal (f11-quotient-coordinate-add y1 y2 modulus)
              (f11-quotient-coordinate-zero modulus))))
(defun f11-quotient-coordinate-trace-candidate-p
  (x y q trace a b modulus)
  (let* ((pi-x (f11-quotient-coordinate-cardinality-power x q a b modulus))
         (pi-y (f11-quotient-coordinate-cardinality-power y q a b modulus))
         (pi2-x (f11-quotient-coordinate-cardinality-power-iterate
                 x q 2 a b modulus))
         (pi2-y (f11-quotient-coordinate-cardinality-power-iterate
                 y q 2 a b modulus))
         (minus-y (f11-quotient-coordinate-neg y modulus))
         (residue (mod (nfix trace) 3)))
    (if (equal residue 0)
        (f11-quotient-coordinate-cross-opposite-p
         pi2-x pi2-y x minus-y modulus)
      (f11-quotient-coordinate-cross-add-p
       pi2-x pi2-y x minus-y pi-x
       (if (equal residue 1) pi-y
         (f11-quotient-coordinate-neg pi-y modulus)) a b modulus))))

; This transparent theorem expands the concrete cardinality-power wrappers
; into executable natural powers. The following functional-instance theorem
; supplies the shared trace-program structure boundary  It applies to
; arbitrary (including malformed) ACL2 inputs and
; moduli; no canonicality, nonzero-modulus, field, or domain hypothesis is
; hidden in the specialization.
(defthm f11-quotient-coordinate-trace-candidate-execution-contract
  (equal (f11-quotient-coordinate-trace-candidate-p x y q trace a b modulus)
         (let* ((pi-x (f11-quotient-coordinate-pow x q a b modulus))
                (pi-y (f11-quotient-coordinate-pow y q a b modulus))
                (pi2-x (f11-quotient-coordinate-pow
                        x (expt (nfix q) 2) a b modulus))
                (pi2-y (f11-quotient-coordinate-pow
                        y (expt (nfix q) 2) a b modulus))
                (minus-y (f11-quotient-coordinate-neg y modulus))
                (residue (mod (nfix trace) 3)))
           (if (equal residue 0)
               (f11-quotient-coordinate-cross-opposite-p
                pi2-x pi2-y x minus-y modulus)
             (f11-quotient-coordinate-cross-add-p
              pi2-x pi2-y x minus-y pi-x
              (if (equal residue 1) pi-y
                (f11-quotient-coordinate-neg pi-y modulus))
              a b modulus))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (f11-quotient-coordinate-trace-candidate-p
                 f11-quotient-coordinate-cardinality-power
                 f11-quotient-coordinate-cardinality-power-iterate)
                (f11-quotient-coordinate-pow expt)))))


; Mechanical instance of the same operation-parametric program contract used
; by the generic production predicate.
(defthm f11-quotient-coordinate-trace-candidate-from-production-program
  (equal
   (f11-quotient-coordinate-trace-candidate-p x y q trace a b modulus)
   (let* ((pi-x (f11-quotient-coordinate-cardinality-power x q a b modulus))
          (pi-y (f11-quotient-coordinate-cardinality-power y q a b modulus))
          (pi2-x (f11-quotient-coordinate-cardinality-power-iterate
                  x q 2 a b modulus))
          (pi2-y (f11-quotient-coordinate-cardinality-power-iterate
                  y q 2 a b modulus))
          (minus-y (f11-quotient-coordinate-neg y modulus))
          (residue (mod (nfix trace) 3)))
     (if (equal residue 0)
         (f11-quotient-coordinate-cross-opposite-p
          pi2-x pi2-y x minus-y modulus)
       (f11-quotient-coordinate-cross-add-p
        pi2-x pi2-y x minus-y pi-x
        (if (equal residue 1) pi-y
          (f11-quotient-coordinate-neg pi-y modulus))
        a b modulus))))
  :rule-classes nil
  :hints (("Goal"
           :by (:functional-instance
                quotient-coordinate-trace-program-definition
                (trace-program-fix f11-quotient-coordinate-fix)
                (trace-program-zero f11-quotient-coordinate-zero)
                (trace-program-add f11-quotient-coordinate-add)
                (trace-program-neg f11-quotient-coordinate-neg)
                (trace-program-sub f11-quotient-coordinate-sub)
                (trace-program-mul f11-quotient-coordinate-mul)
                (trace-program-power
                 f11-quotient-coordinate-cardinality-power)
                (trace-program-power-iterate
                 f11-quotient-coordinate-cardinality-power-iterate)
                (trace-program-cross-add-p
                 f11-quotient-coordinate-cross-add-p)
                (trace-program-cross-opposite-p
                 f11-quotient-coordinate-cross-opposite-p)
                (trace-program-candidate-p
                 f11-quotient-coordinate-trace-candidate-p))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(f11-quotient-coordinate-cross-add-p
              f11-quotient-coordinate-cross-opposite-p
              f11-quotient-coordinate-trace-candidate-p nfix mod)))))

(verify-guards f11-quotient-coordinate-pow-spec)
(verify-guards f11-quotient-coordinate-pow)
(verify-guards f11-quotient-coordinate-cardinality-power)
(verify-guards f11-quotient-coordinate-cardinality-power-iterate)
(verify-guards f11-quotient-coordinate-cross-add-p)
(verify-guards f11-quotient-coordinate-cross-opposite-p)
(verify-guards f11-quotient-coordinate-trace-candidate-p)

(in-theory (disable f11-quotient-coordinate-pow-spec))
