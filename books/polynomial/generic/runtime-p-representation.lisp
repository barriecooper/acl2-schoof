(in-package "GPOLY")

(include-book "pfield-instance")
(local (include-book "arithmetic-5/top" :dir :system))

; Runtime-p coefficient arithmetic.  A malformed modulus is totalized to 2;
; this is an execution convention, not a validity predicate for the input p.
(defun runtime-p-effective-modulus (p)
  (declare (xargs :guard t))
  (if (and (integerp p) (<= 2 p)) p 2))

(defun runtime-p-coefficient-p (x p)
  (declare (xargs :guard t))
  (pfield::fep x (runtime-p-effective-modulus p)))
(defun runtime-p-coefficient-fix (x p)
  (declare (xargs :guard t))
  (pfield::fep-fix x (runtime-p-effective-modulus p)))
(defun runtime-p-zero (p) (declare (ignore p) (xargs :guard t)) 0)
(defun runtime-p-one (p) (declare (ignore p) (xargs :guard t)) 1)
(defun runtime-p-add (x y p)
  (pfield::add (runtime-p-coefficient-fix x p)
               (runtime-p-coefficient-fix y p)
               (runtime-p-effective-modulus p)))
(defun runtime-p-neg (x p)
  (pfield::neg (runtime-p-coefficient-fix x p)
               (runtime-p-effective-modulus p)))
(defun runtime-p-sub (x y p) (runtime-p-add x (runtime-p-neg y p) p))
(defun runtime-p-mul (x y p)
  (pfield::mul (runtime-p-coefficient-fix x p)
               (runtime-p-coefficient-fix y p)
               (runtime-p-effective-modulus p)))

(defun runtime-p-coefficient-list-p (xs p)
  (if (atom xs) (null xs)
    (and (runtime-p-coefficient-p (car xs) p)
         (runtime-p-coefficient-list-p (cdr xs) p))))
(defun runtime-p-fix-coefficients (xs p)
  (if (atom xs) nil
    (cons (runtime-p-coefficient-fix (car xs) p)
          (runtime-p-fix-coefficients (cdr xs) p))))
(defun runtime-p-trim-trailing-zeros (xs p)
  (if (atom xs) nil
    (let ((tail (runtime-p-trim-trailing-zeros (cdr xs) p)))
      (if (and (equal (runtime-p-coefficient-fix (car xs) p) 0)
               (endp tail))
          nil
        (cons (car xs) tail)))))
(defun runtime-p-normalize (xs p)
  (runtime-p-trim-trailing-zeros
   (runtime-p-fix-coefficients xs p) p))
(defun runtime-p-canonical-polynomial-p (xs p)
  (and (runtime-p-coefficient-list-p xs p)
       (or (not (consp xs)) (not (equal (car (last xs)) 0)))))

(defun runtime-p-raw-add (x y p)
  (cond ((atom x) (runtime-p-fix-coefficients y p))
        ((atom y) (runtime-p-fix-coefficients x p))
        (t (cons (runtime-p-add (car x) (car y) p)
                 (runtime-p-raw-add (cdr x) (cdr y) p)))))
(defun runtime-p-poly-add (x y p)
  (runtime-p-normalize
   (runtime-p-raw-add (runtime-p-normalize x p)
                      (runtime-p-normalize y p) p) p))
(defun runtime-p-raw-neg (x p)
  (if (atom x) nil
    (cons (runtime-p-neg (car x) p)
          (runtime-p-raw-neg (cdr x) p))))
(defun runtime-p-poly-neg (x p)
  (runtime-p-normalize (runtime-p-raw-neg (runtime-p-normalize x p) p) p))
(defun runtime-p-poly-sub (x y p)
  (runtime-p-poly-add x (runtime-p-poly-neg y p) p))
(defun runtime-p-polynomial-one (p)
  (list (runtime-p-one p)))
(defun runtime-p-raw-scale (a x p)
  (if (atom x) nil
    (cons (runtime-p-mul (runtime-p-coefficient-fix a p)
                         (runtime-p-coefficient-fix (car x) p) p)
          (runtime-p-raw-scale a (cdr x) p))))
(defun runtime-p-poly-scale (a x p)
  (runtime-p-normalize
   (runtime-p-raw-scale (runtime-p-coefficient-fix a p)
                        (runtime-p-normalize x p) p) p))
(defun runtime-p-raw-mul (x y p)
  (if (or (atom x) (atom y)) nil
    (runtime-p-raw-add
     (runtime-p-raw-scale (car x) y p)
     (cons 0 (runtime-p-raw-mul (cdr x) y p)) p)))
(defun runtime-p-poly-mul (x y p)
  (runtime-p-normalize
   (runtime-p-raw-mul (runtime-p-normalize x p)
                      (runtime-p-normalize y p) p) p))

(defun runtime-p-vector-p (xs width p)
  (and (runtime-p-coefficient-list-p xs p)
       (equal (len xs) (nfix width))))
(defun runtime-p-coding-bound (width p)
  (expt (runtime-p-effective-modulus p) (nfix width)))
(defun runtime-p-rank (coefficients p)
  (if (consp coefficients)
      (+ (runtime-p-coefficient-fix (car coefficients) p)
         (* (runtime-p-effective-modulus p)
            (runtime-p-rank (cdr coefficients) p)))
    0))
(defun runtime-p-unrank (width k p)
  (declare (xargs :measure (nfix width)))
  (if (zp (nfix width)) nil
    (cons (runtime-p-coefficient-fix
           (mod (nfix k) (runtime-p-effective-modulus p)) p)
          (runtime-p-unrank
           (1- (nfix width))
           (floor (nfix k) (runtime-p-effective-modulus p)) p))))

; Coefficient representation laws.
(defthm integerp-of-runtime-p-effective-modulus
  (integerp (runtime-p-effective-modulus p)) :rule-classes :type-prescription)
(defthm runtime-p-effective-modulus-lower-bound
  (<= 2 (runtime-p-effective-modulus p)) :rule-classes :linear)
(defthm booleanp-of-runtime-p-coefficient-p
  (booleanp (runtime-p-coefficient-p x p)) :rule-classes :type-prescription)
(defthm runtime-p-coefficient-p-of-fix
  (runtime-p-coefficient-p (runtime-p-coefficient-fix x p) p))
(defthm runtime-p-coefficient-fix-when-recognized
  (implies (runtime-p-coefficient-p x p)
           (equal (runtime-p-coefficient-fix x p) x)))
(defthm runtime-p-coefficient-fix-idempotent
  (equal (runtime-p-coefficient-fix (runtime-p-coefficient-fix x p) p)
         (runtime-p-coefficient-fix x p)))
(defthm runtime-p-coefficient-p-of-zero
  (runtime-p-coefficient-p (runtime-p-zero p) p))
(defthm runtime-p-coefficient-p-of-one
  (runtime-p-coefficient-p (runtime-p-one p) p))
(defthm runtime-p-coefficient-fix-of-zero
  (equal (runtime-p-coefficient-fix (runtime-p-zero p) p)
         (runtime-p-zero p)))
(defthm runtime-p-coefficient-fix-of-one
  (equal (runtime-p-coefficient-fix (runtime-p-one p) p)
         (runtime-p-one p)))
(defthm runtime-p-coefficient-fix-bounds
  (and (integerp (runtime-p-coefficient-fix x p))
       (<= 0 (runtime-p-coefficient-fix x p))
       (< (runtime-p-coefficient-fix x p) (runtime-p-effective-modulus p)))
  :rule-classes :rewrite)
(defthm runtime-p-coefficient-p-of-add
  (runtime-p-coefficient-p (runtime-p-add x y p) p))
(defthm runtime-p-coefficient-p-of-neg
  (runtime-p-coefficient-p (runtime-p-neg x p) p))
(defthm runtime-p-coefficient-p-of-sub
  (runtime-p-coefficient-p (runtime-p-sub x y p) p))
(defthm runtime-p-coefficient-p-of-mul
  (runtime-p-coefficient-p (runtime-p-mul x y p) p))
(defthm runtime-p-add-of-fixes
  (equal (runtime-p-add (runtime-p-coefficient-fix x p)
                        (runtime-p-coefficient-fix y p) p)
         (runtime-p-add x y p)))
(defthm runtime-p-neg-of-fix
  (equal (runtime-p-neg (runtime-p-coefficient-fix x p) p)
         (runtime-p-neg x p)))
(defthm runtime-p-sub-of-fixes
  (equal (runtime-p-sub (runtime-p-coefficient-fix x p)
                        (runtime-p-coefficient-fix y p) p)
         (runtime-p-sub x y p)))
(defthm runtime-p-mul-of-fixes
  (equal (runtime-p-mul (runtime-p-coefficient-fix x p)
                        (runtime-p-coefficient-fix y p) p)
         (runtime-p-mul x y p)))

; Structural polynomial laws.
(defthm true-listp-of-runtime-p-fix-coefficients
  (true-listp (runtime-p-fix-coefficients xs p)) :rule-classes :type-prescription)
(defthm runtime-p-coefficient-list-p-of-fix-coefficients
  (runtime-p-coefficient-list-p (runtime-p-fix-coefficients xs p) p))
(defthm runtime-p-fix-coefficients-when-recognized
  (implies (runtime-p-coefficient-list-p xs p)
           (equal (runtime-p-fix-coefficients xs p) xs)))
(defthm runtime-p-fix-coefficients-idempotent
  (equal (runtime-p-fix-coefficients
          (runtime-p-fix-coefficients xs p) p)
         (runtime-p-fix-coefficients xs p)))
(defthm runtime-p-coefficient-list-p-of-trim-trailing-zeros
  (implies (runtime-p-coefficient-list-p xs p)
           (runtime-p-coefficient-list-p
            (runtime-p-trim-trailing-zeros xs p) p)))
(defthm runtime-p-consp-of-trim-implies-last-nonzero
  (implies (consp (runtime-p-trim-trailing-zeros xs p))
           (not (equal (car (last (runtime-p-trim-trailing-zeros xs p))) 0))))
(defthm runtime-p-canonical-polynomial-p-of-normalize
  (runtime-p-canonical-polynomial-p (runtime-p-normalize xs p) p))
(defthm runtime-p-normalize-when-canonical
  (implies (runtime-p-canonical-polynomial-p xs p)
           (equal (runtime-p-normalize xs p) xs)))
(defthm runtime-p-normalize-idempotent
  (equal (runtime-p-normalize (runtime-p-normalize xs p) p)
         (runtime-p-normalize xs p)))
(defthm runtime-p-normalize-equal-nil-when-not-consp
  (implies (not (consp (runtime-p-normalize xs p)))
           (equal (runtime-p-normalize xs p) nil)))
(defthm runtime-p-normalize-of-fix-coefficients
  (equal (runtime-p-normalize (runtime-p-fix-coefficients xs p) p)
         (runtime-p-normalize xs p)))
(defthm runtime-p-canonical-polynomial-p-of-poly-add
  (runtime-p-canonical-polynomial-p (runtime-p-poly-add x y p) p))
(defthm runtime-p-canonical-polynomial-p-of-poly-neg
  (runtime-p-canonical-polynomial-p (runtime-p-poly-neg x p) p))
(defthm runtime-p-canonical-polynomial-p-of-poly-sub
  (runtime-p-canonical-polynomial-p (runtime-p-poly-sub x y p) p))
(defthm runtime-p-canonical-polynomial-p-of-poly-scale
  (runtime-p-canonical-polynomial-p (runtime-p-poly-scale a x p) p))
(defthm runtime-p-canonical-polynomial-p-of-poly-mul
  (runtime-p-canonical-polynomial-p (runtime-p-poly-mul x y p) p))
(defthm runtime-p-normalize-of-nil
  (equal (runtime-p-normalize nil p) nil))
(defthm runtime-p-canonical-polynomial-p-of-polynomial-one
  (runtime-p-canonical-polynomial-p (runtime-p-polynomial-one p) p))
(defthm runtime-p-normalize-of-polynomial-one
  (equal (runtime-p-normalize (runtime-p-polynomial-one p) p)
         (runtime-p-polynomial-one p)))
(defthm runtime-p-poly-add-of-normalizes
  (equal (runtime-p-poly-add (runtime-p-normalize x p)
                             (runtime-p-normalize y p) p)
         (runtime-p-poly-add x y p)))
(defthm runtime-p-poly-neg-of-normalize
  (equal (runtime-p-poly-neg (runtime-p-normalize x p) p)
         (runtime-p-poly-neg x p)))
(defthm runtime-p-poly-sub-of-normalizes
  (equal (runtime-p-poly-sub (runtime-p-normalize x p)
                             (runtime-p-normalize y p) p)
         (runtime-p-poly-sub x y p)))
(defthm runtime-p-poly-scale-of-normalize
  (equal (runtime-p-poly-scale a (runtime-p-normalize x p) p)
         (runtime-p-poly-scale a x p)))
(defthm runtime-p-poly-mul-of-normalizes
  (equal (runtime-p-poly-mul (runtime-p-normalize x p)
                             (runtime-p-normalize y p) p)
         (runtime-p-poly-mul x y p)))

; Radix representation laws.
(defthm runtime-p-coding-bound-definition
  (equal (runtime-p-coding-bound width p)
         (expt (runtime-p-effective-modulus p) (nfix width))))
(defthm runtime-p-coding-bound-zero-width
  (equal (runtime-p-coding-bound 0 p) 1))
(defthm natp-of-runtime-p-rank
  (natp (runtime-p-rank coefficients p))
  :rule-classes (:rewrite :type-prescription))
(defthm true-listp-of-runtime-p-unrank
  (true-listp (runtime-p-unrank width k p)) :rule-classes :type-prescription)
(defthm len-of-runtime-p-unrank
  (equal (len (runtime-p-unrank width k p)) (nfix width)))
(defthm runtime-p-coefficient-list-p-of-unrank
  (runtime-p-coefficient-list-p (runtime-p-unrank width k p) p))
(defthm runtime-p-vector-p-of-unrank
  (runtime-p-vector-p (runtime-p-unrank width k p) width p))

(local (defthm runtime-p-rank-upper-bound-by-len
  (implies (runtime-p-coefficient-list-p coefficients p)
           (< (runtime-p-rank coefficients p)
              (expt (runtime-p-effective-modulus p) (len coefficients))))
  :hints (("Goal" :induct (runtime-p-rank coefficients p) :nonlinearp t))))
(defthm runtime-p-rank-upper-bound
  (implies (runtime-p-vector-p coefficients width p)
           (< (runtime-p-rank coefficients p)
              (runtime-p-coding-bound width p)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use runtime-p-rank-upper-bound-by-len
           :in-theory (enable runtime-p-vector-p runtime-p-coding-bound))))

(defthm runtime-p-rank-of-unrank
  (implies (and (natp k) (< k (runtime-p-coding-bound width p)))
           (equal (runtime-p-rank (runtime-p-unrank width k p) p) k))
  :rule-classes nil
  :hints (("Goal" :induct (runtime-p-unrank width k p)
           :in-theory (enable runtime-p-coding-bound))))
(local (defthm runtime-p-mod-of-mixed-radix-step
  (implies (and (natp digit) (< digit radix) (posp radix) (natp rest))
           (equal (mod (+ digit (* radix rest)) radix) digit))))
(local (defthm runtime-p-floor-of-mixed-radix-step
  (implies (and (natp digit) (< digit radix) (posp radix) (natp rest))
           (equal (floor (+ digit (* radix rest)) radix) rest))))
(local (defthm runtime-p-unrank-of-rank-by-len
  (implies (runtime-p-coefficient-list-p coefficients p)
           (equal (runtime-p-unrank (len coefficients)
                                    (runtime-p-rank coefficients p) p)
                  coefficients))
  :hints (("Goal" :induct (runtime-p-rank coefficients p)
           :in-theory (e/d (runtime-p-coefficient-list-p
                             runtime-p-rank runtime-p-unrank
                             runtime-p-vector-p)
                            (runtime-p-effective-modulus
                             runtime-p-coefficient-fix))))))
(defthm runtime-p-unrank-of-rank
  (implies (runtime-p-vector-p coefficients width p)
           (equal (runtime-p-unrank width (runtime-p-rank coefficients p) p)
                  coefficients))
  :rule-classes nil
  :hints (("Goal" :use runtime-p-unrank-of-rank-by-len
           :in-theory (enable runtime-p-vector-p))))

; Exact fixed-p endpoints.  Small coefficient equations rewrite; recursive
; polynomial correspondence endpoints are deliberately non-rewriting bridges.
(defthm runtime-p-effective-modulus-of-pfield-modulus
  (equal (runtime-p-effective-modulus (gfield::pfield-modulus))
         (gfield::pfield-modulus)))
(defthm runtime-p-zero-pfield-correspondence
  (equal (runtime-p-zero (gfield::pfield-modulus))
         (gfield::pfield-zero)))
(defthm runtime-p-one-pfield-correspondence
  (equal (runtime-p-one (gfield::pfield-modulus))
         (gfield::pfield-one)))
(defthm runtime-p-coefficient-fix-pfield-correspondence
  (equal (runtime-p-coefficient-fix x (gfield::pfield-modulus))
         (gfield::pfield-fix x)))
(defthm runtime-p-add-pfield-correspondence
  (equal (runtime-p-add x y (gfield::pfield-modulus))
         (gfield::pfield-add x y)))
(defthm runtime-p-neg-pfield-correspondence
  (equal (runtime-p-neg x (gfield::pfield-modulus))
         (gfield::pfield-neg x)))
(defthm runtime-p-sub-pfield-correspondence
  (equal (runtime-p-sub x y (gfield::pfield-modulus))
         (gfield::pfield-sub x y))
  :hints (("Goal" :in-theory (enable runtime-p-sub gfield::pfield-sub))))
(defthm runtime-p-mul-pfield-correspondence
  (equal (runtime-p-mul x y (gfield::pfield-modulus))
         (gfield::pfield-mul x y)))
(local (defthm runtime-p-fix-coefficients-pfield-correspondence
  (equal (runtime-p-fix-coefficients x (gfield::pfield-modulus))
         (pfield-fix-coefficients x))
  :hints (("Goal" :induct (runtime-p-fix-coefficients
                            x (gfield::pfield-modulus))
           :in-theory (enable pfield-fix-coefficients
                              runtime-p-coefficient-fix-pfield-correspondence)))))
(local (defthm runtime-p-trim-pfield-correspondence
  (equal (runtime-p-trim-trailing-zeros x (gfield::pfield-modulus))
         (pfield-trim-trailing-zeros x))
  :hints (("Goal" :induct (runtime-p-trim-trailing-zeros
                            x (gfield::pfield-modulus))
           :in-theory (enable pfield-trim-trailing-zeros
                              runtime-p-coefficient-fix-pfield-correspondence)))))
(defthm runtime-p-normalize-pfield-correspondence
  (equal (runtime-p-normalize x (gfield::pfield-modulus))
         (pfield-normalize x))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-p-normalize pfield-normalize))))
(local (defthm runtime-p-raw-add-pfield-correspondence
  (equal (runtime-p-raw-add x y (gfield::pfield-modulus))
         (pfield-raw-add x y))
  :hints (("Goal" :induct (runtime-p-raw-add x y (gfield::pfield-modulus))
           :in-theory (enable pfield-raw-add
                              runtime-p-add-pfield-correspondence)))))
(local (defthm runtime-p-raw-scale-pfield-correspondence
  (equal (runtime-p-raw-scale a x (gfield::pfield-modulus))
         (pfield-raw-scale a x))
  :hints (("Goal" :induct (runtime-p-raw-scale a x (gfield::pfield-modulus))
           :in-theory (enable pfield-raw-scale
                              runtime-p-coefficient-fix-pfield-correspondence
                              runtime-p-mul-pfield-correspondence)))))
(local (defthm runtime-p-raw-neg-pfield-correspondence
  (equal (runtime-p-raw-neg x (gfield::pfield-modulus))
         (pfield-raw-neg x))
  :hints (("Goal" :induct (runtime-p-raw-neg x (gfield::pfield-modulus))
           :in-theory (enable pfield-raw-neg
                              runtime-p-neg-pfield-correspondence)))))
(local (defthm runtime-p-raw-mul-pfield-correspondence
  (equal (runtime-p-raw-mul x y (gfield::pfield-modulus))
         (pfield-raw-mul x y))
  :hints (("Goal" :induct (runtime-p-raw-mul x y (gfield::pfield-modulus))
           :in-theory (enable pfield-raw-mul)))))
(defthm runtime-p-poly-add-pfield-correspondence
  (equal (runtime-p-poly-add x y (gfield::pfield-modulus))
         (pfield-poly-add x y))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-p-poly-add pfield-poly-add))))
(defthm runtime-p-poly-neg-pfield-correspondence
  (equal (runtime-p-poly-neg x (gfield::pfield-modulus))
         (pfield-poly-neg x))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-p-poly-neg pfield-poly-neg))))
(defthm runtime-p-poly-sub-pfield-correspondence
  (equal (runtime-p-poly-sub x y (gfield::pfield-modulus))
         (pfield-poly-sub x y))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance runtime-p-poly-add-pfield-correspondence
                     (x x) (y (runtime-p-poly-neg y
                                                  (gfield::pfield-modulus))))
          (:instance runtime-p-poly-neg-pfield-correspondence (x y)))
    :in-theory (enable runtime-p-poly-sub pfield-poly-sub))))
(defthm runtime-p-poly-scale-pfield-correspondence
  (equal (runtime-p-poly-scale a x (gfield::pfield-modulus))
         (pfield-poly-scale a x))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-p-poly-scale pfield-poly-scale))))
(defthm runtime-p-poly-mul-pfield-correspondence
  (equal (runtime-p-poly-mul x y (gfield::pfield-modulus))
         (pfield-poly-mul x y))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-p-poly-mul pfield-poly-mul))))

(verify-guards runtime-p-effective-modulus)
(verify-guards runtime-p-coefficient-fix)
(verify-guards runtime-p-add)
(verify-guards runtime-p-neg)
(verify-guards runtime-p-sub)
(verify-guards runtime-p-mul)
(verify-guards runtime-p-coefficient-list-p)
(verify-guards runtime-p-fix-coefficients)
(verify-guards runtime-p-trim-trailing-zeros)
(verify-guards runtime-p-normalize)
(verify-guards runtime-p-canonical-polynomial-p)
(verify-guards runtime-p-raw-add)
(verify-guards runtime-p-poly-add)
(verify-guards runtime-p-raw-neg)
(verify-guards runtime-p-poly-neg)
(verify-guards runtime-p-poly-sub)
(verify-guards runtime-p-polynomial-one)
(verify-guards runtime-p-raw-scale)
(verify-guards runtime-p-poly-scale)
(verify-guards runtime-p-raw-mul)
(verify-guards runtime-p-poly-mul)
(verify-guards runtime-p-vector-p)
(verify-guards runtime-p-coding-bound)
(verify-guards runtime-p-rank)
(verify-guards runtime-p-unrank)
