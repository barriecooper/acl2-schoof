(in-package "GPOLY")

(include-book "mul")
(include-book "../../field/natural-scalar")

; RAW-DERIVATIVE-AUX processes a constant-first coefficient tail whose first
; entry has degree INDEX.  Atomic tails are discarded consistently with the
; other raw GPOLY operations.  The public operation normalizes both sides of
; this raw boundary and is therefore total and canonical.
(defun raw-derivative-aux (poly index)
  (declare (xargs :measure (acl2-count poly)))
  (if (atom poly)
      nil
    (cons (gfield::field-nat-mul (nfix index) (car poly))
          (raw-derivative-aux (cdr poly) (+ 1 (nfix index))))))

(defun poly-derivative (poly)
  (normalize
   (if (atom (fix-coefficients poly))
       nil
     (raw-derivative-aux (cdr (fix-coefficients poly)) 1))))

(defthm raw-derivative-aux-when-atom
  (implies (atom poly)
           (equal (raw-derivative-aux poly index) nil)))

(defthm raw-derivative-aux-of-cons
  (equal (raw-derivative-aux (cons coefficient poly) index)
         (cons (gfield::field-nat-mul (nfix index) coefficient)
               (raw-derivative-aux poly (+ 1 (nfix index))))))

(defthm true-listp-of-raw-derivative-aux
  (true-listp (raw-derivative-aux poly index)))

(defthm coefficient-list-p-of-raw-derivative-aux
  (coefficient-list-p (raw-derivative-aux poly index)))

(defthm len-of-raw-derivative-aux
  (equal (len (raw-derivative-aux poly index)) (len poly)))

(defthm raw-derivative-aux-of-fix-coefficients
  (equal (raw-derivative-aux (fix-coefficients poly) index)
         (raw-derivative-aux poly index))
  :hints (("Goal" :induct (raw-derivative-aux poly index))))

(defthm raw-derivative-aux-successor
  (equal (raw-derivative-aux poly (+ 1 (nfix index)))
         (raw-add (raw-derivative-aux poly index)
                  (fix-coefficients poly)))
  :hints (("Goal" :induct (raw-derivative-aux poly index)
           :in-theory (enable gfield::field-nat-mul-successor-total))))

(defthm raw-derivative-aux-of-zero-prefix
  (equal (raw-derivative-aux
          (cons (gfield::field-zero) poly) index)
         (cons (gfield::field-zero)
               (raw-derivative-aux poly (+ 1 (nfix index)))))
  :hints (("Goal" :in-theory (enable gfield::field-nat-mul-of-zero))))

(local
 (defthm raw-derivative-aux-of-raw-scale
   (equal (raw-derivative-aux (raw-scale a poly) index)
          (raw-scale a (raw-derivative-aux poly index)))
   :hints (("Goal" :induct (raw-derivative-aux poly index)
            :in-theory (enable gfield::field-nat-mul-of-mul-right
                               gfield::field-mul-commutative)))))

(local
 (defthm normalize-raw-derivative-aux-of-trim-trailing-zeros
   (equal (normalize
           (raw-derivative-aux (trim-trailing-zeros poly) index))
          (normalize (raw-derivative-aux poly index)))
   :hints (("Goal" :induct (raw-derivative-aux poly index)
            :in-theory (enable normalize
                               gfield::field-nat-mul-of-zero)))))

(local
 (defthm trim-raw-derivative-aux-of-trim-trailing-zeros
   (equal (trim-trailing-zeros
           (raw-derivative-aux (trim-trailing-zeros poly) index))
          (trim-trailing-zeros (raw-derivative-aux poly index)))
   :hints (("Goal"
            :use ((:instance
                   normalize-raw-derivative-aux-of-trim-trailing-zeros))
            :in-theory (enable normalize)))))

(local
 (defthm trim-raw-derivative-aux-when-trim-not-consp
   (implies (not (consp (trim-trailing-zeros poly)))
            (not (trim-trailing-zeros
                  (raw-derivative-aux poly index))))
   :hints (("Goal"
            :use ((:instance
                   trim-raw-derivative-aux-of-trim-trailing-zeros))
            :in-theory (enable trim-trailing-zeros)))))

(defthm poly-derivative-of-normalize
  (equal (poly-derivative (normalize poly))
         (poly-derivative poly))
  :hints (("Goal"
           :use ((:instance
                  normalize-raw-derivative-aux-of-trim-trailing-zeros
                  (poly (cdr (fix-coefficients poly))) (index 1))
                 (:instance
                 trim-raw-derivative-aux-of-trim-trailing-zeros
                  (poly (cdr (fix-coefficients poly))) (index 1)))
           :in-theory (enable poly-derivative normalize
                              trim-raw-derivative-aux-when-trim-not-consp))))

(defthm canonical-polynomial-p-of-poly-derivative
  (canonical-polynomial-p (poly-derivative poly)))

(defthm polynomial-p-of-poly-derivative
  (polynomial-p (poly-derivative poly)))

(defthm poly-derivative-of-nil
  (equal (poly-derivative nil) nil)
  :hints (("Goal" :in-theory (enable poly-derivative))))

(defthm poly-derivative-of-constant
  (equal (poly-derivative (list coefficient)) nil)
  :hints (("Goal" :in-theory (enable poly-derivative))))

(local
 (defun raw-derivative-coefficient-induct (n poly index)
   (if (zp (nfix n))
       (list poly index)
     (raw-derivative-coefficient-induct
      (1- (nfix n))
      (if (consp poly) (cdr poly) nil)
      (+ 1 (nfix index))))))

(local
 (defthm consp-of-fix-coefficients-for-coefficients
   (equal (consp (fix-coefficients x)) (consp x))))

(local
 (defthm raw-derivative-aux-of-nfix-index
   (equal (raw-derivative-aux polynomial (nfix index))
          (raw-derivative-aux polynomial index))
   :hints (("Goal" :induct (raw-derivative-aux polynomial index)))))

(local
 (defthm poly-coefficient-of-raw-derivative-aux-natural
   (implies (and (natp n) (natp index))
            (equal
             (poly-coefficient n (raw-derivative-aux polynomial index))
             (gfield::field-nat-mul
              (+ index n) (poly-coefficient n polynomial))))
   :hints (("Goal"
            :induct (raw-derivative-coefficient-induct n polynomial index)
            :in-theory (enable raw-derivative-aux poly-coefficient)))))

(local
 (defthm poly-coefficient-of-raw-derivative-aux
   (equal
    (poly-coefficient n (raw-derivative-aux polynomial index))
    (gfield::field-nat-mul
     (+ (nfix index) (nfix n))
     (poly-coefficient n polynomial)))
   :hints (("Goal"
            :use ((:instance poly-coefficient-of-raw-derivative-aux-natural
                             (n (nfix n)) (index (nfix index))))
            :in-theory (disable
                        poly-coefficient-of-raw-derivative-aux-natural)))))

(defthm poly-coefficient-of-poly-derivative
  (equal
   (poly-coefficient n (poly-derivative polynomial))
   (gfield::field-nat-mul
    (+ 1 (nfix n))
    (poly-coefficient (+ 1 (nfix n)) polynomial)))
  :hints (("Goal"
           :cases ((consp (fix-coefficients polynomial)))
           :do-not-induct t
           :use ((:instance poly-coefficient-of-normalize
                            (polynomial
                             (if (atom (fix-coefficients polynomial))
                                 nil
                               (raw-derivative-aux
                                (cdr (fix-coefficients polynomial)) 1))))
                 (:instance poly-coefficient-of-raw-derivative-aux
                            (polynomial
                             (cdr (fix-coefficients polynomial)))
                            (index 1))
                 (:instance poly-coefficient-of-successor
                            (polynomial (fix-coefficients polynomial)))
                 (:instance poly-coefficient-of-fix-coefficients
                            (n (+ 1 (nfix n)))
                            (polynomial polynomial)))
           :in-theory (e/d (poly-derivative
                            poly-coefficient-of-successor)
                           (normalize trim-trailing-zeros
                            poly-coefficient
                            poly-coefficient-of-normalize
                            poly-coefficient-of-raw-derivative-aux)))))

(local
 (defun raw-derivative-add-induct (x y index)
   (if (and (consp x) (consp y))
       (raw-derivative-add-induct (cdr x) (cdr y)
                                  (+ 1 (nfix index)))
     (list x y index))))

(local
 (defthm raw-derivative-aux-of-raw-add
   (equal (raw-derivative-aux (raw-add x y) index)
          (raw-add (raw-derivative-aux x index)
                   (raw-derivative-aux y index)))
   :hints (("Goal" :induct (raw-derivative-add-induct x y index)
           :in-theory (enable gfield::field-nat-mul-of-add)))))

(local
 (defthm raw-add-zero-scale-before-scaled-derivative
   (implies (consp g)
            (equal (raw-add
                    (raw-scale (gfield::field-zero) g)
                    (raw-scale a (raw-derivative-aux g 0)))
                   (raw-scale a (raw-derivative-aux g 0))))
   :hints
   (("Goal"
     :use ((:instance raw-add-of-zero-scale-left
                      (x (fix-coefficients g))
                      (y (raw-scale a (raw-derivative-aux g 0))))
           (:instance len-of-raw-derivative-aux (poly g) (index 0))
           (:instance len-of-raw-scale
                      (a a) (x (raw-derivative-aux g 0)))
           (:instance len-of-fix-coefficients (xs g)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(coefficient-list-p-of-raw-scale
        coefficient-list-p-of-raw-derivative-aux
        coefficient-list-p-of-fix-coefficients
        raw-scale-of-fix-coefficients))))))

(local
 (defthm coefficient-list-p-of-zero-prefix
   (equal (coefficient-list-p (cons (gfield::field-zero) x))
          (coefficient-list-p x))))

(local
 (defthm consp-of-raw-derivative-aux
   (equal (consp (raw-derivative-aux x index)) (consp x))))

(defthm raw-derivative-horner-step-alignment
   (implies
    (consp g)
    (equal
    (raw-add
     (raw-scale a (raw-derivative-aux g 0))
     (cons (gfield::field-zero)
           (raw-add
            (raw-mul (raw-derivative-aux f 1) g)
            (raw-mul f (raw-derivative-aux g 0)))))
    (raw-add
     (raw-mul
      (cons (gfield::field-zero) (raw-derivative-aux f 1)) g)
     (raw-mul (cons a f) (raw-derivative-aux g 0)))))
   :hints
   (("Goal"
     :use
     ((:instance raw-add-interchange
       (a (raw-scale (gfield::field-zero) g))
       (b (cons (gfield::field-zero)
                (raw-mul (raw-derivative-aux f 1) g)))
       (c (raw-scale a (raw-derivative-aux g 0)))
       (d (cons (gfield::field-zero)
                (raw-mul f (raw-derivative-aux g 0)))))
      (:instance raw-add-zero-scale-before-scaled-derivative)
      (:instance raw-add-of-zero-prefixes
       (x (raw-mul (raw-derivative-aux f 1) g))
       (y (raw-mul f (raw-derivative-aux g 0))))
      (:instance coefficient-list-p-of-raw-scale
       (a (gfield::field-zero)) (x g))
      (:instance coefficient-list-p-of-raw-scale
       (a a) (x (raw-derivative-aux g 0)))
      (:instance raw-add-associative
       (x (raw-scale a (raw-derivative-aux g 0)))
       (y (cons (gfield::field-zero)
                (raw-mul (raw-derivative-aux f 1) g)))
       (z (cons (gfield::field-zero)
                (raw-mul f (raw-derivative-aux g 0))))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(raw-mul-of-cons
        raw-mul-when-atom-right
        coefficient-list-p
        coefficient-list-p-of-raw-scale
        coefficient-list-p-of-raw-mul
        coefficient-list-p-of-raw-derivative-aux
        coefficient-list-p-of-zero-prefix
        consp-of-raw-derivative-aux
        gfield::field-element-p-of-zero)))))

(local
 (defthm raw-derivative-aux-of-raw-neg
   (equal (raw-derivative-aux (raw-neg x) index)
          (raw-neg (raw-derivative-aux x index)))
   :hints (("Goal" :induct (raw-derivative-aux x index)
            :in-theory (enable gfield::field-nat-mul-of-neg)))))

(local
 (defthm cdr-of-raw-add-when-both-consp
   (implies (and (consp x) (consp y))
            (equal (cdr (raw-add x y))
                   (raw-add (cdr x) (cdr y))))))

(local
 (defthm cdr-of-fix-coefficients-when-consp
   (implies (consp x)
            (equal (cdr (fix-coefficients x))
                   (fix-coefficients (cdr x))))))

(local
 (defthm consp-of-fix-coefficients
   (equal (consp (fix-coefficients x)) (consp x))))

(local
 (defthm cdr-of-raw-neg-when-consp
   (implies (consp x)
            (equal (cdr (raw-neg x)) (raw-neg (cdr x))))))

(local
 (defthm normalize-raw-neg-of-normalize
   (equal (normalize (raw-neg (normalize x)))
          (normalize (raw-neg x)))
   :hints (("Goal" :use ((:instance poly-neg-of-normalize))
            :in-theory (enable poly-neg)))))

(local
 (defthm poly-derivative-of-raw-add
   (equal (poly-derivative (raw-add x y))
          (poly-add (poly-derivative x)
                    (poly-derivative y)))
   :hints (("Goal"
            :use ((:instance raw-derivative-aux-of-raw-add
                             (x (cdr (fix-coefficients x)))
                             (y (cdr (fix-coefficients y)))
                             (index 1)))
            :do-not-induct t
            :in-theory (e/d (poly-derivative poly-add raw-add)
                            (normalize trim-trailing-zeros))))))

(defthm poly-derivative-of-poly-add
  (equal (poly-derivative (poly-add x y))
         (poly-add (poly-derivative x)
                   (poly-derivative y)))
  :hints (("Goal"
           :use ((:instance poly-derivative-of-normalize
                            (poly (raw-add (normalize x) (normalize y))))
                 (:instance poly-derivative-of-raw-add
                            (x (normalize x)) (y (normalize y)))
                 (:instance poly-derivative-of-normalize (poly x))
                 (:instance poly-derivative-of-normalize (poly y)))
           :in-theory (e/d (poly-add) (poly-derivative-of-normalize
                                       poly-derivative-of-raw-add)))))

(local
 (defthm poly-derivative-of-raw-neg
   (equal (poly-derivative (raw-neg x))
          (poly-neg (poly-derivative x)))
   :hints (("Goal"
            :use ((:instance raw-derivative-aux-of-raw-neg
                             (x (cdr (fix-coefficients x))) (index 1))
                  (:instance poly-neg-of-normalize
                             (x (raw-derivative-aux
                                 (cdr (fix-coefficients x)) 1))))
            :do-not-induct t
            :in-theory (e/d (poly-derivative poly-neg raw-neg)
                            (normalize trim-trailing-zeros))))))

(defthm poly-derivative-of-poly-neg
  (equal (poly-derivative (poly-neg x))
         (poly-neg (poly-derivative x)))
  :hints (("Goal"
           :use ((:instance poly-derivative-of-normalize (poly x))
                 (:instance poly-derivative-of-normalize
                            (poly (raw-neg (normalize x))))
                 (:instance poly-derivative-of-raw-neg
                            (x (normalize x))))
           :in-theory (e/d (poly-neg) (poly-derivative-of-normalize
                                       poly-derivative-of-raw-neg)))))

(defthm poly-derivative-of-poly-sub
  (equal (poly-derivative (poly-sub x y))
         (poly-sub (poly-derivative x)
                   (poly-derivative y)))
  :hints (("Goal"
           :use ((:instance poly-derivative-of-poly-add
                            (x x) (y (poly-neg y)))
                 (:instance poly-derivative-of-poly-neg (x y)))
           :in-theory (e/d (poly-sub) (poly-derivative-of-poly-add
                                       poly-derivative-of-poly-neg)))))

(defthm len-of-poly-derivative-upper-bound
  (<= (len (poly-derivative poly))
      (if (consp poly) (1- (len poly)) 0))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance len-of-normalize
                            (xs (raw-derivative-aux
                                 (cdr (fix-coefficients poly)) 1)))
                 (:instance len-of-raw-derivative-aux
                            (poly (cdr (fix-coefficients poly)))
                            (index 1))
                 (:instance len-of-fix-coefficients (xs poly)))
           :in-theory (enable poly-derivative))))

(verify-guards raw-derivative-aux)
(verify-guards poly-derivative)
