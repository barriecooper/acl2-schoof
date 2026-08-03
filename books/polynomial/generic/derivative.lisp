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

; These two sums are deliberately local proof devices.  TOTAL stays fixed
; while COUNT is the decreasing upper endpoint.
(local
 (defun product-rule-left-weighted-sum (total count f g)
   (declare (xargs :measure (nfix count)))
   (if (zp (nfix count))
       (gfield::field-nat-mul
        0 (gfield::field-mul (poly-coefficient 0 f)
                             (poly-coefficient (nfix total) g)))
     (gfield::field-add
      (product-rule-left-weighted-sum total (1- (nfix count)) f g)
      (gfield::field-nat-mul
       (nfix count)
       (gfield::field-mul
        (poly-coefficient (nfix count) f)
        (poly-coefficient (- (nfix total) (nfix count)) g)))))))

(local
 (defun product-rule-right-weighted-sum (total count f g)
   (declare (xargs :measure (nfix count)))
   (if (zp (nfix count))
       (gfield::field-nat-mul
        (nfix total)
        (gfield::field-mul (poly-coefficient 0 f)
                           (poly-coefficient (nfix total) g)))
     (gfield::field-add
      (product-rule-right-weighted-sum total (1- (nfix count)) f g)
      (gfield::field-nat-mul
       (- (nfix total) (nfix count))
       (gfield::field-mul
        (poly-coefficient (nfix count) f)
        (poly-coefficient (- (nfix total) (nfix count)) g)))))))

(local
 (defthm natural-index-split
   (implies (and (natp total) (natp j) (<= j total))
            (equal total (+ j (- total j))))
   :rule-classes nil))

(local
 (defthm product-rule-pointwise-split
   (implies
    (and (natp total) (natp j) (<= j total))
    (equal
     (gfield::field-nat-mul
      total
      (gfield::field-mul (poly-coefficient j f)
                         (poly-coefficient (- total j) g)))
     (gfield::field-add
      (gfield::field-nat-mul
       j (gfield::field-mul (poly-coefficient j f)
                            (poly-coefficient (- total j) g)))
      (gfield::field-nat-mul
       (- total j)
       (gfield::field-mul (poly-coefficient j f)
                          (poly-coefficient (- total j) g))))))
   :rule-classes nil
   :hints (("Goal"
            :use (natural-index-split
                  (:instance gfield::field-nat-mul-of-sum
                             (m j) (n (- total j))
                             (x (gfield::field-mul
                                 (poly-coefficient j f)
                                 (poly-coefficient (- total j) g)))))
            :in-theory (disable gfield::field-nat-mul-of-sum)))))

(local
 (defthm product-rule-exact-reassociation
   (equal (gfield::field-add
           (gfield::field-add a b)
           (gfield::field-add c d))
          (gfield::field-add
           (gfield::field-add a c)
           (gfield::field-add b d)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance gfield::field-add-associative (x a) (y b)
                             (z (gfield::field-add c d)))
                  (:instance gfield::field-add-associative (x a) (y c)
                             (z (gfield::field-add b d)))
                  (:instance gfield::field-add-associative (x b) (y c) (z d))
                  (:instance gfield::field-add-commutative (x b) (y c)))
            :in-theory (disable gfield::field-add-associative
                                gfield::field-add-commutative)))))

(local
 (defthm product-rule-pointwise-split-rewrite
   (implies
    (and (natp total) (natp j) (<= j total))
    (equal
     (gfield::field-nat-mul
      total
      (gfield::field-mul (poly-coefficient j f)
                         (poly-coefficient (- total j) g)))
     (gfield::field-add
      (gfield::field-nat-mul
       j (gfield::field-mul (poly-coefficient j f)
                            (poly-coefficient (- total j) g)))
      (gfield::field-nat-mul
       (- total j)
       (gfield::field-mul (poly-coefficient j f)
                          (poly-coefficient (- total j) g))))))
   :hints (("Goal" :use product-rule-pointwise-split))))

(local
 (defthm product-rule-exact-reassociation-rewrite
   (equal (gfield::field-add
           (gfield::field-add a b)
           (gfield::field-add c d))
          (gfield::field-add
           (gfield::field-add a c)
           (gfield::field-add b d)))
   :hints (("Goal" :use product-rule-exact-reassociation))))

(local
 (defthm field-nat-mul-over-convolution-aux
   (implies (and (natp total) (natp count) (<= count total))
            (equal
             (gfield::field-nat-mul
              total (poly-convolution-sum-aux count total f g))
             (gfield::field-add
              (product-rule-left-weighted-sum total count f g)
              (product-rule-right-weighted-sum total count f g))))
   :hints (("Goal"
            :induct (poly-convolution-sum-aux count total f g)
            :in-theory
            (e/d (poly-convolution-sum-aux
                  product-rule-left-weighted-sum
                  product-rule-right-weighted-sum
                  product-rule-pointwise-split-rewrite
                  product-rule-exact-reassociation-rewrite)
                 (gfield::field-nat-mul-of-mul-left
                  gfield::field-nat-mul
                  gfield::field-nat-mul-of-mul-right
                  gfield::field-nat-mul-successor
                  gfield::field-nat-mul-successor-total
                  gfield::field-mul-commutative)))
           ("Subgoal *1/2"
            :use ((:instance gfield::field-nat-mul-of-add
                             (n total)
                             (x (poly-convolution-sum-aux
                                 (1- count) total f g))
                             (y (gfield::field-mul
                                 (poly-coefficient count f)
                                 (poly-coefficient (- total count) g))))
                  (:instance product-rule-pointwise-split (j count))
                  (:instance product-rule-exact-reassociation
                             (a (product-rule-left-weighted-sum
                                 total (1- count) f g))
                             (b (product-rule-right-weighted-sum
                                 total (1- count) f g))
                             (c (gfield::field-nat-mul
                                 count
                                 (gfield::field-mul
                                  (poly-coefficient count f)
                                  (poly-coefficient (- total count) g))))
                             (d (gfield::field-nat-mul
                                 (- total count)
                                 (gfield::field-mul
                                  (poly-coefficient count f)
                                  (poly-coefficient (- total count) g))))))
            :in-theory
            (e/d (product-rule-pointwise-split-rewrite
                  product-rule-exact-reassociation-rewrite)
                 (gfield::field-nat-mul-of-add
                  gfield::field-nat-mul
                  gfield::field-nat-mul-of-mul-left
                  gfield::field-nat-mul-of-mul-right
                  gfield::field-nat-mul-successor
                  gfield::field-nat-mul-successor-total
                  gfield::field-mul-commutative))))))

(local
 (defthm field-nat-mul-over-convolution
   (equal
    (gfield::field-nat-mul total (poly-convolution-sum total f g))
    (gfield::field-add
     (product-rule-left-weighted-sum (nfix total) (nfix total) f g)
     (product-rule-right-weighted-sum (nfix total) (nfix total) f g)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance field-nat-mul-over-convolution-aux
                                    (total (nfix total))
                                    (count (nfix total))))
            :in-theory (enable poly-convolution-sum)))))

(local
 (defthm derivative-first-convolution-alignment-aux
   (implies (and (natp total) (natp count) (<= count total))
            (equal
             (poly-convolution-sum-aux count total (poly-derivative f) g)
             (product-rule-left-weighted-sum
              (+ 1 total) (+ 1 count) f g)))
   :hints (("Goal"
            :induct (poly-convolution-sum-aux count total
                                               (poly-derivative f) g)
            :in-theory
            (e/d (poly-convolution-sum-aux
                  product-rule-left-weighted-sum
                  poly-coefficient-of-poly-derivative)
                 (poly-derivative raw-derivative-aux normalize
                  trim-trailing-zeros fix-coefficients
                  gfield::field-nat-mul
                  gfield::field-nat-mul-successor
                  gfield::field-nat-mul-successor-total
                  gfield::field-nat-mul-of-mul-right
                  gfield::field-mul-commutative))))))

(local
 (defthm derivative-first-convolution-alignment
   (equal
    (poly-convolution-sum n (poly-derivative f) g)
    (product-rule-left-weighted-sum
     (+ 1 (nfix n)) (+ 1 (nfix n)) f g))
   :rule-classes nil
   :hints (("Goal" :use ((:instance derivative-first-convolution-alignment-aux
                                    (total (nfix n)) (count (nfix n))))
            :in-theory (enable poly-convolution-sum)))))

(local
 (defthm derivative-second-convolution-alignment-aux
   (implies (and (natp total) (natp count) (<= count total))
            (equal
             (poly-convolution-sum-aux count total f (poly-derivative g))
             (product-rule-right-weighted-sum (+ 1 total) count f g)))
   :hints (("Goal"
            :induct (poly-convolution-sum-aux count total
                                               f (poly-derivative g))
            :in-theory
            (e/d (poly-convolution-sum-aux
                  product-rule-right-weighted-sum
                  poly-coefficient-of-poly-derivative)
                 (poly-derivative raw-derivative-aux normalize
                  trim-trailing-zeros fix-coefficients
                  gfield::field-nat-mul
                  gfield::field-nat-mul-successor
                  gfield::field-nat-mul-successor-total
                  gfield::field-nat-mul-of-mul-left
                  gfield::field-mul-commutative))))))

(local
 (defthm right-weighted-sum-zero-endpoint-extension
   (equal (product-rule-right-weighted-sum
           (+ 1 (nfix n)) (+ 1 (nfix n)) f g)
          (product-rule-right-weighted-sum
           (+ 1 (nfix n)) (nfix n) f g))
   :hints (("Goal" :in-theory (enable product-rule-right-weighted-sum)))))

(local
 (defthm derivative-second-convolution-alignment
   (equal
    (poly-convolution-sum n f (poly-derivative g))
    (product-rule-right-weighted-sum
     (+ 1 (nfix n)) (+ 1 (nfix n)) f g))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance derivative-second-convolution-alignment-aux
                             (total (nfix n)) (count (nfix n)))
                  right-weighted-sum-zero-endpoint-extension)
            :in-theory (enable poly-convolution-sum)))))

(local
 (defthm derivative-product-coefficient-convolution-identity
   (equal
    (gfield::field-nat-mul
     (+ 1 (nfix n))
     (poly-convolution-sum (+ 1 (nfix n)) f g))
    (gfield::field-add
     (poly-convolution-sum n (poly-derivative f) g)
     (poly-convolution-sum n f (poly-derivative g))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance field-nat-mul-over-convolution
                             (total (+ 1 (nfix n))))
                  derivative-first-convolution-alignment
                  derivative-second-convolution-alignment)
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(nfix natp))))))

(defthm poly-coefficient-of-derivative-product-rule-sides
  (equal
   (poly-coefficient n (poly-derivative (poly-mul f g)))
   (poly-coefficient
    n (poly-add (poly-mul (poly-derivative f) g)
                (poly-mul f (poly-derivative g)))))
  :rule-classes nil
  :hints (("Goal"
           :use derivative-product-coefficient-convolution-identity
           :in-theory '(poly-coefficient-of-poly-derivative
                        poly-coefficient-of-poly-mul
                        poly-coefficient-of-poly-add))))

(local
 (defun bounded-coefficient-agreement-p (count first second)
   (declare (xargs :measure (nfix count)))
   (if (zp (nfix count))
       t
     (and (equal (poly-coefficient (1- (nfix count)) first)
                 (poly-coefficient (1- (nfix count)) second))
          (bounded-coefficient-agreement-p
           (1- (nfix count)) first second)))))

(local
 (defthm product-rule-coefficient-equality-rewrite
   (equal
    (poly-coefficient n (poly-derivative (poly-mul f g)))
    (poly-coefficient
     n (poly-add (poly-mul (poly-derivative f) g)
                 (poly-mul f (poly-derivative g)))))
   :hints (("Goal"
            :use poly-coefficient-of-derivative-product-rule-sides))))

(local
 (defthm bounded-product-rule-coefficients-agree
   (bounded-coefficient-agreement-p
    count
    (poly-derivative (poly-mul f g))
    (poly-add (poly-mul (poly-derivative f) g)
              (poly-mul f (poly-derivative g))))
   :hints (("Goal" :induct (bounded-coefficient-agreement-p count nil nil)
            :in-theory
            (e/d (bounded-coefficient-agreement-p
                  product-rule-coefficient-equality-rewrite)
                 (poly-derivative poly-mul poly-add raw-derivative-aux
                  raw-mul raw-add normalize trim-trailing-zeros
                  fix-coefficients canonical-polynomial-p))))))

(local
 (defthm coefficient-zero-equal-from-bounded-agreement
   (implies (and (posp count)
                 (bounded-coefficient-agreement-p count first second))
            (equal (poly-coefficient 0 first)
                   (poly-coefficient 0 second)))
   :hints (("Goal" :induct (bounded-coefficient-agreement-p
                              count first second)
            :in-theory (enable bounded-coefficient-agreement-p)))))

(local
 (defthm bounded-agreement-of-tails
   (implies
    (bounded-coefficient-agreement-p (+ 1 (nfix count)) first second)
    (bounded-coefficient-agreement-p
     count
     (if (consp first) (cdr first) nil)
     (if (consp second) (cdr second) nil)))
   :hints (("Goal" :induct (bounded-coefficient-agreement-p
                              count first second)
            :in-theory (enable bounded-coefficient-agreement-p
                               poly-coefficient-of-successor)))))

(local
 (defthm same-coefficients-from-bounded-agreement
   (implies (bounded-coefficient-agreement-p count first second)
            (same-polynomial-coefficients-p count first second))
   :hints (("Goal" :induct (same-polynomial-coefficients-p
                              count first second)
            :in-theory (enable same-polynomial-coefficients-p
                               coefficient-zero-equal-from-bounded-agreement
                               bounded-agreement-of-tails)))))

(local
 (defthm same-coefficients-of-product-rule-sides
   (same-polynomial-coefficients-p
    count
    (poly-derivative (poly-mul f g))
    (poly-add (poly-mul (poly-derivative f) g)
              (poly-mul f (poly-derivative g))))
   :rule-classes nil
   :hints (("Goal"
            :use (bounded-product-rule-coefficients-agree
                  (:instance same-coefficients-from-bounded-agreement
                             (first (poly-derivative (poly-mul f g)))
                             (second
                              (poly-add
                               (poly-mul (poly-derivative f) g)
                               (poly-mul f (poly-derivative g))))))))))

(defthm poly-derivative-of-poly-mul
  (equal
   (poly-derivative (poly-mul f g))
   (poly-add (poly-mul (poly-derivative f) g)
             (poly-mul f (poly-derivative g))))
  :hints
  (("Goal"
    :use ((:instance canonical-polynomial-extensionality
                     (first (poly-derivative (poly-mul f g)))
                     (second
                      (poly-add (poly-mul (poly-derivative f) g)
                                (poly-mul f (poly-derivative g)))))
          (:instance same-coefficients-of-product-rule-sides
                     (count
                      (max (len (poly-derivative (poly-mul f g)))
                           (len
                            (poly-add
                             (poly-mul (poly-derivative f) g)
                             (poly-mul f (poly-derivative g))))))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(canonical-polynomial-p-of-poly-derivative
       canonical-polynomial-p-of-poly-mul
       canonical-polynomial-p-of-poly-add)))))

(verify-guards raw-derivative-aux)
(verify-guards poly-derivative)
