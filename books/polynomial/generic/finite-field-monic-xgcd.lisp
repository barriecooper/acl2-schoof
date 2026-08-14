(in-package "GPOLY")

(include-book "finite-field-xgcd")
(include-book "finite-field-monic-euclidean-gcd")

; Transparent post-processing of the certified raw XGCD triple.  In
; particular, no second Euclidean computation is hidden in this wrapper.
(defun finite-field-poly-monic-extended-euclidean-gcd (first second)
  (declare (xargs :guard t))
  (mv-let (gcd s coefficient-t)
    (finite-field-poly-extended-euclidean-gcd first second)
    (let ((scale
           (gfield::finite-field-inv
            (finite-field-poly-leading-coefficient gcd))))
      (mv (finite-field-poly-monic-normalize gcd)
          (finite-field-poly-scale scale s)
          (finite-field-poly-scale scale coefficient-t)))))

(verify-guards finite-field-poly-monic-extended-euclidean-gcd)

(defthm finite-field-poly-monic-extended-euclidean-gcd-is-scaled-xgcd
  (equal
   (finite-field-poly-monic-extended-euclidean-gcd first second)
   (mv-let (gcd s coefficient-t)
     (finite-field-poly-extended-euclidean-gcd first second)
     (let ((scale
            (gfield::finite-field-inv
             (finite-field-poly-leading-coefficient gcd))))
       (mv (finite-field-poly-monic-normalize gcd)
           (finite-field-poly-scale scale s)
           (finite-field-poly-scale scale coefficient-t)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory
           (enable finite-field-poly-monic-extended-euclidean-gcd))))

(defthm finite-field-poly-monic-extended-euclidean-gcd-gcd-is-monic-euclidean-gcd
  (equal
   (mv-nth 0
           (finite-field-poly-monic-extended-euclidean-gcd first second))
   (finite-field-poly-monic-euclidean-gcd first second))
  :hints
  (("Goal"
    :use
    ((:instance
      finite-field-poly-monic-extended-euclidean-gcd-is-scaled-xgcd)
     (:instance
      finite-field-poly-extended-euclidean-gcd-gcd-is-euclidean-gcd)
     (:instance finite-field-poly-monic-euclidean-gcd-is-monic-normalize))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-monic-extended-euclidean-gcd-gcd-canonical
  (finite-field-canonical-polynomial-p
   (mv-nth 0
           (finite-field-poly-monic-extended-euclidean-gcd first second)))
  :hints
  (("Goal"
    :use
    ((:instance
      finite-field-poly-monic-extended-euclidean-gcd-gcd-is-monic-euclidean-gcd)
     (:instance
      finite-field-canonical-polynomial-p-of-poly-monic-euclidean-gcd))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-monic-extended-euclidean-gcd-first-coefficient-canonical
  (finite-field-canonical-polynomial-p
   (mv-nth 1
           (finite-field-poly-monic-extended-euclidean-gcd first second)))
  :hints
  (("Goal"
    :use
    ((:instance
      finite-field-poly-monic-extended-euclidean-gcd-is-scaled-xgcd)
     (:instance finite-field-canonical-polynomial-p-of-poly-scale
                (a (gfield::finite-field-inv
                    (finite-field-poly-leading-coefficient
                     (mv-nth 0
                             (finite-field-poly-extended-euclidean-gcd
                              first second)))))
                (x (mv-nth 1
                           (finite-field-poly-extended-euclidean-gcd
                            first second)))))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-monic-extended-euclidean-gcd-second-coefficient-canonical
  (finite-field-canonical-polynomial-p
   (mv-nth 2
           (finite-field-poly-monic-extended-euclidean-gcd first second)))
  :hints
  (("Goal"
    :use
    ((:instance
      finite-field-poly-monic-extended-euclidean-gcd-is-scaled-xgcd)
     (:instance finite-field-canonical-polynomial-p-of-poly-scale
                (a (gfield::finite-field-inv
                    (finite-field-poly-leading-coefficient
                     (mv-nth 0
                             (finite-field-poly-extended-euclidean-gcd
                              first second)))))
                (x (mv-nth 2
                           (finite-field-poly-extended-euclidean-gcd
                            first second)))))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-normalize-of-monic-extended-euclidean-gcd-gcd
  (equal
   (finite-field-poly-normalize
    (mv-nth 0
            (finite-field-poly-monic-extended-euclidean-gcd first second)))
   (mv-nth 0
           (finite-field-poly-monic-extended-euclidean-gcd first second)))
  :hints (("Goal"
           :use
           ((:instance finite-field-poly-normalize-when-canonical
                       (xs (mv-nth
                            0
                            (finite-field-poly-monic-extended-euclidean-gcd
                             first second))))
            (:instance
             finite-field-poly-monic-extended-euclidean-gcd-gcd-canonical))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-normalize-of-monic-extended-euclidean-gcd-first-coefficient
  (equal
   (finite-field-poly-normalize
    (mv-nth 1
            (finite-field-poly-monic-extended-euclidean-gcd first second)))
   (mv-nth 1
           (finite-field-poly-monic-extended-euclidean-gcd first second)))
  :hints (("Goal"
           :use
           ((:instance finite-field-poly-normalize-when-canonical
                       (xs (mv-nth
                            1
                            (finite-field-poly-monic-extended-euclidean-gcd
                             first second))))
            (:instance
             finite-field-poly-monic-extended-euclidean-gcd-first-coefficient-canonical))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-normalize-of-monic-extended-euclidean-gcd-second-coefficient
  (equal
   (finite-field-poly-normalize
    (mv-nth 2
            (finite-field-poly-monic-extended-euclidean-gcd first second)))
   (mv-nth 2
           (finite-field-poly-monic-extended-euclidean-gcd first second)))
  :hints (("Goal"
           :use
           ((:instance finite-field-poly-normalize-when-canonical
                       (xs (mv-nth
                            2
                            (finite-field-poly-monic-extended-euclidean-gcd
                             first second))))
            (:instance
             finite-field-poly-monic-extended-euclidean-gcd-second-coefficient-canonical))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-consp-of-poly-monic-extended-euclidean-gcd-gcd
  (equal
   (consp
    (mv-nth 0
            (finite-field-poly-monic-extended-euclidean-gcd first second)))
   (consp (finite-field-poly-monic-euclidean-gcd first second)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      finite-field-poly-monic-extended-euclidean-gcd-gcd-is-monic-euclidean-gcd))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-leading-coefficient-of-poly-monic-extended-euclidean-gcd
  (equal
   (finite-field-poly-leading-coefficient
    (mv-nth 0
            (finite-field-poly-monic-extended-euclidean-gcd first second)))
   (if (consp (finite-field-poly-euclidean-gcd first second))
       (gfield::finite-field-one)
     (gfield::finite-field-zero)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      finite-field-poly-monic-extended-euclidean-gcd-gcd-is-monic-euclidean-gcd)
     (:instance
      finite-field-poly-leading-coefficient-of-poly-monic-euclidean-gcd))
    :in-theory (theory 'minimal-theory))))

(local
 (defun finite-field-poly-const-for-monic-xgcd (a)
   (if (equal (gfield::finite-field-fix a)
              (gfield::finite-field-zero))
       nil
     (list (gfield::finite-field-fix a)))))

; Confine the finite-field context and renamed-definition theories to the
; small functional-instance audit below.
(set-default-hints
 '((and stable-under-simplificationp
        (list :use (theory 'gfield::finite-field-context-instance-theory)
              :in-theory
              (list 'quote
                    (union-theories
                     '(finite-field-poly-const-for-monic-xgcd)
                     (union-theories
                      (theory 'finite-field-poly-definition-theory)
                      (theory 'minimal-theory))))))))

(local
 (defthm finite-field-poly-mul-const-left-for-monic-xgcd
   (equal (finite-field-poly-mul
           (finite-field-poly-const-for-monic-xgcd scalar) polynomial)
          (finite-field-poly-scale scalar polynomial))
   :hints (("Goal"
            :in-theory (theory 'minimal-theory)
            :by (:functional-instance
                 poly-mul-const-left
                 (gfield::field-element-p gfield::finite-field-element-p)
                 (gfield::field-fix gfield::finite-field-fix)
                 (gfield::field-zero gfield::finite-field-zero)
                 (gfield::field-one gfield::finite-field-one)
                 (gfield::field-add gfield::finite-field-add)
                 (gfield::field-mul gfield::finite-field-mul)
                 (gfield::field-neg gfield::finite-field-neg)
                 (gfield::field-inv gfield::finite-field-inv)
                 (fix-coefficients finite-field-poly-fix-coefficients)
                 (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
                 (normalize finite-field-poly-normalize)
                 (raw-add finite-field-poly-raw-add)
                 (poly-add finite-field-poly-add)
                 (raw-scale finite-field-poly-raw-scale)
                 (poly-scale finite-field-poly-scale)
                 (raw-mul finite-field-poly-raw-mul)
                 (poly-mul finite-field-poly-mul)
                 (const finite-field-poly-const-for-monic-xgcd))))))

(local
 (defthm finite-field-poly-mul-of-poly-scale-left-for-monic-xgcd
   (equal
    (finite-field-poly-mul
     (finite-field-poly-scale scalar coefficient) input)
    (finite-field-poly-scale
     scalar (finite-field-poly-mul coefficient input)))
   :hints
   (("Goal"
     :use
     ((:instance finite-field-poly-mul-associative-for-reduction
                 (x (finite-field-poly-const-for-monic-xgcd scalar))
                 (y coefficient) (z input))
      (:instance finite-field-poly-mul-const-left-for-monic-xgcd
                 (polynomial coefficient))
      (:instance finite-field-poly-mul-const-left-for-monic-xgcd
                 (polynomial (finite-field-poly-mul coefficient input))))
     :in-theory (disable finite-field-poly-mul finite-field-poly-scale)))))

(local
 (defthm finite-field-poly-scale-of-poly-add-for-monic-xgcd
   (equal
    (finite-field-poly-scale scalar
                             (finite-field-poly-add x y))
    (finite-field-poly-add (finite-field-poly-scale scalar x)
                           (finite-field-poly-scale scalar y)))
   :hints
   (("Goal"
     :in-theory (theory 'minimal-theory)
     :by (:functional-instance
          poly-scale-of-poly-add
          (gfield::field-element-p gfield::finite-field-element-p)
          (gfield::field-fix gfield::finite-field-fix)
          (gfield::field-zero gfield::finite-field-zero)
          (gfield::field-one gfield::finite-field-one)
          (gfield::field-add gfield::finite-field-add)
          (gfield::field-mul gfield::finite-field-mul)
          (gfield::field-neg gfield::finite-field-neg)
          (gfield::field-inv gfield::finite-field-inv)
          (fix-coefficients finite-field-poly-fix-coefficients)
          (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
          (normalize finite-field-poly-normalize)
          (raw-add finite-field-poly-raw-add)
          (poly-add finite-field-poly-add)
          (raw-scale finite-field-poly-raw-scale)
          (poly-scale finite-field-poly-scale))))))

(local
 (defthm finite-field-poly-scale-by-zero-for-monic-xgcd
   (equal (finite-field-poly-scale
           (gfield::finite-field-zero) polynomial)
          nil)
   :hints (("Goal"
            :in-theory (theory 'minimal-theory)
            :by (:functional-instance
                 poly-scale-by-zero
                 (gfield::field-element-p gfield::finite-field-element-p)
                 (gfield::field-fix gfield::finite-field-fix)
                 (gfield::field-zero gfield::finite-field-zero)
                 (gfield::field-one gfield::finite-field-one)
                 (gfield::field-add gfield::finite-field-add)
                 (gfield::field-mul gfield::finite-field-mul)
                 (gfield::field-neg gfield::finite-field-neg)
                 (gfield::field-inv gfield::finite-field-inv)
                 (fix-coefficients finite-field-poly-fix-coefficients)
                 (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
                 (normalize finite-field-poly-normalize)
                 (raw-scale finite-field-poly-raw-scale)
                 (poly-scale finite-field-poly-scale))))))

(set-default-hints nil)

(defthm finite-field-poly-monic-extended-euclidean-gcd-bezout
  (equal
   (finite-field-poly-add
    (finite-field-poly-mul
     (mv-nth 1
             (finite-field-poly-monic-extended-euclidean-gcd first second))
     first)
    (finite-field-poly-mul
     (mv-nth 2
             (finite-field-poly-monic-extended-euclidean-gcd first second))
     second))
   (finite-field-poly-monic-euclidean-gcd first second))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      finite-field-poly-monic-extended-euclidean-gcd-is-scaled-xgcd)
     (:instance finite-field-poly-extended-euclidean-gcd-bezout)
     (:instance finite-field-poly-scale-of-poly-add-for-monic-xgcd
                (scalar
                 (gfield::finite-field-inv
                  (finite-field-poly-leading-coefficient
                   (mv-nth 0
                           (finite-field-poly-extended-euclidean-gcd
                            first second)))))
                (x (finite-field-poly-mul
                    (mv-nth 1
                            (finite-field-poly-extended-euclidean-gcd
                             first second))
                    first))
                (y (finite-field-poly-mul
                    (mv-nth 2
                            (finite-field-poly-extended-euclidean-gcd
                             first second))
                    second)))
     (:instance finite-field-poly-monic-euclidean-gcd-is-monic-normalize)
     (:instance finite-field-poly-scale-by-zero-for-monic-xgcd))
    :in-theory
    (e/d (finite-field-poly-monic-normalize)
         (finite-field-poly-monic-extended-euclidean-gcd
          finite-field-poly-extended-euclidean-gcd
          finite-field-poly-add finite-field-poly-mul
          finite-field-poly-scale finite-field-poly-leading-coefficient
          finite-field-poly-mul-commutative-for-reduction)))))

(defthm finite-field-poly-monic-extended-euclidean-gcd-bezout-when-one
  (implies
   (equal (finite-field-poly-monic-euclidean-gcd first second)
          (list (gfield::finite-field-one)))
   (equal
    (finite-field-poly-add
     (finite-field-poly-mul
      (mv-nth 1
              (finite-field-poly-monic-extended-euclidean-gcd first second))
      first)
     (finite-field-poly-mul
      (mv-nth 2
              (finite-field-poly-monic-extended-euclidean-gcd first second))
      second))
    (list (gfield::finite-field-one))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance finite-field-poly-monic-extended-euclidean-gcd-bezout))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-monic-extended-euclidean-gcd-specification
  (and
   (equal
    (mv-nth 0
            (finite-field-poly-monic-extended-euclidean-gcd first second))
    (finite-field-poly-monic-euclidean-gcd first second))
   (equal
    (finite-field-poly-add
     (finite-field-poly-mul
      (mv-nth 1
              (finite-field-poly-monic-extended-euclidean-gcd first second))
      first)
     (finite-field-poly-mul
      (mv-nth 2
              (finite-field-poly-monic-extended-euclidean-gcd first second))
      second))
    (finite-field-poly-monic-euclidean-gcd first second))
   (finite-field-canonical-polynomial-p
    (mv-nth 0
            (finite-field-poly-monic-extended-euclidean-gcd first second)))
   (finite-field-canonical-polynomial-p
    (mv-nth 1
            (finite-field-poly-monic-extended-euclidean-gcd first second)))
   (finite-field-canonical-polynomial-p
    (mv-nth 2
            (finite-field-poly-monic-extended-euclidean-gcd first second)))
   (equal
    (finite-field-poly-leading-coefficient
     (mv-nth 0
             (finite-field-poly-monic-extended-euclidean-gcd first second)))
    (if (consp (finite-field-poly-euclidean-gcd first second))
        (gfield::finite-field-one)
      (gfield::finite-field-zero))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      finite-field-poly-monic-extended-euclidean-gcd-gcd-is-monic-euclidean-gcd)
     (:instance finite-field-poly-monic-extended-euclidean-gcd-bezout)
     (:instance
      finite-field-poly-monic-extended-euclidean-gcd-gcd-canonical)
     (:instance
      finite-field-poly-monic-extended-euclidean-gcd-first-coefficient-canonical)
     (:instance
      finite-field-poly-monic-extended-euclidean-gcd-second-coefficient-canonical)
     (:instance
      finite-field-poly-leading-coefficient-of-poly-monic-extended-euclidean-gcd))
    :in-theory (theory 'minimal-theory))))
