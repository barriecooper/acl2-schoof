(in-package "HS")
(include-book "base")
(include-book "kestrel/arithmetic-light/mod" :dir :system)
(include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)

(defun poly-eval (poly x p)
  (if (endp poly) 0
    (pfield::add (car poly)
                 (pfield::mul x (poly-eval (cdr poly) x p) p) p)))

(defthm normalize-preserves-eval
  (equal (poly-eval (poly-normalize poly) x p)
         (poly-eval poly x p)))

(defthm poly-eval-is-field-element
  (implies (and (field-polynomial-p poly p)
                (pfield::fep x p)
                (posp p))
           (pfield::fep (poly-eval poly x p) p)))

(defthm poly-eval-of-add-raw
  (implies (and (field-polynomial-p left p)
                (field-polynomial-p right p)
                (pfield::fep x p)
                (posp p))
           (equal (poly-eval (poly-add-raw left right p) x p)
                  (pfield::add (poly-eval left x p)
                               (poly-eval right x p) p))))

(defthm poly-eval-of-add
  (implies (and (field-polynomial-p left p)
                (field-polynomial-p right p)
                (pfield::fep x p)
                (posp p))
           (equal (poly-eval (poly-add left right p) x p)
                  (pfield::add (poly-eval left x p)
                               (poly-eval right x p) p))))

(defthm poly-eval-of-poly-scale-raw
  (implies (and (field-polynomial-p poly p)
                (pfield::fep a p)
                (pfield::fep x p)
                (posp p))
           (equal (poly-eval (poly-scale-raw a poly p) x p)
                  (pfield::mul a (poly-eval poly x p) p)))
  :hints (("Goal" :in-theory (enable pfield::mul-of-add-arg2
                                      pfield::mul-associative
                                      pfield::mul-commutative))))

(defthm poly-eval-of-zero-cons
  (implies (and (field-polynomial-p poly p)
                (pfield::fep x p)
                (posp p))
           (equal (poly-eval (cons 0 poly) x p)
                  (pfield::mul x (poly-eval poly x p) p))))

(defthm poly-eval-of-mul-raw
  (implies (and (field-polynomial-p left p)
                (field-polynomial-p right p)
                (pfield::fep x p)
                (posp p))
           (equal (poly-eval (poly-mul-raw left right p) x p)
                  (pfield::mul (poly-eval left x p)
                               (poly-eval right x p) p)))
  :hints (("Goal" :induct (field-polynomial-p left p)
                    :in-theory (enable pfield::mul-of-add-arg1
                                       pfield::mul-of-add-arg2
                                       pfield::mul-associative
                                       pfield::mul-commutative))))

(defthm poly-eval-of-mul
  (implies (and (field-polynomial-p left p)
                (field-polynomial-p right p)
                (pfield::fep x p)
                (posp p))
           (equal (poly-eval (poly-mul left right p) x p)
                  (pfield::mul (poly-eval left x p)
                               (poly-eval right x p) p))))
