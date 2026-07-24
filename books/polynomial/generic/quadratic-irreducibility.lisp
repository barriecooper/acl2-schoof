(in-package "GPOLY")
(include-book "irreducibility")

; This is a logical field quantifier, not an executable root search.
(defun-sk poly-has-root-p (poly)
  (exists (root)
          (and (gfield::field-element-p root)
               (equal (eval poly root) (gfield::field-zero)))))

(defthm poly-has-root-p-of-normalize
  (equal (poly-has-root-p (normalize poly))
         (poly-has-root-p poly))
  :hints (("Goal"
           :use ((:instance poly-has-root-p-suff
                            (poly (normalize poly))
                            (root (poly-has-root-p-witness poly)))
                 (:instance poly-has-root-p-suff
                            (poly poly)
                            (root (poly-has-root-p-witness
                                   (normalize poly)))))
           :in-theory (disable poly-has-root-p-suff))))

(local
 (defthm true-list-of-length-two
   (implies (and (true-listp x) (equal (len x) 2))
            (equal x (list (car x) (cadr x))))
   :rule-classes nil))

(defthm normalized-degree-one-has-root
  (implies (and (canonical-polynomial-p poly)
                (equal (poly-degree poly) 1))
           (poly-has-root-p poly))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-has-root-p-suff
                            (root (gfield::field-div
                                   (gfield::field-neg (car poly))
                                   (cadr poly))))
                 (:instance poly-degree-when-canonical-nonzero (p poly))
                 (:instance true-list-of-length-two (x poly)))
           :cases ((poly-has-root-p poly))
           :in-theory (e/d (eval gfield::field-div canonical-polynomial-p)
                           (poly-has-root-p poly-has-root-p-suff)))))

(defthm normalized-nonunit-factor-of-nonzero-product-has-positive-degree
  (implies (and (canonical-polynomial-p factor)
                (consp (poly-mul factor other))
                (not (poly-unit-p factor)))
           (< 0 (poly-degree factor)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable poly-unit-p))))

(defthm normalized-nonunit-factors-of-degree-two-product-have-degree-one
  (implies (and (canonical-polynomial-p left)
                (canonical-polynomial-p right)
                (consp left)
                (consp right)
                (not (poly-unit-p left))
                (not (poly-unit-p right))
                (equal (poly-degree (poly-mul left right)) 2))
           (and (equal (poly-degree left) 1)
                (equal (poly-degree right) 1)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-degree-of-poly-mul
                            (f left) (g right))
                 (:instance
                  normalized-nonunit-factor-of-nonzero-product-has-positive-degree
                  (factor left) (other right))
                 (:instance
                 normalized-nonunit-factor-of-nonzero-product-has-positive-degree
                  (factor right) (other left))
                 (:instance poly-mul-commutative (x right) (y left)))
           :in-theory (disable poly-degree poly-mul poly-unit-p
                               ))))

(defthm poly-has-root-p-of-poly-mul-left
  (implies (poly-has-root-p left)
           (poly-has-root-p (poly-mul left right)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-has-root-p-suff
                            (poly (poly-mul left right))
                            (root (poly-has-root-p-witness left)))
                 (:instance poly-has-root-p (poly left)))
           :cases ((poly-has-root-p (poly-mul left right)))
           :in-theory (e/d (eval-of-poly-mul)
                           (poly-has-root-p poly-has-root-p-suff)))))

(defthm normalized-degree-two-nonunit-product-has-root
  (implies (and (canonical-polynomial-p left)
                (canonical-polynomial-p right)
                (consp left) (consp right)
                (not (poly-unit-p left))
                (not (poly-unit-p right))
                (equal (poly-degree (poly-mul left right)) 2))
           (poly-has-root-p (poly-mul left right)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  normalized-nonunit-factors-of-degree-two-product-have-degree-one)
                 (:instance normalized-degree-one-has-root (poly left))
                 (:instance poly-has-root-p-of-poly-mul-left)))))

(defthm degree-two-nonunit-factorization-has-root
  (implies (and (canonical-polynomial-p poly)
                (equal (poly-degree poly) 2)
                (equal (poly-mul left right) poly)
                (not (poly-unit-p left))
                (not (poly-unit-p right)))
           (poly-has-root-p poly))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance normalized-degree-two-nonunit-product-has-root
                            (left (normalize left))
                            (right (normalize right)))))))

(defthm normalized-reducible-quadratic-has-root
  (implies (and (canonical-polynomial-p poly)
                (equal (poly-degree poly) 2)
                (poly-reducible-p poly))
           (poly-has-root-p poly))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-reducible-p (poly poly))
                 (:instance degree-two-nonunit-factorization-has-root
                            (left (mv-nth 0
                                     (poly-reducible-p-witness poly)))
                            (right (mv-nth 1
                                      (poly-reducible-p-witness poly)))))
           :in-theory (disable poly-reducible-p))))

(defthm root-free-quadratic-is-irreducible
  (implies (and (equal (poly-degree poly) 2)
                (not (poly-has-root-p poly)))
           (poly-irreducible-p poly))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance normalized-reducible-quadratic-has-root
                            (poly (normalize poly)))
                 (:instance poly-degree-of-normalize (p poly))
                 (:instance poly-has-root-p-of-normalize)
                 (:instance poly-reducible-p-of-normalize))
           :in-theory (e/d (poly-irreducible-p)
                           (poly-reducible-p poly-has-root-p
                            poly-degree-of-normalize
                            poly-has-root-p-of-normalize
                            poly-reducible-p-of-normalize)))))

(defthm root-free-normalized-quadratic-is-irreducible
  (implies (and (equal (poly-degree (normalize poly)) 2)
                (not (poly-has-root-p (normalize poly))))
           (poly-irreducible-p (normalize poly)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance root-free-quadratic-is-irreducible
                                    (poly (normalize poly)))))))
