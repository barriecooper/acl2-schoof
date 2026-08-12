(in-package "GPOLY")

(include-book "../polynomial/generic/reduced-ring")

; Elements of (F[x]/modulus)[y]/(y^2 - (x^3+a*x+b)) are represented by
; the transparent pair (u . v), denoting u + y*v.  Every public constructor
; reduces both components, so atoms deterministically fix to (nil . nil).
(defun quotient-coordinate (u v modulus)
  (cons (poly-remainder u modulus)
        (poly-remainder v modulus)))

(defun quotient-coordinate-u (coordinate)
  (if (consp coordinate) (car coordinate) nil))
(defun quotient-coordinate-v (coordinate)
  (if (consp coordinate) (cdr coordinate) nil))

(defun quotient-coordinate-fix (coordinate modulus)
  (quotient-coordinate (quotient-coordinate-u coordinate)
                       (quotient-coordinate-v coordinate)
                       modulus))

(defun quotient-coordinate-p (coordinate modulus)
  (equal (quotient-coordinate-fix coordinate modulus) coordinate))

(defun quotient-coordinate-zero (modulus)
  (quotient-coordinate nil nil modulus))

(defun quotient-coordinate-one (modulus)
  (quotient-coordinate (poly-reduced-one modulus) nil modulus))

(defun quotient-coordinate-embed (polynomial modulus)
  (quotient-coordinate polynomial nil modulus))

(defun quotient-coordinate-x (modulus)
  (quotient-coordinate
   (list (gfield::field-zero) (gfield::field-one)) nil modulus))

(defun quotient-coordinate-y (modulus)
  (quotient-coordinate nil (poly-reduced-one modulus) modulus))

(defun quotient-coordinate-add (left right modulus)
  (let ((left (quotient-coordinate-fix left modulus))
        (right (quotient-coordinate-fix right modulus)))
    (quotient-coordinate
     (poly-reduced-add (quotient-coordinate-u left)
                       (quotient-coordinate-u right) modulus)
     (poly-reduced-add (quotient-coordinate-v left)
                       (quotient-coordinate-v right) modulus)
     modulus)))

(defun quotient-coordinate-neg (coordinate modulus)
  (let ((coordinate (quotient-coordinate-fix coordinate modulus)))
    (quotient-coordinate
     (poly-reduced-neg (quotient-coordinate-u coordinate) modulus)
     (poly-reduced-neg (quotient-coordinate-v coordinate) modulus)
     modulus)))

(defun quotient-coordinate-sub (left right modulus)
  (quotient-coordinate-add left (quotient-coordinate-neg right modulus)
                           modulus))

(defun quotient-coordinate-curve-cubic (a b modulus)
  (poly-remainder
   (list (gfield::field-fix b) (gfield::field-fix a)
         (gfield::field-zero) (gfield::field-one))
   modulus))

(defun quotient-coordinate-mul (left right a b modulus)
  (let* ((left (quotient-coordinate-fix left modulus))
         (right (quotient-coordinate-fix right modulus))
         (u1 (quotient-coordinate-u left))
         (v1 (quotient-coordinate-v left))
         (u2 (quotient-coordinate-u right))
         (v2 (quotient-coordinate-v right))
         (cubic (quotient-coordinate-curve-cubic a b modulus)))
    (quotient-coordinate
     (poly-reduced-add
      (poly-reduced-mul u1 u2 modulus)
      (poly-reduced-mul cubic (poly-reduced-mul v1 v2 modulus) modulus)
      modulus)
     (poly-reduced-add (poly-reduced-mul u1 v2 modulus)
                       (poly-reduced-mul v1 u2 modulus) modulus)
     modulus)))

(defthm quotient-coordinate-u-of-constructor
  (equal (quotient-coordinate-u (quotient-coordinate u v modulus))
         (poly-remainder u modulus)))

(defthm quotient-coordinate-v-of-constructor
  (equal (quotient-coordinate-v (quotient-coordinate u v modulus))
         (poly-remainder v modulus)))

(defthm quotient-coordinate-p-of-fix
  (quotient-coordinate-p (quotient-coordinate-fix coordinate modulus) modulus)
  :hints (("Goal"
           :use ((:instance poly-remainder-idempotent
                            (dividend (car coordinate)))
                 (:instance poly-remainder-idempotent
                            (dividend (cdr coordinate))))
           :in-theory (e/d (quotient-coordinate-p
                            quotient-coordinate-fix quotient-coordinate)
                           (poly-remainder poly-divmod)))))

(defthm quotient-coordinate-p-of-constructor
  (quotient-coordinate-p (quotient-coordinate u v modulus) modulus)
  :hints (("Goal"
           :use ((:instance poly-remainder-idempotent (dividend u))
                 (:instance poly-remainder-idempotent (dividend v)))
           :in-theory (e/d (quotient-coordinate-p quotient-coordinate-fix
                                                  quotient-coordinate)
                           (poly-remainder poly-divmod)))))

(defthm quotient-coordinate-fix-idempotent
  (equal (quotient-coordinate-fix
          (quotient-coordinate-fix coordinate modulus) modulus)
         (quotient-coordinate-fix coordinate modulus))
  :hints (("Goal" :use ((:instance poly-remainder-idempotent
                         (dividend (car coordinate)))
                        (:instance poly-remainder-idempotent
                         (dividend (cdr coordinate))))
           :in-theory (e/d (quotient-coordinate-fix quotient-coordinate)
                           (poly-remainder poly-divmod)))))

(defthm quotient-coordinate-fix-when-p
  (implies (quotient-coordinate-p coordinate modulus)
           (equal (quotient-coordinate-fix coordinate modulus) coordinate))
  :hints (("Goal" :in-theory (enable quotient-coordinate-p))))

(defthm poly-reduced-p-of-quotient-coordinate-u-of-fix
  (poly-reduced-p
   (quotient-coordinate-u (quotient-coordinate-fix coordinate modulus))
   modulus)
  :hints (("Goal" :use ((:instance poly-reduced-p-of-poly-remainder
                          (polynomial (car coordinate))))
           :in-theory (e/d (quotient-coordinate-fix quotient-coordinate)
                           (poly-remainder poly-reduced-p poly-divmod)))))

(defthm poly-reduced-p-of-quotient-coordinate-v-of-fix
  (poly-reduced-p
   (quotient-coordinate-v (quotient-coordinate-fix coordinate modulus))
   modulus)
  :hints (("Goal" :use ((:instance poly-reduced-p-of-poly-remainder
                          (polynomial (cdr coordinate))))
           :in-theory (e/d (quotient-coordinate-fix quotient-coordinate)
                           (poly-remainder poly-reduced-p poly-divmod)))))

(defthm quotient-coordinate-operations-closed
  (and (quotient-coordinate-p (quotient-coordinate-zero modulus) modulus)
       (quotient-coordinate-p (quotient-coordinate-one modulus) modulus)
       (quotient-coordinate-p (quotient-coordinate-embed x modulus) modulus)
       (quotient-coordinate-p (quotient-coordinate-x modulus) modulus)
       (quotient-coordinate-p (quotient-coordinate-y modulus) modulus)
       (quotient-coordinate-p (quotient-coordinate-add x z modulus) modulus)
       (quotient-coordinate-p (quotient-coordinate-neg x modulus) modulus)
       (quotient-coordinate-p (quotient-coordinate-sub x z modulus) modulus)
       (quotient-coordinate-p (quotient-coordinate-mul x z a b modulus)
                              modulus))
  :hints (("Goal" :in-theory (e/d (quotient-coordinate-zero
                                      quotient-coordinate-one
                                      quotient-coordinate-embed
                                      quotient-coordinate-x
                                      quotient-coordinate-y
                                      quotient-coordinate-add
                                      quotient-coordinate-neg
                                      quotient-coordinate-sub
                                      quotient-coordinate-mul
                                      (:rewrite quotient-coordinate-p-of-constructor))
                                    (quotient-coordinate
                                     quotient-coordinate-p
                                     quotient-coordinate-fix
                                     poly-remainder poly-divmod))
           :do-not '(preprocess)
           :do-not-induct t)))

(defthm quotient-coordinate-add-of-fixes
  (equal (quotient-coordinate-add
          (quotient-coordinate-fix left modulus)
          (quotient-coordinate-fix right modulus) modulus)
         (quotient-coordinate-add left right modulus))
  :hints (("Goal" :use ((:instance quotient-coordinate-fix-idempotent
                          (coordinate left))
                        (:instance quotient-coordinate-fix-idempotent
                          (coordinate right)))
           :in-theory (e/d (quotient-coordinate-add)
                           (quotient-coordinate-fix quotient-coordinate
                            poly-remainder poly-divmod)))))

(defthm quotient-coordinate-neg-of-fix
  (equal (quotient-coordinate-neg
          (quotient-coordinate-fix coordinate modulus) modulus)
         (quotient-coordinate-neg coordinate modulus))
  :hints (("Goal" :use ((:instance quotient-coordinate-fix-idempotent))
           :in-theory (e/d (quotient-coordinate-neg)
                           (quotient-coordinate-fix quotient-coordinate
                            poly-remainder poly-divmod)))))

(defthm quotient-coordinate-mul-of-fixes
  (equal (quotient-coordinate-mul
          (quotient-coordinate-fix left modulus)
          (quotient-coordinate-fix right modulus) a b modulus)
         (quotient-coordinate-mul left right a b modulus))
  :hints (("Goal" :use ((:instance quotient-coordinate-fix-idempotent
                          (coordinate left))
                        (:instance quotient-coordinate-fix-idempotent
                          (coordinate right)))
           :in-theory (e/d (quotient-coordinate-mul)
                           (quotient-coordinate-fix quotient-coordinate
                            poly-remainder poly-divmod)))))

(local (in-theory (e/d (quotient-coordinate-add quotient-coordinate-neg
                          quotient-coordinate-sub quotient-coordinate-mul
                          quotient-coordinate-zero quotient-coordinate-one
                          quotient-coordinate-embed quotient-coordinate-y
                          quotient-coordinate-curve-cubic quotient-coordinate
                          quotient-coordinate-fix)
                        (poly-remainder poly-divmod
                         poly-reduced-add poly-reduced-neg poly-reduced-sub
                         poly-reduced-mul poly-reduced-one
                         poly-reduced-add-definition
                         poly-reduced-neg-definition
                         poly-reduced-sub-definition
                         poly-reduced-mul-definition
                         poly-reduced-one-definition))))

(defthm quotient-coordinate-add-zero-left
  (equal (quotient-coordinate-add (quotient-coordinate-zero modulus) x modulus)
         (quotient-coordinate-fix x modulus)))

(defthm quotient-coordinate-add-zero-right
  (equal (quotient-coordinate-add x (quotient-coordinate-zero modulus) modulus)
         (quotient-coordinate-fix x modulus)))

(defthm quotient-coordinate-add-inverse-left
  (equal (quotient-coordinate-add (quotient-coordinate-neg x modulus) x modulus)
         (quotient-coordinate-zero modulus))
  :hints (("Goal" :use ((:instance poly-reduced-add-inverse-left
                          (a (poly-remainder (car x) modulus)))
                        (:instance poly-reduced-add-inverse-left
                          (a (poly-remainder (cdr x) modulus)))))))

(defthm quotient-coordinate-add-inverse-right
  (equal (quotient-coordinate-add x (quotient-coordinate-neg x modulus) modulus)
         (quotient-coordinate-zero modulus))
  :hints (("Goal" :use ((:instance poly-reduced-add-inverse-right
                          (a (poly-remainder (car x) modulus)))
                        (:instance poly-reduced-add-inverse-right
                          (a (poly-remainder (cdr x) modulus)))))))

(defthm quotient-coordinate-add-commutative
  (equal (quotient-coordinate-add x z modulus)
         (quotient-coordinate-add z x modulus)))

(defthm quotient-coordinate-add-associative
  (equal (quotient-coordinate-add (quotient-coordinate-add x z modulus) w modulus)
         (quotient-coordinate-add x (quotient-coordinate-add z w modulus) modulus))
  :hints (("Goal" :use ((:instance poly-reduced-add-associative
                          (a (poly-remainder (car x) modulus))
                          (b (poly-remainder (car z) modulus))
                          (c (poly-remainder (car w) modulus)))
                        (:instance poly-reduced-add-associative
                          (a (poly-remainder (cdr x) modulus))
                          (b (poly-remainder (cdr z) modulus))
                          (c (poly-remainder (cdr w) modulus))))
           :in-theory (disable quotient-coordinate-add-commutative))))

(defthm quotient-coordinate-mul-one-left
  (equal (quotient-coordinate-mul (quotient-coordinate-one modulus) x a b modulus)
         (quotient-coordinate-fix x modulus))
  :hints (("Goal" :use ((:instance poly-reduced-mul-one-left
                          (a (poly-remainder (car x) modulus)))
                        (:instance poly-reduced-mul-one-left
                          (a (poly-remainder (cdr x) modulus)))))))

(defthm quotient-coordinate-mul-one-right
  (equal (quotient-coordinate-mul x (quotient-coordinate-one modulus) a b modulus)
         (quotient-coordinate-fix x modulus))
  :hints (("Goal" :use ((:instance poly-reduced-mul-one-right
                          (a (poly-remainder (car x) modulus)))
                        (:instance poly-reduced-mul-one-right
                          (a (poly-remainder (cdr x) modulus)))
                        (:instance poly-reduced-mul-one-left
                          (a (poly-remainder (car x) modulus)))
                        (:instance poly-reduced-mul-one-left
                          (a (poly-remainder (cdr x) modulus))))
           :in-theory (disable poly-reduced-mul-commutative))))

(defthm quotient-coordinate-mul-commutative
  (equal (quotient-coordinate-mul x z a b modulus)
         (quotient-coordinate-mul z x a b modulus)))

(defthm quotient-coordinate-mul-zero-left
  (equal (quotient-coordinate-mul
          (quotient-coordinate-zero modulus) z a b modulus)
         (quotient-coordinate-zero modulus))
  :hints (("Goal"
           :in-theory (e/d (quotient-coordinate-mul
                            quotient-coordinate-zero)
                           (quotient-coordinate-fix quotient-coordinate
                            poly-remainder poly-divmod)))))

(defthm quotient-coordinate-mul-zero-right
  (equal (quotient-coordinate-mul
          z (quotient-coordinate-zero modulus) a b modulus)
         (quotient-coordinate-zero modulus))
  :hints (("Goal"
           :use ((:instance quotient-coordinate-mul-commutative
                            (x z)
                            (z (quotient-coordinate-zero modulus)))
                 (:instance quotient-coordinate-mul-zero-left
                            (z z)))
           :in-theory (disable quotient-coordinate-mul
                               quotient-coordinate-zero
                               quotient-coordinate-mul-commutative
                               quotient-coordinate-mul-zero-left))))

; The following local lemmas deliberately normalize only the bounded ring
; expressions generated by rank-two multiplication.  Commutativity is used by
; explicit instances instead of as a global rewrite rule.
(local
 (defthm quotient-coordinate-reduced-add-interchange
   (equal
    (poly-reduced-add (poly-reduced-add a b modulus)
                      (poly-reduced-add c d modulus) modulus)
    (poly-reduced-add (poly-reduced-add a c modulus)
                      (poly-reduced-add b d modulus) modulus))
   :hints
   (("Goal"
     :use ((:instance poly-reduced-add-commutative
                      (a b) (b (poly-reduced-add c d modulus)))
           (:instance poly-reduced-add-commutative (a d) (b b)))
     :in-theory (enable poly-reduced-add-associative)))))

(local
 (defthm quotient-coordinate-reduced-scalar-distributive
   (equal
    (poly-reduced-add
     (poly-reduced-mul u1 (poly-reduced-add u2 u3 modulus) modulus)
     (poly-reduced-mul
      cubic
      (poly-reduced-mul v1 (poly-reduced-add v2 v3 modulus) modulus)
      modulus)
     modulus)
    (poly-reduced-add
     (poly-reduced-add
      (poly-reduced-mul u1 u2 modulus)
      (poly-reduced-mul cubic (poly-reduced-mul v1 v2 modulus) modulus)
      modulus)
     (poly-reduced-add
      (poly-reduced-mul u1 u3 modulus)
      (poly-reduced-mul cubic (poly-reduced-mul v1 v3 modulus) modulus)
      modulus)
     modulus))
   :hints
   (("Goal"
     :use ((:instance poly-reduced-mul-left-distributive
                      (a u1) (b u2) (c u3))
           (:instance poly-reduced-mul-left-distributive
                      (a v1) (b v2) (c v3))
           (:instance poly-reduced-mul-left-distributive
                      (a cubic)
                      (b (poly-reduced-mul v1 v2 modulus))
                      (c (poly-reduced-mul v1 v3 modulus)))
           (:instance quotient-coordinate-reduced-add-interchange
                      (a (poly-reduced-mul u1 u2 modulus))
                      (b (poly-reduced-mul u1 u3 modulus))
                      (c (poly-reduced-mul
                          cubic (poly-reduced-mul v1 v2 modulus) modulus))
                      (d (poly-reduced-mul
                          cubic (poly-reduced-mul v1 v3 modulus) modulus))))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm quotient-coordinate-reduced-y-distributive
   (equal
    (poly-reduced-add
     (poly-reduced-mul u1 (poly-reduced-add v2 v3 modulus) modulus)
     (poly-reduced-mul v1 (poly-reduced-add u2 u3 modulus) modulus)
     modulus)
    (poly-reduced-add
     (poly-reduced-add (poly-reduced-mul u1 v2 modulus)
                       (poly-reduced-mul v1 u2 modulus) modulus)
     (poly-reduced-add (poly-reduced-mul u1 v3 modulus)
                       (poly-reduced-mul v1 u3 modulus) modulus)
     modulus))
   :hints
   (("Goal"
     :use ((:instance poly-reduced-mul-left-distributive
                      (a u1) (b v2) (c v3))
           (:instance poly-reduced-mul-left-distributive
                      (a v1) (b u2) (c u3))
           (:instance quotient-coordinate-reduced-add-interchange
                      (a (poly-reduced-mul u1 v2 modulus))
                      (b (poly-reduced-mul u1 v3 modulus))
                      (c (poly-reduced-mul v1 u2 modulus))
                      (d (poly-reduced-mul v1 u3 modulus))))
     :in-theory (theory 'minimal-theory)))))

(defthm quotient-coordinate-mul-left-distributive
  (equal
   (quotient-coordinate-mul
    x (quotient-coordinate-add z w modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-mul x z a b modulus)
    (quotient-coordinate-mul x w a b modulus) modulus)))

(defthm quotient-coordinate-mul-right-distributive
  (equal
   (quotient-coordinate-mul
    (quotient-coordinate-add x z modulus) w a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-mul x w a b modulus)
    (quotient-coordinate-mul z w a b modulus) modulus))
  :hints (("Goal"
           :use ((:instance quotient-coordinate-mul-left-distributive
                            (x w) (z x) (w z))
                 (:instance quotient-coordinate-mul-commutative
                            (x w) (z (quotient-coordinate-add x z modulus)))
                 (:instance quotient-coordinate-mul-commutative
                            (x w) (z x))
                 (:instance quotient-coordinate-mul-commutative
                            (x w) (z z)))
           :in-theory (disable quotient-coordinate-mul
                               quotient-coordinate-add))))

(local
 (defthm quotient-coordinate-reduced-mul-three-swap
   (equal (poly-reduced-mul
           a (poly-reduced-mul b c modulus) modulus)
          (poly-reduced-mul
           b (poly-reduced-mul a c modulus) modulus))
   :hints (("Goal"
            :use ((:instance poly-reduced-mul-commutative
                             (a a) (b (poly-reduced-mul b c modulus)))
                  (:instance poly-reduced-mul-commutative (a c) (b a)))
            :in-theory (enable poly-reduced-mul-associative)))))

(local
 (defthm quotient-coordinate-reduced-scalar-associative
   (equal
    (poly-reduced-add
     (poly-reduced-mul
      (poly-reduced-add
       (poly-reduced-mul u1 u2 modulus)
       (poly-reduced-mul cubic (poly-reduced-mul v1 v2 modulus) modulus)
       modulus)
      u3 modulus)
     (poly-reduced-mul
      cubic
      (poly-reduced-mul
       (poly-reduced-add (poly-reduced-mul u1 v2 modulus)
                         (poly-reduced-mul v1 u2 modulus) modulus)
       v3 modulus)
      modulus)
     modulus)
    (poly-reduced-add
     (poly-reduced-mul
      u1
      (poly-reduced-add
       (poly-reduced-mul u2 u3 modulus)
       (poly-reduced-mul cubic (poly-reduced-mul v2 v3 modulus) modulus)
       modulus)
      modulus)
     (poly-reduced-mul
      cubic
      (poly-reduced-mul
       v1
       (poly-reduced-add (poly-reduced-mul u2 v3 modulus)
                         (poly-reduced-mul v2 u3 modulus) modulus)
       modulus)
      modulus)
     modulus))
   :hints (("Goal"
            :in-theory
            (enable poly-reduced-mul-left-distributive
                    poly-reduced-mul-right-distributive
                    poly-reduced-mul-associative
                    poly-reduced-add-associative)))))

(local
 (defthm quotient-coordinate-reduced-y-associative
   (equal
    (poly-reduced-add
     (poly-reduced-mul
      (poly-reduced-add
       (poly-reduced-mul u1 u2 modulus)
       (poly-reduced-mul cubic (poly-reduced-mul v1 v2 modulus) modulus)
       modulus)
      v3 modulus)
     (poly-reduced-mul
      (poly-reduced-add (poly-reduced-mul u1 v2 modulus)
                        (poly-reduced-mul v1 u2 modulus) modulus)
      u3 modulus)
     modulus)
    (poly-reduced-add
     (poly-reduced-mul
      u1
      (poly-reduced-add (poly-reduced-mul u2 v3 modulus)
                        (poly-reduced-mul v2 u3 modulus) modulus)
      modulus)
     (poly-reduced-mul
      v1
      (poly-reduced-add
       (poly-reduced-mul u2 u3 modulus)
       (poly-reduced-mul cubic (poly-reduced-mul v2 v3 modulus) modulus)
       modulus)
      modulus)
     modulus))
   :hints (("Goal"
            :in-theory
            (enable poly-reduced-mul-left-distributive
                    poly-reduced-mul-right-distributive
                    poly-reduced-mul-associative
                    poly-reduced-add-associative)))))

(defthm quotient-coordinate-mul-associative
  (equal
   (quotient-coordinate-mul
    (quotient-coordinate-mul x z a b modulus) w a b modulus)
   (quotient-coordinate-mul
    x (quotient-coordinate-mul z w a b modulus) a b modulus)))

(defthm quotient-coordinate-embed-exact
  (equal (quotient-coordinate-embed polynomial modulus)
         (cons (poly-remainder polynomial modulus) nil)))

(defthm quotient-coordinate-embed-add
  (equal (quotient-coordinate-add
          (quotient-coordinate-embed x modulus)
          (quotient-coordinate-embed z modulus) modulus)
         (quotient-coordinate-embed (poly-add x z) modulus))
  :hints (("Goal" :use ((:instance poly-remainder-of-poly-add-remainders
                          (left x) (right z)))
           :in-theory (enable poly-reduced-add-definition))))

(defthm quotient-coordinate-embed-mul
  (equal (quotient-coordinate-mul
          (quotient-coordinate-embed x modulus)
          (quotient-coordinate-embed z modulus) a b modulus)
         (quotient-coordinate-embed (poly-mul x z) modulus))
  :hints (("Goal" :use ((:instance poly-remainder-of-poly-mul-remainders
                          (left x) (right z)))
           :in-theory (enable poly-reduced-mul-definition))))

(defthm quotient-coordinate-y-squared
  (equal (quotient-coordinate-mul
          (quotient-coordinate-y modulus)
          (quotient-coordinate-y modulus) a b modulus)
         (quotient-coordinate-embed
          (list (gfield::field-fix b) (gfield::field-fix a)
                (gfield::field-zero) (gfield::field-one))
          modulus))
  :hints (("Goal" :use ((:instance poly-reduced-mul-one-left
                          (a (quotient-coordinate-curve-cubic a b modulus)))
                        (:instance poly-reduced-mul-one-left
                          (a (poly-reduced-one modulus)))
                        (:instance poly-reduced-mul-one-right
                          (a (poly-reduced-one modulus)))))))

(verify-guards quotient-coordinate)
(verify-guards quotient-coordinate-u)
(verify-guards quotient-coordinate-v)
(verify-guards quotient-coordinate-fix)
(verify-guards quotient-coordinate-p)
(verify-guards quotient-coordinate-zero)
(verify-guards quotient-coordinate-one)
(verify-guards quotient-coordinate-embed)
(verify-guards quotient-coordinate-y)
(verify-guards quotient-coordinate-add)
(verify-guards quotient-coordinate-neg)
(verify-guards quotient-coordinate-sub)
(verify-guards quotient-coordinate-curve-cubic)
(verify-guards quotient-coordinate-mul)
