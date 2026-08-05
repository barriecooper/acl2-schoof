(in-package "GPOLY")

(include-book "finite-field-reduction")
(include-book "f7-division")

(local (in-theory (disable finite-field-poly-divmod-core
                           finite-field-poly-divmod
                           finite-field-poly-remainder
                           finite-field-poly-reduced-p
                           finite-field-poly-division-step-core
                           finite-field-poly-add
                           finite-field-poly-mul
                           finite-field-poly-normalize
                           finite-field-poly-raw-add
                           finite-field-poly-raw-mul)))

(defthm finite-field-remainder-normalize-minimal-theory-client
  (and (equal (finite-field-poly-remainder
               (finite-field-poly-normalize dividend) modulus)
              (finite-field-poly-remainder dividend modulus))
       (equal (finite-field-poly-remainder
               dividend (finite-field-poly-normalize modulus))
              (finite-field-poly-remainder dividend modulus))
       (equal (finite-field-poly-normalize
               (finite-field-poly-remainder dividend modulus))
              (finite-field-poly-remainder dividend modulus)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance finite-field-poly-remainder-of-normalize-dividend)
                 (:instance finite-field-poly-remainder-of-normalize-modulus)
                 (:instance finite-field-poly-normalize-of-remainder)))))

(defthm finite-field-remainder-fixer-minimal-theory-client
  (and (finite-field-poly-reduced-p
        (finite-field-poly-remainder polynomial modulus) modulus)
       (equal (finite-field-poly-remainder
               (finite-field-poly-remainder polynomial modulus) modulus)
              (finite-field-poly-remainder polynomial modulus))
       (implies (finite-field-poly-reduced-p polynomial modulus)
                (equal (finite-field-poly-remainder polynomial modulus)
                       polynomial)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance finite-field-poly-reduced-p-of-remainder)
                 (:instance finite-field-poly-remainder-idempotent
                            (dividend polynomial))
                 (:instance finite-field-poly-remainder-when-reduced-p)))))

(defthm finite-field-reduced-characterization-minimal-theory-client
  (implies
   (consp (finite-field-poly-normalize modulus))
   (equal
    (finite-field-poly-reduced-p polynomial modulus)
    (and (finite-field-canonical-polynomial-p polynomial)
         (or (equal polynomial nil)
             (< (finite-field-poly-degree polynomial)
                (finite-field-poly-degree
                 (finite-field-poly-normalize modulus)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance finite-field-poly-reduced-p-iff-canonical-and-degree-bounded)))))

(defthm f7-reduction-public-interface-client
  (and (equal (f7-poly-remainder (f7-normalize dividend) modulus)
              (f7-poly-remainder dividend modulus))
       (equal (f7-poly-remainder
               (f7-poly-remainder dividend modulus) modulus)
              (f7-poly-remainder dividend modulus)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f7-poly-remainder-of-normalize-dividend)
                         (:instance f7-poly-remainder-idempotent)))))

(assert-event (equal (f7-poly-remainder '(1) '(0 1)) '(1)))
(assert-event (equal (f7-poly-remainder '(1 0 1) '(1 1)) '(2)))
(assert-event (equal (f7-poly-remainder '(2 3) '(1 0 1)) '(2 3)))
(assert-event (equal (f7-poly-remainder nil '(1 1)) nil))
(assert-event (equal (f7-poly-remainder '(1 0 1) nil) '(1 0 1)))
(assert-event (equal (f7-poly-remainder '(0 0) '(0 0)) nil))
(assert-event (equal (f7-poly-remainder '(8 . bad-tail) '(1 1)) '(1)))
