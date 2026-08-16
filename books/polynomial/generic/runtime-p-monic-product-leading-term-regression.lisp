(in-package "GPOLY")

(include-book "runtime-p-monic-product-leading-term")

; The aggregate boundary is intentionally opt-in even for an exact client.
(defthm runtime-p-monic-product-leading-term-minimal-theory-client
  (implies
   (and (consp (runtime-p-normalize remainder p))
        (equal (runtime-p-poly-leading-coefficient divisor p)
               (runtime-p-one p))
        (<= (runtime-p-poly-degree divisor p)
            (runtime-p-poly-degree remainder p)))
   (let* ((term
           (runtime-p-poly-monomial
            (runtime-p-poly-leading-coefficient remainder p)
            (- (runtime-p-poly-degree remainder p)
               (runtime-p-poly-degree divisor p))
            p))
          (product (runtime-p-poly-mul term divisor p)))
     (and (runtime-p-canonical-polynomial-p product p)
          (consp product)
          (equal (runtime-p-poly-degree product p)
                 (runtime-p-poly-degree remainder p))
          (equal (runtime-p-poly-leading-coefficient product p)
                 (runtime-p-poly-leading-coefficient remainder p))
          (equal (len product)
                 (len (runtime-p-normalize remainder p))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-monic-product-leading-term-properties))
           :in-theory (theory 'minimal-theory))))

; Over Z/6Z the lower product 3*2 vanishes, but the monic top product 3*1
; survives.  The active term for the chosen remainder is 3*x^2.
(assert-event
 (let* ((p 6)
        (remainder '(5 0 4 3))
        (divisor '(2 1))
        (term (runtime-p-poly-monomial
               (runtime-p-poly-leading-coefficient remainder p)
               (- (runtime-p-poly-degree remainder p)
                  (runtime-p-poly-degree divisor p))
               p))
        (product (runtime-p-poly-mul term divisor p)))
   (and (equal term '(0 0 3))
        (equal product '(0 0 0 3))
        (runtime-p-canonical-polynomial-p product p)
        (equal (runtime-p-poly-degree product p)
               (runtime-p-poly-degree remainder p))
        (equal (runtime-p-poly-leading-coefficient product p)
               (runtime-p-poly-leading-coefficient remainder p))
        (equal (len product) (len (runtime-p-normalize remainder p))))))

; Unrestricted product-degree additivity is false over the same total ring:
; both factors are nonzero constants, while their product is canonical zero.
(assert-event
 (and (equal (runtime-p-poly-degree '(3) 6) 0)
      (equal (runtime-p-poly-degree '(2) 6) 0)
      (equal (runtime-p-poly-mul '(3) '(2) 6) nil)
      (equal (runtime-p-poly-degree
              (runtime-p-poly-mul '(3) '(2) 6) 6)
             -1)))

; A malformed modulus follows the documented effective-modulus-2 convention.
(assert-event
 (equal (runtime-p-poly-mul
         (runtime-p-poly-monomial 1 1 'malformed)
         '(1 1) 'malformed)
        '(0 1 1)))
