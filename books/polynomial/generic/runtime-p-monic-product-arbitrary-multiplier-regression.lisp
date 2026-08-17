(in-package "GPOLY")

(include-book "runtime-p-monic-product-arbitrary-multiplier")

(defthm runtime-p-poly-mul-nonzero-by-monic-properties-minimal-theory-client
  (implies
   (and (runtime-p-canonical-polynomial-p multiplier p)
        (consp multiplier)
        (equal (runtime-p-poly-leading-coefficient divisor p)
               (runtime-p-one p)))
   (let ((product (runtime-p-poly-mul multiplier divisor p)))
     (and (runtime-p-canonical-polynomial-p product p)
          (consp product)
          (equal (runtime-p-poly-degree product p)
                 (+ (runtime-p-poly-degree multiplier p)
                    (runtime-p-poly-degree divisor p)))
          (equal (runtime-p-poly-leading-coefficient product p)
                 (runtime-p-poly-leading-coefficient multiplier p))
          (equal (len product)
                 (+ -1 (len multiplier)
                    (len (runtime-p-normalize divisor p)))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  runtime-p-poly-mul-nonzero-by-monic-properties))
           :in-theory (theory 'minimal-theory))))

; F7, with the reducible monic divisor x^2-1 and a multi-term multiplier.
(assert-event
 (let* ((multiplier '(1 2 3))
        (divisor '(6 0 1))
        (product (runtime-p-poly-mul multiplier divisor 7)))
   (and (equal product '(6 5 5 2 3))
        (consp product)
        (equal (runtime-p-poly-degree product 7) 4)
        (equal (runtime-p-poly-leading-coefficient product 7) 3)
        (equal (len product) 5))))

; Composite modulus 6: lower coefficients may contain zero-divisor products,
; but the monic top coefficient preserves degree and leading coefficient.
(assert-event
 (let ((product (runtime-p-poly-mul '(1 2 3) '(2 1) 6)))
   (and (equal product '(2 5 2 3))
        (equal (runtime-p-poly-degree product 6) 3)
        (equal (runtime-p-poly-leading-coefficient product 6) 3)
        (<= (runtime-p-poly-degree '(2 1) 6)
            (runtime-p-poly-degree product 6)))))

; Raw coefficients and a trailing zero normalize to the same reducible monic
; F7 divisor used above.
(assert-event
 (equal (runtime-p-poly-mul '(1 2 3) '(13 0 8 0) 7)
        '(6 5 5 2 3)))

; A malformed p uses effective modulus 2.
(assert-event
 (let ((product (runtime-p-poly-mul '(1 1) '(1 1 0) 'malformed)))
   (and (equal product '(1 0 1))
        (equal (runtime-p-poly-degree product 'malformed) 2)
        (equal (runtime-p-poly-leading-coefficient product 'malformed) 1))))

; The monic hypothesis is essential: over Z/6Z two nonzero, nonmonic
; constants can multiply to zero, so unrestricted degree additivity is false.
(assert-event
 (and (consp (runtime-p-normalize '(3) 6))
      (consp (runtime-p-normalize '(2) 6))
      (equal (runtime-p-poly-mul '(3) '(2) 6) nil)
      (not (equal (runtime-p-poly-degree
                   (runtime-p-poly-mul '(3) '(2) 6) 6)
                  (+ (runtime-p-poly-degree '(3) 6)
                     (runtime-p-poly-degree '(2) 6))))))
