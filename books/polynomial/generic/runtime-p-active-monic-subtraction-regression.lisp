(in-package "GPOLY")

(include-book "runtime-p-active-monic-subtraction")

(defthm runtime-p-active-monic-subtraction-minimal-theory-client
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
               (runtime-p-poly-degree divisor p)) p))
          (product (runtime-p-poly-mul term divisor p))
          (next (runtime-p-poly-sub remainder product p)))
     (and (runtime-p-canonical-polynomial-p next p)
          (equal (runtime-p-poly-add product next p)
                 (runtime-p-normalize remainder p))
          (< (len next) (len (runtime-p-normalize remainder p)))
          (or (not (consp next))
              (< (runtime-p-poly-degree next p)
                 (runtime-p-poly-degree remainder p))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-active-monic-subtraction-properties))
           :in-theory (theory 'minimal-theory))))

; Modulo 6, 3*2 vanishes in the lower product coefficient, while the monic
; top coefficient 3*1 survives and is then cancelled by subtraction.
(assert-event
 (let* ((p 6)
        (remainder '(5 0 4 3))
        (divisor '(2 1))
        (term (runtime-p-poly-monomial
               (runtime-p-poly-leading-coefficient remainder p)
               (- (runtime-p-poly-degree remainder p)
                  (runtime-p-poly-degree divisor p)) p))
        (product (runtime-p-poly-mul term divisor p))
        (next (runtime-p-poly-sub remainder product p)))
   (and (equal term '(0 0 3))
        (equal product '(0 0 0 3))
        (equal next '(5 0 4))
        (equal (runtime-p-poly-add product next p) remainder)
        (< (len next) (len (runtime-p-normalize remainder p)))
        (< (runtime-p-poly-degree next p)
           (runtime-p-poly-degree remainder p)))))

(assert-event
 (let* ((p 6)
        (remainder '(2 1))
        (divisor '(2 1))
        (term (runtime-p-poly-monomial
               (runtime-p-poly-leading-coefficient remainder p)
               (- (runtime-p-poly-degree remainder p)
                  (runtime-p-poly-degree divisor p)) p))
        (product (runtime-p-poly-mul term divisor p))
        (next (runtime-p-poly-sub remainder product p)))
   (and (equal term '(1))
        (equal product '(2 1))
        (equal next nil)
        (equal (runtime-p-poly-add product next p) remainder)
        (< (len next) (len (runtime-p-normalize remainder p))))))

; Malformed p executes with the documented effective modulus 2.
(assert-event
 (let* ((p 'malformed)
        (remainder '(3 0 3))
        (divisor '(1 1))
        (term (runtime-p-poly-monomial
               (runtime-p-poly-leading-coefficient remainder p)
               (- (runtime-p-poly-degree remainder p)
                  (runtime-p-poly-degree divisor p)) p))
        (product (runtime-p-poly-mul term divisor p))
        (next (runtime-p-poly-sub remainder product p)))
   (and (equal term '(0 1))
        (equal product '(0 1 1))
        (equal next '(1 1))
        (equal (runtime-p-poly-add product next p) '(1 0 1))
        (< (len next) (len (runtime-p-normalize remainder p)))
        (< (runtime-p-poly-degree next p)
           (runtime-p-poly-degree remainder p)))))
