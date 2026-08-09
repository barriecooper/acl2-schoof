(in-package "GPOLY")

(include-book "finite-field-reduced-ring")
(include-book "f7-reduced-arithmetic")

(defthm finite-field-poly-reduced-add-commutative-minimal-theory-client
  (equal (finite-field-poly-reduced-add left right modulus)
         (finite-field-poly-reduced-add right left modulus))
  :hints (("Goal"
           :in-theory (theory 'minimal-theory)
           :use ((:instance finite-field-poly-reduced-add-commutative
                            (a left) (b right))))))

(defthm finite-field-poly-reduced-add-definition-minimal-theory-client
  (equal (finite-field-poly-reduced-add left right modulus)
         (finite-field-poly-remainder (finite-field-poly-add left right)
                                      modulus))
  :hints (("Goal"
           :in-theory (theory 'minimal-theory)
           :use ((:instance finite-field-poly-reduced-add-definition)))))

(defthm finite-field-poly-reduced-add-associative-minimal-theory-client
  (equal
   (finite-field-poly-reduced-add
    (finite-field-poly-reduced-add a b modulus) c modulus)
   (finite-field-poly-reduced-add
    a (finite-field-poly-reduced-add b c modulus) modulus))
  :hints
  (("Goal"
    :in-theory (theory 'minimal-theory)
    :use ((:instance finite-field-poly-reduced-add-associative)))))

; Concrete F7 execution witnesses use the existing executable F7 reduced-ring
; instance.  They supplement, but do not replace, the generic staged theorem.
(assert-event (equal (f7-poly-reduced-add '(1 2) '(3 4) '(1 0 1))
                     '(4 6)))
(assert-event (equal (f7-poly-reduced-add '(1 2) '(6 5) '(1 0 1))
                     nil))
(assert-event (equal (f7-poly-reduced-add nil '(3 4) '(1 0 1))
                     '(3 4)))
(assert-event (equal (f7-poly-reduced-add '(8 . bad-tail) 'malformed
                                          '(1 0 1))
                     '(1)))
(assert-event (equal (f7-poly-reduced-add '(1 2) '(3 4) nil)
                     '(4 6)))
(assert-event (equal (f7-poly-reduced-add '(1) '(6) '(0 0))
                     nil))
