(in-package "GFIELD")

(include-book "xcert-semantics")
(include-book "affine-distinct-x-secant-identity")

; Protect the three ordered input-secant instances needed by the prospective H
; reconstruction.  In particular, no slope is replaced by a reversed quotient.
(local
 (defthm xcert-ordered-input-secants-regression
   (implies
    (and (short-weierstrass-affine-point-p a)
         (short-weierstrass-affine-point-p b)
         (short-weierstrass-affine-point-p c)
         (short-weierstrass-affine-point-p (xcert-ab a b))
         (equal (affine-pair-classify a b) :distinct-x)
         (equal (affine-pair-classify b c) :distinct-x)
         (equal (affine-pair-classify (xcert-ab a b) c) :distinct-x))
    (and
     (equal
      (field-mul (xcert-p a b)
                 (field-add (affine-coordinates-y b)
                            (affine-coordinates-y a)))
      (field-add
       (field-mul (xcert-xb b) (xcert-xb b))
       (field-add
        (field-mul (xcert-xb b) (xcert-xa a))
        (field-add (field-mul (xcert-xa a) (xcert-xa a))
                   (field-fix (short-weierstrass-a))))))
     (equal
      (field-mul (xcert-r b c)
                 (field-add (affine-coordinates-y c)
                            (affine-coordinates-y b)))
      (field-add
       (field-mul (xcert-xc c) (xcert-xc c))
       (field-add
        (field-mul (xcert-xc c) (xcert-xb b))
        (field-add (field-mul (xcert-xb b) (xcert-xb b))
                   (field-fix (short-weierstrass-a))))))
     (equal
      (field-mul (xcert-q a b c)
                 (field-add (affine-coordinates-y c)
                            (affine-coordinates-y (xcert-ab a b))))
      (field-add
       (field-mul (xcert-xc c) (xcert-xc c))
       (field-add
        (field-mul (xcert-xc c) (xcert-xab a b))
        (field-add (field-mul (xcert-xab a b) (xcert-xab a b))
                   (field-fix (short-weierstrass-a))))))))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-distinct-x-input-secant-identity
                 (first a) (second b))
      (:instance affine-distinct-x-input-secant-identity
                 (first b) (second c))
      (:instance affine-distinct-x-input-secant-identity
                 (first (xcert-ab a b)) (second c)))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(xcert-p xcert-q xcert-r xcert-xa xcert-xb xcert-xc
                       xcert-xab))))))
