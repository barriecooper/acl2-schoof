(in-package "GFIELD")
(include-book "xcert-semantics")

; Protect the exact ordered A/B/C configuration independently of proof use.
(local
 (defthm xcert-curve-operand-map-regression
   (and
    (equal (xcert-ab a b) (affine-distinct-x-output a b))
    (equal (xcert-bc b c) (affine-distinct-x-output b c))
    (equal (xcert-left a b c)
           (affine-distinct-x-output (affine-distinct-x-output a b) c))
    (equal (xcert-right a b c)
           (affine-distinct-x-output a (affine-distinct-x-output b c)))
    (equal (xcert-p a b) (affine-distinct-x-slope a b))
    (equal (xcert-q a b c)
           (affine-distinct-x-slope (affine-distinct-x-output a b) c))
    (equal (xcert-r b c) (affine-distinct-x-slope b c))
    (equal (xcert-tt a b c)
           (affine-distinct-x-slope a (affine-distinct-x-output b c))))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
                            '(xcert-ab xcert-bc xcert-left xcert-right
                              xcert-p xcert-q xcert-r xcert-tt))))))

; Public-theorem regressions protect all orientations and the opaque curve
; instantiation.  The production statements, rather than fresh algebra, close
; this event.
(local
 (defthm xcert-curve-public-results-regression
   (and
    (equal (xcert-gxl (xcert-xl a b c) (xcert-xab a b) (xcert-xc c)
                       (xcert-q a b c)) (field-zero))
    (equal (xcert-gxr (xcert-xr a b c) (xcert-xa a) (xcert-xbc b c)
                       (xcert-tt a b c)) (field-zero))
    (equal (xcert-gxab (xcert-xab a b) (xcert-xa a) (xcert-xb b)
                        (xcert-p a b)) (field-zero))
    (equal (xcert-gxbc (xcert-xbc b c) (xcert-xb b) (xcert-xc c)
                        (xcert-r b c)) (field-zero))
    (equal
     (xcert-dx (xcert-xl a b c) (xcert-xr a b c))
     (field-add
      (field-sub
       (xcert-telescope (xcert-xl a b c) (xcert-xr a b c)
                        (xcert-xab a b) (xcert-xbc b c)
                        (xcert-xa a) (xcert-xb b) (xcert-xc c)
                        (xcert-p a b) (xcert-q a b c) (xcert-r b c)
                        (xcert-tt a b c))
       (field-add
        (xcert-h (xcert-p a b) (xcert-q a b c) (xcert-r b c)
                 (xcert-xa a) (xcert-xc c))
        (xcert-h (xcert-p a b) (xcert-q a b c) (xcert-r b c)
                 (xcert-xa a) (xcert-xc c))))
      (field-mul
       (xcert-c (xcert-p a b) (xcert-q a b c) (xcert-r b c)
                (xcert-tt a b c))
       (xcert-s (xcert-p a b) (xcert-q a b c) (xcert-r b c)
                (xcert-tt a b c))))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance xcert-gxl-curve-zero)
                          (:instance xcert-gxr-curve-zero)
                          (:instance xcert-gxab-curve-zero)
                          (:instance xcert-gxbc-curve-zero)
                          (:instance xcert-curve-composition))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm xcert-h-curve-zero-regression
   (implies
    (and (short-weierstrass-affine-point-p a)
         (short-weierstrass-affine-point-p b)
         (short-weierstrass-affine-point-p c)
         (equal (affine-pair-classify a b) :distinct-x)
         (equal (affine-pair-classify b c) :distinct-x)
         (equal (affine-pair-classify (xcert-ab a b) c) :distinct-x))
    (equal (xcert-h (xcert-p a b) (xcert-q a b c) (xcert-r b c)
                    (xcert-xa a) (xcert-xc c))
           (field-zero)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance xcert-h-curve-zero))
             :in-theory (theory 'minimal-theory)))))

(local
 (defthm xcert-s-curve-zero-regression
   (implies
    (and (short-weierstrass-affine-point-p a)
         (short-weierstrass-affine-point-p b)
         (short-weierstrass-affine-point-p c)
         (equal (affine-pair-classify a b) :distinct-x)
         (equal (affine-pair-classify b c) :distinct-x)
         (equal (affine-pair-classify (xcert-ab a b) c) :distinct-x)
         (equal (affine-pair-classify a (xcert-bc b c)) :distinct-x))
    (equal
     (field-sub (field-add (xcert-p a b) (xcert-q a b c))
                (field-add (xcert-r b c) (xcert-tt a b c)))
     (field-zero)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance xcert-s-curve-zero))
             :in-theory (union-theories (theory 'minimal-theory)
                         '(xcert-p xcert-q xcert-r xcert-tt))))))
