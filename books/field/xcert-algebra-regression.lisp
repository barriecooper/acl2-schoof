(in-package "GFIELD")

(include-book "xcert-algebra")

; Definition-shape regressions protect the residual orientations and the
; deliberately left-associated telescope without making them rewrite rules.
(local
 (defthm xcert-residual-definitions-regression
   (and
    (equal (xcert-gxl xl xab xc q)
           (field-sub (field-add (field-add xl xab) xc) (field-mul q q)))
    (equal (xcert-gxr xr xa xbc tt)
           (field-sub (field-add (field-add xr xa) xbc) (field-mul tt tt)))
    (equal (xcert-gxab xab xa xb p)
           (field-sub (field-add (field-add xab xa) xb) (field-mul p p)))
    (equal (xcert-gxbc xbc xb xc r)
           (field-sub (field-add (field-add xbc xb) xc) (field-mul r r))))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
                            '(xcert-gxl xcert-gxr xcert-gxab xcert-gxbc))))))

(local
 (defthm xcert-grouped-definitions-regression
   (and
    (equal (xcert-dx xl xr) (field-sub xl xr))
    (equal
     (xcert-telescope xl xr xab xbc xa xb xc p q r tt)
     (field-add
      (field-sub
       (field-sub (xcert-gxl xl xab xc q)
                  (xcert-gxr xr xa xbc tt))
       (xcert-gxab xab xa xb p))
      (xcert-gxbc xbc xb xc r)))
    (equal
     (xcert-remainder p q r tt xa xc)
     (field-add
      (field-add (field-sub (field-mul q q) (field-mul p p))
                 (field-sub (field-mul r r) (field-mul tt tt)))
      (field-add (field-sub xa xc) (field-sub xa xc))))
    (equal
     (xcert-h p q r xa xc)
     (field-sub (field-mul (field-sub p r) (field-add p q))
                (field-sub xa xc)))
    (equal (xcert-s p q r tt)
           (field-sub (field-add p q) (field-add r tt)))
    (equal (xcert-c p q r tt)
           (field-add (field-sub (field-add p q) r) tt)))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
                            '(xcert-dx xcert-telescope xcert-remainder
                              xcert-h xcert-s xcert-c))))))

 ; The generic kernel is constrained and non-executable.  These focused theorem
; regressions therefore protect all three public statements without pretending
; that a concrete instance supplies their generic proofs.
(local
 (defthm xcert-public-theorems-regression
   (and
    (equal (xcert-dx xl xr)
           (field-add
            (xcert-telescope xl xr xab xbc xa xb xc p q r tt)
            (xcert-remainder p q r tt xa xc)))
    (equal
     (xcert-remainder p q r tt xa xc)
     (field-add
      (field-neg (field-add (xcert-h p q r xa xc)
                            (xcert-h p q r xa xc)))
      (field-mul (xcert-c p q r tt) (xcert-s p q r tt))))
    (equal
     (xcert-dx xl xr)
     (field-add
      (field-sub
       (xcert-telescope xl xr xab xbc xa xb xc p q r tt)
       (field-add (xcert-h p q r xa xc)
                  (xcert-h p q r xa xc)))
      (field-mul (xcert-c p q r tt) (xcert-s p q r tt)))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance xcert-output-telescope)
                  (:instance xcert-remainder-identity)
                  (:instance xcert-composition))
            :in-theory (theory 'minimal-theory)))))
