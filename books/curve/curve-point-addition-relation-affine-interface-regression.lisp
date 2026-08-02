(in-package "GFIELD")

(include-book "curve-point-addition-relation-affine-interface")

(defthm affine-relation-case-coverage-client-regression
  (implies
   (and
    (short-weierstrass-affine-point-p a)
    (short-weierstrass-affine-point-p b)
    (curve-point-addition-relation-p
     (curve-point-affine-coordinates a)
     (curve-point-affine-coordinates b)
     output))
   (or
    (let ((payload (curve-point-affine-coordinates-get
                    (curve-point-fix output)))
          (slope (field-div
                  (field-sub (affine-coordinates-y (affine-coordinates-fix b))
                             (affine-coordinates-y (affine-coordinates-fix a)))
                  (field-sub (affine-coordinates-x (affine-coordinates-fix b))
                             (affine-coordinates-x (affine-coordinates-fix a))))))
      (and
       (equal (curve-point-fix output)
              (curve-point-affine-coordinates (affine-coordinates-fix payload)))
       (affine-distinct-x-secant-relation-p
        (affine-coordinates-fix a) (affine-coordinates-fix b)
        slope payload)))
    (affine-opposite-y-infinity-relation-p a b output)
    (let ((payload (curve-point-affine-coordinates-get
                    (curve-point-fix output)))
          (tangent
           (field-div
            (field-add
             (field-mul
              (field-add (field-add (field-one) (field-one)) (field-one))
              (field-mul (affine-coordinates-x (affine-coordinates-fix a))
                         (affine-coordinates-x (affine-coordinates-fix a))))
             (field-fix (short-weierstrass-a)))
            (field-add (affine-coordinates-y (affine-coordinates-fix a))
                       (affine-coordinates-y (affine-coordinates-fix a))))))
      (and
       (equal (curve-point-fix output)
              (curve-point-affine-coordinates (affine-coordinates-fix payload)))
       (affine-doubling-relation-p (affine-coordinates-fix a) tangent payload)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use (curve-point-addition-relation-affine-case-coverage)
    :in-theory (theory 'minimal-theory))))

(defthm fixed-operands-determinacy-client-regression
  (implies
   (and
    (curve-point-addition-relation-p first-a second-a output-a)
    (curve-point-addition-relation-p first-b second-b output-b)
    (equal (curve-point-fix first-a) (curve-point-fix first-b))
    (equal (curve-point-fix second-a) (curve-point-fix second-b)))
   (equal (curve-point-fix output-a) (curve-point-fix output-b)))
  :rule-classes nil
  :hints
  (("Goal"
    :use (curve-point-addition-relation-output-determinate-under-fixed-operands)
    :in-theory (theory 'minimal-theory))))
