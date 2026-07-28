(in-package "GFIELD")

(include-book "affine-same-point-non-opposite-output")
(include-book "f11-affine-same-point-non-opposite-output-y")

; Direct named-operation substitution into the generic constructor body.
(defun f11-affine-same-point-non-opposite-output (first)
  (let ((output-x (f11-affine-same-point-non-opposite-output-x first))
        (output-y (f11-affine-same-point-non-opposite-output-y first)))
    (f11-affine-coordinates-make output-x output-y)))

; Execution evidence only: the generic structural theorems, rather than this
; concrete example, establish the constructor interface.
(assert-event
 (and (equal (f11-affine-coordinates-fix '(2 4)) '(2 4))
      (equal (f11-affine-same-point-non-opposite-output-x '(2 4)) 5)
      (equal (f11-affine-same-point-non-opposite-output-y '(2 4)) 9)
      (equal (f11-affine-same-point-non-opposite-output '(2 4)) '(5 9))
      (equal
       (f11-affine-coordinates-x
        (f11-affine-same-point-non-opposite-output '(2 4)))
       5)
      (equal
       (f11-affine-coordinates-y
        (f11-affine-same-point-non-opposite-output '(2 4)))
       9)
      (f11-affine-coordinates-p
       (f11-affine-same-point-non-opposite-output '(2 4)))
      (equal
       (f11-affine-coordinates-fix
        (f11-affine-same-point-non-opposite-output '(2 4)))
       '(5 9))))

(verify-guards f11-affine-same-point-non-opposite-output)
