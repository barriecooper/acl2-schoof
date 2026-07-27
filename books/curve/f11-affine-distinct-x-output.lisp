(in-package "GFIELD")

(include-book "affine-distinct-x-output")
(include-book "f11-affine-distinct-x-output-y")

; Direct named-operation substitution into the generic constructor body.
(defun f11-affine-distinct-x-output (first second)
  (let ((output-x (f11-affine-distinct-x-output-x first second))
        (output-y (f11-affine-distinct-x-output-y first second)))
    (f11-affine-coordinates-make output-x output-y)))

(assert-event
 (and (equal (f11-affine-pair-classify '(1 2) '(3 6)) :distinct-x)
      (equal (f11-affine-distinct-x-output-x '(1 2) '(3 6)) 0)
      (equal (f11-affine-distinct-x-output-y '(1 2) '(3 6)) 0)
      (equal (f11-affine-distinct-x-output '(1 2) '(3 6)) '(0 0))
      (equal (f11-affine-coordinates-x
              (f11-affine-distinct-x-output '(1 2) '(3 6))) 0)
      (equal (f11-affine-coordinates-y
              (f11-affine-distinct-x-output '(1 2) '(3 6))) 0)
      (f11-affine-coordinates-p
       (f11-affine-distinct-x-output '(1 2) '(3 6)))
      (equal (f11-affine-coordinates-fix
              (f11-affine-distinct-x-output '(1 2) '(3 6))) '(0 0))))

(assert-event
 (and (equal (f11-affine-coordinates-fix '(2 4)) '(2 4))
      (equal (f11-affine-coordinates-fix '(3 9)) '(3 9))
      (equal (f11-affine-distinct-x-output-x '(2 4) '(3 9)) 9)
      (equal (f11-affine-distinct-x-output-y '(2 4) '(3 9)) 5)
      (equal (f11-affine-distinct-x-output '(2 4) '(3 9)) '(9 5))
      (equal (f11-affine-coordinates-x
              (f11-affine-distinct-x-output '(2 4) '(3 9))) 9)
      (equal (f11-affine-coordinates-y
              (f11-affine-distinct-x-output '(2 4) '(3 9))) 5)
      (f11-affine-coordinates-p
       (f11-affine-distinct-x-output '(2 4) '(3 9)))
      (equal (f11-affine-coordinates-fix
              (f11-affine-distinct-x-output '(2 4) '(3 9))) '(9 5))))

(assert-event
 (and (equal (f11-affine-coordinates-fix '(1 5)) '(1 5))
      (equal (f11-affine-coordinates-fix '(2 2)) '(2 2))
      (equal (f11-affine-distinct-x-output-x '(1 5) '(2 2)) 6)
      (equal (f11-affine-distinct-x-output-y '(1 5) '(2 2)) 10)
      (equal (f11-affine-distinct-x-output '(1 5) '(2 2)) '(6 10))
      (equal (f11-affine-coordinates-x
              (f11-affine-distinct-x-output '(1 5) '(2 2))) 6)
      (equal (f11-affine-coordinates-y
              (f11-affine-distinct-x-output '(1 5) '(2 2))) 10)
      (f11-affine-coordinates-p
       (f11-affine-distinct-x-output '(1 5) '(2 2)))
      (equal (f11-affine-coordinates-fix
              (f11-affine-distinct-x-output '(1 5) '(2 2))) '(6 10))))

(assert-event
 (and (equal (f11-affine-coordinates-fix '(12 13)) '(1 2))
      (equal (f11-affine-coordinates-fix '(14 17)) '(3 6))
      (equal (f11-affine-coordinates-x '(12 13)) 1)
      (equal (f11-affine-coordinates-y '(12 13)) 2)
      (equal (f11-affine-distinct-x-output-x '(12 13) '(14 17)) 0)
      (equal (f11-affine-distinct-x-output-y '(12 13) '(14 17)) 0)
      (equal (f11-affine-distinct-x-output '(12 13) '(14 17)) '(0 0))
      (equal (f11-affine-coordinates-x
              (f11-affine-distinct-x-output '(12 13) '(14 17))) 0)
      (equal (f11-affine-coordinates-y
              (f11-affine-distinct-x-output '(12 13) '(14 17))) 0)
      (f11-affine-coordinates-p
       (f11-affine-distinct-x-output '(12 13) '(14 17)))
      (equal (f11-affine-coordinates-fix
              (f11-affine-distinct-x-output '(12 13) '(14 17))) '(0 0))))

(assert-event
 (and (equal (f11-affine-coordinates-fix 'bad) '(0 0))
      (equal (f11-affine-coordinates-x 'bad) 0)
      (equal (f11-affine-coordinates-y 'bad) 0)
      (equal (f11-affine-distinct-x-output-x 'bad '(3 6)) 1)
      (equal (f11-affine-distinct-x-output-y 'bad '(3 6)) 9)
      (equal (f11-affine-distinct-x-output 'bad '(3 6)) '(1 9))
      (equal (f11-affine-coordinates-x
              (f11-affine-distinct-x-output 'bad '(3 6))) 1)
      (equal (f11-affine-coordinates-y
              (f11-affine-distinct-x-output 'bad '(3 6))) 9)
      (f11-affine-coordinates-p
       (f11-affine-distinct-x-output 'bad '(3 6)))
      (equal (f11-affine-coordinates-fix
              (f11-affine-distinct-x-output 'bad '(3 6))) '(1 9))))

; Outside :DISTINCT-X, (7 7) is only the inherited total programming value.
(assert-event
 (and (not (equal (f11-affine-pair-classify '(2 4) '(2 7)) :distinct-x))
      (equal (f11-affine-coordinates-fix '(2 4)) '(2 4))
      (equal (f11-affine-coordinates-fix '(2 7)) '(2 7))
      (equal (f11-affine-distinct-x-output-x '(2 4) '(2 7)) 7)
      (equal (f11-affine-distinct-x-output-y '(2 4) '(2 7)) 7)
      (equal (f11-affine-distinct-x-output '(2 4) '(2 7)) '(7 7))
      (equal (f11-affine-coordinates-x
              (f11-affine-distinct-x-output '(2 4) '(2 7))) 7)
      (equal (f11-affine-coordinates-y
              (f11-affine-distinct-x-output '(2 4) '(2 7))) 7)
      (f11-affine-coordinates-p
       (f11-affine-distinct-x-output '(2 4) '(2 7)))
      (equal (f11-affine-coordinates-fix
              (f11-affine-distinct-x-output '(2 4) '(2 7))) '(7 7))))

(verify-guards f11-affine-distinct-x-output)
