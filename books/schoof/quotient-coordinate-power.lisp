(in-package "GPOLY")

(include-book "quotient-coordinate")

; Transparent repeated multiplication in the quotient-coordinate commutative
; ring.  The public operation totalizes both arguments: N is read through
; NFIX and the base is fixed before the logical recursion starts.
(defun quotient-coordinate-pow-spec (base n a b modulus)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (quotient-coordinate-one modulus)
    (quotient-coordinate-mul
     base
     (quotient-coordinate-pow-spec base (1- n) a b modulus)
     a b modulus)))

(defun quotient-coordinate-pow (base n a b modulus)
  (quotient-coordinate-pow-spec
   (quotient-coordinate-fix base modulus) (nfix n) a b modulus))

(defthm quotient-coordinate-p-of-pow-spec
  (quotient-coordinate-p
   (quotient-coordinate-pow-spec base n a b modulus) modulus)
  :hints (("Goal" :induct (quotient-coordinate-pow-spec base n a b modulus)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(quotient-coordinate-pow-spec
                         quotient-coordinate-operations-closed)))))

(defthm quotient-coordinate-p-of-pow
  (quotient-coordinate-p
   (quotient-coordinate-pow base n a b modulus) modulus)
  :hints (("Goal" :in-theory (enable quotient-coordinate-pow))))

(defthm quotient-coordinate-pow-of-fix
  (equal (quotient-coordinate-pow
          (quotient-coordinate-fix base modulus) n a b modulus)
         (quotient-coordinate-pow base n a b modulus))
  :hints (("Goal" :use ((:instance quotient-coordinate-fix-idempotent
                          (coordinate base)))
           :in-theory (e/d (quotient-coordinate-pow)
                           (quotient-coordinate-fix)))))

(defthm quotient-coordinate-pow-of-nfix
  (equal (quotient-coordinate-pow base (nfix n) a b modulus)
         (quotient-coordinate-pow base n a b modulus))
  :hints (("Goal" :in-theory (enable quotient-coordinate-pow))))

(defthm quotient-coordinate-pow-zero
  (equal (quotient-coordinate-pow base 0 a b modulus)
         (quotient-coordinate-one modulus))
  :hints (("Goal" :in-theory
           (enable quotient-coordinate-pow quotient-coordinate-pow-spec))))

(local
 (defthm quotient-coordinate-mul-left-fix-for-power
   (equal (quotient-coordinate-mul
           (quotient-coordinate-fix left modulus) right a b modulus)
          (quotient-coordinate-mul left right a b modulus))
   :hints (("Goal" :use ((:instance quotient-coordinate-fix-idempotent
                           (coordinate left)))
            :in-theory (e/d (quotient-coordinate-mul)
                            (quotient-coordinate-fix))))))

(defthm quotient-coordinate-pow-spec-successor
  (equal (quotient-coordinate-pow-spec base (+ 1 (nfix n)) a b modulus)
         (quotient-coordinate-mul
          base (quotient-coordinate-pow-spec base (nfix n) a b modulus)
          a b modulus))
  :hints (("Goal"
           :expand ((quotient-coordinate-pow-spec
                     base (+ 1 (nfix n)) a b modulus))
           :in-theory (e/d (nfix zp)
                           (quotient-coordinate-mul
                            quotient-coordinate-fix)))))

(defthm quotient-coordinate-pow-successor
  (equal (quotient-coordinate-pow base (+ 1 (nfix n)) a b modulus)
         (quotient-coordinate-mul
          base (quotient-coordinate-pow base n a b modulus) a b modulus))
  :hints (("Goal" :use ((:instance quotient-coordinate-pow-spec-successor
                          (base (quotient-coordinate-fix base modulus))))
           :in-theory (e/d (quotient-coordinate-pow
                            quotient-coordinate-mul-left-fix-for-power)
                           (quotient-coordinate-mul quotient-coordinate-fix
                            quotient-coordinate-pow-spec))
           :do-not-induct t)))

(defthm quotient-coordinate-pow-one
  (equal (quotient-coordinate-pow base 1 a b modulus)
         (quotient-coordinate-fix base modulus))
  :hints (("Goal" :use ((:instance quotient-coordinate-pow-successor (n 0))))))

; Cardinality-indexed power.  The name records the intended Schoof action;
; homomorphism properties require characteristic/prime-power metadata and are
; deliberately not asserted by this universally quantified book.
(defun quotient-coordinate-frobenius (coordinate q a b modulus)
  (quotient-coordinate-pow coordinate q a b modulus))

(defun quotient-coordinate-frobenius-iterate (coordinate q iterations a b modulus)
  (quotient-coordinate-pow coordinate
                           (expt (nfix q) (nfix iterations)) a b modulus))

(defthm quotient-coordinate-p-of-frobenius
  (quotient-coordinate-p
   (quotient-coordinate-frobenius coordinate q a b modulus) modulus))

(defthm quotient-coordinate-frobenius-iterate-one
  (equal (quotient-coordinate-frobenius-iterate coordinate q 1 a b modulus)
         (quotient-coordinate-frobenius coordinate q a b modulus))
  :hints (("Goal" :in-theory (enable quotient-coordinate-frobenius-iterate
                                      quotient-coordinate-frobenius))))

(verify-guards quotient-coordinate-pow-spec)
(verify-guards quotient-coordinate-pow)
(verify-guards quotient-coordinate-frobenius)
(verify-guards quotient-coordinate-frobenius-iterate)

(in-theory (disable quotient-coordinate-pow-spec))
