(in-package "GPOLY")

(include-book "quotient-coordinate")

(defthm quotient-coordinate-x-closed-minimal-theory-client
  (quotient-coordinate-p (quotient-coordinate-x modulus) modulus)
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-operations-closed))
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-zero-multiplication-minimal-theory-client
  (and
   (equal (quotient-coordinate-mul
           (quotient-coordinate-zero modulus) coordinate a b modulus)
          (quotient-coordinate-zero modulus))
   (equal (quotient-coordinate-mul
           coordinate (quotient-coordinate-zero modulus) a b modulus)
          (quotient-coordinate-zero modulus)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-mul-zero-left
                            (z coordinate))
                 (:instance quotient-coordinate-mul-zero-right
                            (z coordinate)))
           :in-theory (theory 'minimal-theory))))
