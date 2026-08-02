(in-package "GFIELD")
(include-book "affine-dd-secant-associativity")

(local
 (defthm affine-dd-secant-associativity-minimal-theory-regression
   (implies
    (and
     (affine-distinct-x-secant-relation-p a b p-slope ab)
     (affine-distinct-x-secant-relation-p b c r-slope bc)
     (affine-distinct-x-secant-relation-p ab c q-slope left)
     (affine-distinct-x-secant-relation-p a bc tt-slope right))
    (equal (affine-coordinates-fix left)
           (affine-coordinates-fix right)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance
            affine-dd-secant-relation-associative-when-all-distinct-x))
     :in-theory (theory 'minimal-theory)))))
