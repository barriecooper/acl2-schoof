(in-package "GFIELD")

(include-book "curve-point-addition-relation-associativity-structural")

(defthm relation-both-inner-opposite-y-client-regression
  (implies
   (and (affine-opposite-y-infinity-relation-p a b ab)
        (affine-opposite-y-infinity-relation-p b c bc)
        (curve-point-addition-relation-p
         ab (curve-point-affine-coordinates c) left)
        (curve-point-addition-relation-p
         (curve-point-affine-coordinates a) bc right))
   (equal (curve-point-fix left) (curve-point-fix right)))
  :hints (("Goal" :use
           curve-point-addition-relation-associative-when-both-inner-opposite-y
           :in-theory (theory 'minimal-theory))))

(defthm relation-both-inner-doubling-client-regression
  (implies
   (and (curve-point-addition-relation-p a b ab)
        (curve-point-addition-relation-p b c bc)
        (curve-point-addition-relation-p ab c left)
        (curve-point-addition-relation-p a bc right)
        (equal (curve-point-fix a) (curve-point-fix b))
        (equal (curve-point-fix b) (curve-point-fix c)))
   (equal (curve-point-fix left) (curve-point-fix right)))
  :hints (("Goal" :use
           curve-point-addition-relation-associative-when-both-inner-doubling
           :in-theory (theory 'minimal-theory))))

(defthm relation-first-original-infinity-client-regression
  (implies
   (and (curve-point-addition-relation-p a b ab)
        (curve-point-addition-relation-p b c bc)
        (curve-point-addition-relation-p ab c left)
        (curve-point-addition-relation-p a bc right)
        (equal (curve-point-fix a) (curve-point-infinity)))
   (equal (curve-point-fix left) (curve-point-fix right)))
  :hints (("Goal" :use
           curve-point-addition-relation-associative-when-original-infinity
           :in-theory (theory 'minimal-theory))))

(defthm relation-second-original-infinity-client-regression
  (implies
   (and (curve-point-addition-relation-p a b ab)
        (curve-point-addition-relation-p b c bc)
        (curve-point-addition-relation-p ab c left)
        (curve-point-addition-relation-p a bc right)
        (equal (curve-point-fix b) (curve-point-infinity)))
   (equal (curve-point-fix left) (curve-point-fix right)))
  :hints (("Goal" :use
           curve-point-addition-relation-associative-when-original-infinity
           :in-theory (theory 'minimal-theory))))

(defthm relation-third-original-infinity-client-regression
  (implies
   (and (curve-point-addition-relation-p a b ab)
        (curve-point-addition-relation-p b c bc)
        (curve-point-addition-relation-p ab c left)
        (curve-point-addition-relation-p a bc right)
        (equal (curve-point-fix c) (curve-point-infinity)))
   (equal (curve-point-fix left) (curve-point-fix right)))
  :hints (("Goal" :use
           curve-point-addition-relation-associative-when-original-infinity
           :in-theory (theory 'minimal-theory))))
