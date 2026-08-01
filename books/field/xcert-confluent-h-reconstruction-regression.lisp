(in-package "GFIELD")
(include-book "xcert-confluent-h-reconstruction")

(local (defthm xcert-confluent-h-factored-client-regression
 (implies
  (and
   (equal (field-mul m (field-add v u))
    (field-add (field-mul z z) (field-add (field-mul z x) (field-add (field-mul x x) c))))
   (equal (field-mul n (field-add v w))
    (field-add (field-mul z z) (field-add (field-mul z h) (field-add (field-mul h h) c))))
   (equal (field-mul k (field-add v v))
    (field-add (field-mul (field-add (field-add (field-one)(field-one))(field-one))
                          (field-mul z z)) c))
   (equal (field-mul m (field-sub z x)) (field-sub v u))
   (equal (field-mul n (field-sub z h)) (field-sub v w))
   (equal (field-add (field-add h x) z) (field-mul m m))
   (equal (field-add w u) (field-mul m (field-sub x h))))
  (equal (field-mul (field-sub z x)
   (field-mul (field-sub z h)
    (field-sub (field-mul (field-sub m k)(field-add m n))(field-sub x z))))
   (field-zero)))
 :rule-classes nil :hints (("Goal" :use ((:instance xcert-confluent-h-factored-reconstruction
  (p m)(q n)(tangent k)(xa x)(ya u)(xb z)(yb v)(xp h)(yp w)(a c)))
  :in-theory (theory 'minimal-theory)))))

(local (defthm xcert-confluent-h-scalar-client-regression
 (implies
  (and
   (equal (field-mul m (field-add v u))
    (field-add (field-mul z z) (field-add (field-mul z x) (field-add (field-mul x x) c))))
   (equal (field-mul n (field-add v w))
    (field-add (field-mul z z) (field-add (field-mul z h) (field-add (field-mul h h) c))))
   (equal (field-mul k (field-add v v))
    (field-add (field-mul (field-add (field-add (field-one)(field-one))(field-one))
                          (field-mul z z)) c))
   (equal (field-mul m (field-sub z x)) (field-sub v u))
   (equal (field-mul n (field-sub z h)) (field-sub v w))
   (equal (field-add (field-add h x) z) (field-mul m m))
   (equal (field-add w u) (field-mul m (field-sub x h)))
   (not (equal (field-sub z x)(field-zero)))
   (not (equal (field-sub z h)(field-zero))))
  (equal (field-mul (field-sub m k)(field-add m n))(field-sub x z)))
 :rule-classes nil :hints (("Goal" :use ((:instance xcert-confluent-h-scalar-reconstruction
  (p m)(q n)(tangent k)(xa x)(ya u)(xb z)(yb v)(xp h)(yp w)(a c)))
  :in-theory (theory 'minimal-theory)))))
