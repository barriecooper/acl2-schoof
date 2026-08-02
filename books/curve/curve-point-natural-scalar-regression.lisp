(in-package "GFIELD")

(include-book "curve-point-natural-scalar")

; Client-side generation exercises the public scalar instantiation endpoint.
(def-curve-point-natural-scalar-theorem
  curve-point-natural-scalar-client-sum
  abelian-group-nat-mul-of-sum)
