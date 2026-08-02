(in-package "GFIELD")

(include-book "curve-point-abelian-group")

; A client sees only the packaging book and obtains this consequence through
; its generic functional-instantiation endpoint.
(def-curve-point-abelian-group-theorem
  curve-point-abelian-group-client-inverse-of-identity
  abelian-group-inverse-of-identity)
