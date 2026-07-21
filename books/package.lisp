(in-package "ACL2")
(include-book "projects/numbers/prime-fields/prime-fields" :dir :system)

; Keep the project package small.  Prime-field operations are intentionally
; referenced with their PFIELD:: qualification in project books.
(defpkg "HS" *acl2-exports*)
