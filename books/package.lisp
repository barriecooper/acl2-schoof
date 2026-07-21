(in-package "ACL2")
(include-book "kestrel/prime-fields/prime-fields" :dir :system)

; The bootstrap books deliberately stay in ACL2's package.  This book is the
; single certifiable import boundary for the PFIELD library; introducing a
; project package later requires a proper portcullis, not an in-book DEFPKG.
