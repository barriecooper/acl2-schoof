(in-package "ACL2")
(include-book "kestrel/prime-fields/prime-fields" :dir :system)

; This book is the single certifiable import boundary for the PFIELD library.
; Its companion package.acl2 creates HS before certification; package.port
; carries that package definition to every book that includes this one.
