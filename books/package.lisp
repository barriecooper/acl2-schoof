(in-package "ACL2")
(defpkg "HS"
  (append '(pfield::add pfield::mul pfield::neg pfield::fep)
          *acl2-exports*))
