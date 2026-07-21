# Architecture

## Pinned foundation

ACL2 is pinned by `ACL2_VERSION` to official release tag **8.6** and built with
SBCL. We include Community Book
`kestrel/prime-fields/prime-fields` (package `PFIELD`) and reuse
`PFIELD::FEP`, `PFIELD::ADD`, `PFIELD::MUL`, and their certified rules. No second
modular arithmetic layer is introduced. The package book is the independently
certifiable import boundary.

## Package portcullis and imports

`books/package.acl2` is the companion pre-certification file recognized by
ACL2 8.6 `books/build/cert.pl`. It runs `DEFPKG` before `package.lisp` is
certified, and `cert.pl` records the command in `package.port`. Before certifying
an including book, the build system loads that portcullis, so the book can begin
with `(in-package "HS")`. This follows the ACL2 8.6 Community Books pattern in
`centaur/svl/portcullis.acl2` and the `BUILD::PRE-CERTIFY-BOOK-COMMANDS`
documentation in `books/build/doc.lisp`.

The `HS` import list is explicit and limited to ACL2/Common Lisp syntax and
utilities used by current project books. No `PFIELD` symbol is imported. Field
operations remain visibly qualified (`PFIELD::FEP`, `PFIELD::ADD`, and
`PFIELD::MUL`) to keep the boundary auditable and avoid collisions.

## Current include graph

* `package.lisp` includes the system prime-field book.
* `polynomial/base.lisp` includes `package.lisp`.
* `polynomial/eval.lisp` includes `base.lisp` and the system modular-arithmetic
  rules needed by its evaluation theorem.
* `polynomial/degree.lisp` includes `eval.lisp`.
* `top.lisp` includes `polynomial/degree.lisp`.
* `tests/smoke.lisp` includes `top.lisp`.

## Representations and layers

Polynomials are true lists `(c0 ... cn)` in ascending degree order. `nil` is the
only zero polynomial; every other canonical polynomial has field elements as
coefficients and a nonzero final coefficient. Normalisation removes trailing
integer zeroes. Rational functions will be normalized numerator/denominator
pairs over these polynomials, with a nonzero denominator and an explicit
cross-multiplication equivalence before a canonical gcd layer is attempted.

The intended Hasse stack is: field polynomials; rational functions; valuation
at infinity; a generic quadratic twist; Frobenius and scalar multiplication;
the quadratic degree sequence; point-count/separability bridges; and the
integer quadratic argument. Schoof will then add division polynomials,
coordinate quotient rings, trace residues modulo small primes, and CRT
reconstruction.
