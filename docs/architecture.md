# Architecture

## Pinned foundation

ACL2 is pinned by `ACL2_VERSION` to official release tag **8.6** and built with
SBCL. We include Community Book
`kestrel/prime-fields/prime-fields` (package `PFIELD`) and reuse
`PFIELD::FEP`, `PFIELD::ADD`, `PFIELD::MUL`, and their certified rules. No second
modular arithmetic layer is introduced. The package book is the independently
certifiable import boundary. Bootstrap books remain in package `ACL2` and retain
explicit `PFIELD::` qualification; a separate project package will only be
introduced with a proper ACL2 portcullis.

## Representations and layers

Polynomials are true lists `(c0 ... cn)` in ascending degree order, so `c0` is
the constant coefficient and the high-degree coefficient is at the end. The
coefficients are elements recognized by `PFIELD::FEP`. `nil` is the only
canonical representation of the zero polynomial; every other canonical
polynomial has a nonzero final coefficient. Normalisation removes exactly the
redundant zero coefficients at the high-degree end, returning `nil` when every
coefficient is zero. This canonical form is needed so that structural equality
agrees with coefficient equality and so later degree theorems do not depend on
irrelevant trailing zeroes. Rational functions will be normalized numerator/denominator
pairs over these polynomials, with a nonzero denominator and an explicit
cross-multiplication equivalence before a canonical gcd layer is attempted.

The intended Hasse stack is: field polynomials; rational functions; valuation
at infinity; a generic quadratic twist; Frobenius and scalar multiplication;
the quadratic degree sequence; point-count/separability bridges; and the
integer quadratic argument. Schoof will then add division polynomials,
coordinate quotient rings, trace residues modulo small primes, and CRT
reconstruction.
