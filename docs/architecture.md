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

Polynomial addition has two deliberately separate layers. `POLY-ADD-RAW`
performs structurally recursive coefficientwise `PFIELD::ADD`, treating absent
higher coefficients as zero by copying the remainder of the longer list.
`POLY-ADD` normalises that raw list.  This final step is necessary because field
addition can cancel the leading coefficients and otherwise leave redundant
high-degree zeroes.  Closure and evaluation results assume coefficient lists
whose entries satisfy `PFIELD::FEP` and a positive field modulus; no broader
ring interface is introduced.

The generic GPOLY layer also provides scalar-first coefficientwise scaling.
Its raw traversal uses the GFIELD multiplication and the established total
fixers; its public operation alone removes trailing zeroes.  Raw evaluation is
proved first and evaluation preservation under normalization then yields the
canonical semantic theorem.  Ordinary executable F_7 definitions share the
transparent two-`DEFUN` template, and their semantic bridge is transported by
functional instantiation through the certified PFIELD adapter.

The intended Hasse stack is: field polynomials; rational functions; valuation
at infinity; a generic quadratic twist; Frobenius and scalar multiplication;
the quadratic degree sequence; point-count/separability bridges; and the
integer quadratic argument. Schoof will then add division polynomials,
coordinate quotient rings, trace residues modulo small primes, and CRT
reconstruction.

Polynomial multiplication likewise has raw and canonical layers.  With the
constant coefficient first, `POLY-MUL-RAW` splits the left operand as
`(a . rest)`, scales every coefficient of the right operand by `a`, and adds
that list to a zero-prefixed recursive product of `rest`.  This is ordinary
coefficient convolution: prefixing zero shifts the recursive contribution up
one degree.  `POLY-SCALE-RAW`, `POLY-ADD-RAW`, and all coefficient arithmetic
use explicitly qualified `PFIELD::MUL` and `PFIELD::ADD` operations.

`POLY-MUL` normalises the raw convolution because zero coefficients at the
high-degree end can be inherited from a noncanonical operand or produced by
field arithmetic.  Thus `nil` remains the sole canonical zero, while
`POLY-ONE` is `(1)`, the canonical constant polynomial one.  Certification now
covers closure, zero and one laws, commutativity, associativity,
distributivity over canonical addition, compatibility with normalisation, and
the homomorphism from polynomial multiplication to `PFIELD::MUL` under Horner
evaluation.  Degree arithmetic, leading coefficients, division, gcds,
derivatives, rational functions, and elliptic-curve constructions remain
separate later milestones rather than being anticipated by a broad algebra
hierarchy here.
