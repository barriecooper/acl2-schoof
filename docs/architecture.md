# Architecture

## Pinned foundation

ACL2 is pinned by `ACL2_VERSION` to official release tag **8.6** and built with
SBCL. We include Community Book
`kestrel/prime-fields/prime-fields` (package `PFIELD`) and reuse its certified
prime-field rules. The package book is the independently certifiable import
boundary.

## Authoritative polynomial stack

The abstract `GFIELD` kernel and generic `GPOLY` books are the authoritative
architecture for polynomial algebra. `GFIELD` supplies constrained field
operations and laws; `GPOLY` supplies the canonical dense representation and
certified algorithms over those operations. New GCD, reduction, quotient, and
extension developments belong in this stack rather than being duplicated in
the older HS/PFIELD polynomial books.

`PFIELD` remains a constrained-modulus adapter and supports the legacy
root-count bridge; it is not ordinary arithmetic for one named runtime modulus
and is not the principal future implementation route. F7 is a named executable
prime-field instance and a source of certified transported polynomial support.
Its recursive divmod-through-modular-inverse instantiation remains blocked on
the inverse/division guard-contract decision recorded in `obligations.md`. The
F11 books provide the concrete golden-curve fixture.

## Representation and certified algorithms

GPOLY polynomials are true lists `(c0 ... cn)` in ascending degree order, with
the constant coefficient first. `nil` is the sole canonical zero; every other
canonical polynomial has a nonzero final coefficient. Normalization removes
redundant high-degree zero coefficients. Raw operations perform structural
coefficient work using `GFIELD`, while their public canonical operations
normalize the result. The PFIELD adapter is one functional instance of this
architecture.

The certified generic stack includes normalization and evaluation; additive
and multiplicative ring operations; scaling, constants, powers, degree,
leading coefficients, monomials, and shifts; leading-term cancellation;
Euclidean quotient and remainder with reconstruction and degree bounds;
congruence and its additive and multiplicative compatibility; divisibility;
raw Euclidean GCD and monic GCD post-processing; raw XGCD with unconditional
Bezout; monic XGCD with monic Bezout; the XGCD remainder bridge; and the total
`POLY-MODULAR-INVERSE` candidate with its conditional correctness theorem.
Literal-one correctness for that candidate requires a nonempty normalized
positive-degree modulus; constant moduli retain their zero-remainder semantics.

## Subsequent algebraic layers

The next algebraic layers deliberately separate two constructions:

* Quotient fields modulo certified irreducible polynomials provide
  coefficient-field extensions.
* General polynomial quotient rings provide the coordinate algebra used in
  Schoof torsion and division-polynomial calculations. Their moduli need not be
  irreducible.

Neither set of quotient laws is complete. The dependency path first resolves
concrete named-field guards and instantiation, proves that irreducibility
implies monic GCD one, and supplies executable irreducibility certificates for
selected defining polynomials. Quotient fields, general quotient rings, and
extension fields then support the elliptic-curve, Frobenius, torsion, and CRT
layers. Detailed proved, open, and postponed status is maintained only in
`obligations.md`.

The intended Hasse stack is field polynomials; rational functions; valuation at
infinity; a generic quadratic twist; Frobenius and scalar multiplication; the
quadratic degree sequence; point-count and separability bridges; and the
integer quadratic argument. Schoof additionally requires division polynomials,
general coordinate quotient rings, trace residues modulo small primes, and
bounded CRT reconstruction.
