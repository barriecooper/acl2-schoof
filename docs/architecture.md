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
Its generic reduced-product laws now return `POLY-REDUCED-ONE` in both
orientations under the exact monic-GCD-one condition, with no degree or
irreducibility hypothesis.  Literal polynomial-one correctness still requires
a nonempty normalized positive-degree modulus; constant moduli retain their
trivial-ring zero-remainder semantics.

The narrowly downstream `irreducible-modular-inverse` book now composes those
layers: irreducibility plus an explicit nonzero representative fixed by
`POLY-REMAINDER` yields both `POLY-REDUCED-MUL` unit laws. The candidate remains
the transparent XGCD-derived `POLY-MODULAR-INVERSE`; no inverse algorithm,
quotient object, or executable boundary was added. The certified F7 examples
for `x^2+1` are regression witnesses only, not an implementation of
`F7[x]/(x^2+1)` as a field.  The presentation-specific `F7X2` boundary now
completes its canonical carrier representation: every recognized element is a
normalized constant-first F7 polynomial of degree below two, fixed by the
existing remainder modulo `(1 0 1)`, and is reconstructible uniquely from its
constant and linear F7 coefficients.  Equality of recognized carrier elements
is ordinary ACL2 equality and is coefficient-extensional; arbitrary ACL2 inputs
must first pass through `F7X2-FIX` before those projections compare their
canonical representatives.  This is not a quotient-equivalence-class object,
and its downstream arithmetic book adds only transparent reduced addition, negation, subtraction, and multiplication.  These operations compute with the existing F7 polynomial arithmetic and then pass through `F7X2-FIX`; certified per-operand compatibility proves that fixing any operand first leaves the result unchanged, even for arbitrary malformed or noncanonical ACL2 objects. Equality of canonical results remains ordinary ACL2 equality.  The multiplication boundary is intended to expose `(a+bx)(c+dx) = (ac-bd) + (ad+bc)x` in later field-law proofs; its coefficient projection formulas remain open.  No inverse, complete field-law package, elliptic-curve arithmetic, or `GFIELD` instance is introduced.
Irreducibility and modular-inverse certificates remain downstream facts for
later field promotion.

## Subsequent algebraic layers

The next algebraic layers deliberately separate two constructions:

* Quotient fields modulo certified irreducible polynomials provide
  coefficient-field extensions.
* General polynomial quotient rings provide the coordinate algebra used in
  Schoof torsion and division-polynomial calculations. Their moduli need not be
  irreducible.

The concrete dependency audit after the certified F7 monic GCD is recorded in
`f7-extension-field-reconnaissance.md`.  Generic raw/monic XGCD and modular
inverse are already certified; the smallest next implementation is therefore
the transparent **concrete F7 raw XGCD instance**, now certified with exact raw-GCD and unconditional Bezout interfaces.  Concrete raw and monic XGCD are certified. The concrete F7 modular-inverse layer now transparently reduces the first monic-XGCD coefficient through the retained remainder path. It is total, but its inverse certificate explicitly requires monic GCD one; later residue-ring code must distinguish this unit condition from field inversion supplied only by irreducibility or another unit guarantee. No claim is made that reducible Schoof division-polynomial quotients are fields.

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
