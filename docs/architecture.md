# Architecture

## Shared kernel and scope

The authoritative new algebra is the GFIELD/GPOLY stack: a generic field
interface plus canonical dense polynomials and certified algorithms. HS/PFIELD
remains a legacy/root-count bridge unless a specific theorem needs it. The
common kernel is intended to support both a Manin-style Hasse proof and an
executable Schoof development for short Weierstrass curves in characteristic
greater than three.

The two developments share finite-field, polynomial, curve, and Frobenius
prerequisites. After that seam they are parallel tracks. Hasse completion is
not an implementation prerequisite for Schoof.

## Certified layers

The generated public field-power correspondence is certified, and a separate
minimal constrained interface supplies a positive Frobenius exponent with the
unconditional public-power equation `x^q=x` under total fixing semantics. F7
and a regression-local modulus-11 power are mechanics clients. This certificate
does not identify q with cardinality and supplies no enumeration,
characteristic, prime-power, or extension-degree metadata.

The generic polynomial layer is certified through arithmetic, evaluation,
degree, recursive division, canonical remainder and congruence, reduced
representative operations, GCD, XGCD, modular inverse, logical irreducibility,
the irreducibility-to-monic-GCD-one bridge, and two-sided reduced inverse laws
under irreducibility and a nonzero representative.

`generic/fixed-modulus-field.lisp` promotes those results to a reusable field
interface over one constrained nullary irreducible modulus. Its carrier is
literal remainder fixedness, its operations return canonical remainder
representatives, and inverse fixes arbitrary input before its explicit zero
branch. The definitions are ordinary transparent total wrappers.

Named F7 polynomial definitions specialize recursive division, raw and monic
GCD, raw and monic XGCD, and modular inverse. They have verified guards,
semantic theorems, and focused exact executions. The generic quadratic root
criterion and concrete enumeration establish that `x^2+1` is irreducible over
F7.

The presentation-specific F7X2 layer fixes arbitrary ACL2 objects to canonical
representatives modulo `x^2+1`, transparently implements reduced addition,
negation, subtraction, and multiplication, and provides a total executable
inverse candidate with an explicit zero branch. Its certified laws currently
cover zero/one distinctness, additive identities/inverses/associativity/
commutativity and cancellation, multiplicative zero/identity/associativity/
commutativity, and both distributive laws. It is not yet a field or a GFIELD
instance. A proof-only simultaneous functional-instantiation regression now
certifies that the nine unchanged F7X2 definitions satisfy the reusable
fixed-modulus-field interface, including its nonzero inverse law. The ordinary
public F7X2 inverse theorem surface, replacement of bespoke proof bodies, formal
GFIELD client packaging, finite enumeration/cardinality, and Frobenius remain
open.

## Quotient architecture

Two quotient uses must remain distinct:

* Quotients by certified irreducible polynomials provide coefficient fields.
* General polynomial quotients provide Schoof coordinate rings; their moduli
  need not be irreducible and the rings need not be fields.

The reusable fixed-modulus field handles the first use and has an F7
simultaneous-functional-instantiation regression. That regression is not a
public concrete F7 quotient API. A separate F7X2 regression certifies the
existing presentation's simultaneous compatibility without changing its
execution, public definitions, or proof provenance. F7X2 has not been migrated
to the generic interface. The construction
does not apply to the possibly reducible coordinate-ring moduli in the second
use.

## Downstream tracks

The Manin-style Hasse track needs rational-function and valuation machinery,
curve endomorphisms, Frobenius degree and kernel/fibre results, separability,
and the integer quadratic conclusion.

The executable Schoof track needs quotient-coordinate arithmetic, Frobenius,
division polynomials, trace testing, and bounded incremental CRT. A named prime
field may support its first path; arbitrary finite-field execution is a later
architectural phase.

Logical correctness, guard verification, exact execution regressions, and
practical execution evidence are separate claims. Compiled benchmarks and
allocation/normalization measurements are future acceptance evidence, not
certified mathematics. Detailed status is maintained only in
`obligations.md`, and the current sequence is in `proof-plan.md`.
