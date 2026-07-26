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

The generic polynomial layer is certified through arithmetic, evaluation,
degree, recursive division, canonical remainder and congruence, reduced
representative operations, GCD, XGCD, modular inverse, logical irreducibility,
the irreducibility-to-monic-GCD-one bridge, and two-sided reduced inverse laws
under irreducibility and a nonzero representative.

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
instance; universal inverse laws, remaining field packaging, finite
enumeration/cardinality, and Frobenius remain open.

## Quotient architecture

Two quotient uses must remain distinct:

* Quotients by certified irreducible polynomials provide coefficient fields.
* General polynomial quotients provide Schoof coordinate rings; their moduli
  need not be irreducible and the rings need not be fields.

F7X2 is a proving ground for the first use, not the intended final general
architecture. No reusable quotient-field constructor is currently certified.
After the minimal F7X2 field interface is complete, development must pause to
extract or design the reusable irreducible-quotient-field pattern before
multiplying presentation-specific instances.

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
