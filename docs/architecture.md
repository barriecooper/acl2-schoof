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

A separate additive-only constrained interface defines total natural repeated
addition and directly certifies that two and three copies of field one are
nonzero.  These independent facts, rather than a nonminimal annihilator, form
the characteristic-not-2-or-3 boundary needed by the initial short-Weierstrass
scope.  No mathematical characteristic value, leastness, primality,
cardinality, enumeration, prime-power, or extension-degree metadata is
certified.  F7 and a regression-local modulus-11 client validate transport.

The generic curve layer begins with only two constrained nullary short-
Weierstrass coefficients.  Coefficients and arbitrary coordinates are fixed at
every use by the existing GFIELD fixer; the transparent right-hand side and
coordinate predicate therefore have total canonical semantics.  The layer
adopts nonzeroness of `4*a^3 + 27*b^2` as its non-rewriting certificate and
depends on the existing characteristic-not-2-or-3 book.  The F11 golden values
`a=1`, `b=6` validate the concrete boundary.  This is not a point
representation, group law, formal discriminant theory, or smoothness theorem.

Finite affine coordinates use the transparent proper list `(x y)`, with both
entries passed through the field fixer.  Atoms, dotted pairs, and proper lists
whose length is not two all denote canonical `(0 0)`; entries in an exact
two-list are independently field-fixed.  Fixing is total and idempotent but
says nothing about curve membership.  The separate recognizer is exactly the
existing short-Weierstrass equation on the fixed accessors.  F11 validates
`(2,4)`, `(2,5)`, and noncanonical `(13,15)`.

Full points are exactly canonical `(:infinity)` or `(:affine coordinates)`
proper lists, with the existing canonical affine payload.  Exact affine outer
shapes fix their two-coordinate payload; malformed payloads, unknown tags,
atoms, wrong-length lists, and dotted values fix to `(:infinity)`.  The total
affine accessor returns `(0 0)` outside an affine branch, without claiming it
is on the curve.  Structural fixed-point recognition is separate from
mathematical recognition, which accepts infinity unconditionally or tests the
affine equation.  Off-curve affine branches therefore remain affine.  F11
validates both branches and malformed behavior.  No curve operation, group
law, Frobenius, or counting machinery is added.

Point negation is defined directly at the full-point layer, without a public
affine helper.  It applies `curve-point-fix`, leaves infinity unchanged, and
maps affine `(x,y)` to `(x,-y)` with existing field negation.  Noncanonical
coordinates are fixed and malformed points retain the infinity fallback.
Certification gives structural closure, double negation equal to the fixed
input, literal involution for canonical inputs, and curve-membership closure
from `(-y)^2=y^2`.  It adds no addition, doubling, scalar multiplication, group
law, Frobenius, enumeration, counting, Hasse, or Schoof machinery.

The generic field layer exposes the non-rewriting
`FIELD-EQUAL-SQUARES-IMPLIES-EQUAL-OR-NEG` theorem under total fixing semantics.
Its non-rewriting zero-product support follows from the existing inverse and
multiplication-cancellation laws. Local difference-of-squares and zero-factor
translation lemmas avoid broad public algebra rewrites. No characteristic
assumption is used, and neither `FIELD-EQUIV`, field operations, nor execution
boundaries change.

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

## Affine exceptional-case classification

The semantic curve client of the structural classifier proves one public,
non-rewriting theorem: two inputs satisfying the same constrained
`short-weierstrass-affine-point-p` equation cannot be `:same-x-other`. No
explicit equal-x hypothesis is needed because the classifier characterization
supplies it. Equal x makes the common curve right-hand sides identical, hence
the y squares equal; generic equal-squares theory then gives equal or opposite
y. No nonsingularity or characteristic restriction is used. The alternatives
may overlap for self-inverse y, and an identical self-inverse pair remains
`:opposite-y` by priority. Off-curve and malformed inputs retain fixing
semantics, classifier symmetry remains deferred, and no slope, division,
addition, doubling, scalar multiplication, or group law is added.

The structural classifier also exports the non-rewriting theorem
`affine-pair-classify-distinct-x-implies-x-difference-nonzero`. It chooses
`x_second - x_first`, matching the conventional ordered future secant quotient,
and needs no curve-membership hypothesis. The non-rewriting generic field
theorem `field-sub-equal-zero-implies-fixed-equal` supplies the additive
contrapositive: zero subtraction equates fixed representatives, not arbitrary
raw ACL2 objects. Fixed accessors therefore cover noncanonical entries, while
malformed outer inputs retain the affine fixer's `(0 0)` fallback. Focused F11
executions cover both pair orders, distinct and equal fixed representatives,
noncanonical inputs, and off-curve inputs. No inverse is used and no slope or
addition operation is introduced.

Before any slope or addition operation, the affine-coordinate layer classifies
two arbitrary objects after applying `affine-coordinates-fix` to both. The
canonical keyword result is selected by distinct x first, then opposite y,
then equal y, with `:same-x-other` as the total fallback. Thus an identical
pair satisfying `y=-y` is deliberately `:opposite-y`, not
`:same-point-non-opposite`. This structural boundary is independent of curve
coefficients and membership; malformed inputs inherit the existing `(0 0)`
fallback. No fixing-induced equivalence, infinity dispatcher, slope, division,
or addition boundary is introduced.
