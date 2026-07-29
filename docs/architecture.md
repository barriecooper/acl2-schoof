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

The named F11 coefficient runtime also includes transparent total `f11-inv`
and `f11-div`.  Inversion fixes once, returns zero when the fixed input is zero,
and otherwise calls the existing PFIELD inverse at modulus 11; its certified
left-inverse law has the generic fixed-input nonzero hypothesis.  Division is
exactly numerator times inverse of denominator.  Closure, fixing compatibility,
guards, and concrete canonical/noncanonical executions are certified without a
new generic axiom or logical/executable split.

The first classifier-selected generic affine formula is the ordinary DEFUN
`affine-distinct-x-slope(first, second)`.  It is exactly the total `FIELD-DIV`
of `y_second-y_first` by `x_second-x_first`; total accessors supply `(0,0)` for
malformed coordinates and no nonzero guard or classifier branch is embedded in
the definition.  `:distinct-x` supplies the predecessor's exact nonzero
denominator only to the certified, non-rewriting reconstruction theorem.  The
corresponding F11 book substitutes the existing named F11 operations into the
same body for execution regressions; it is not a parallel slope theory.

`affine-distinct-x-output-x(first, second)` is the next ordinary transparent
DEFUN.  A local `slope` binding reuses that certified operation, direct
`FIELD-MUL` self-multiplication represents its square, and two `FIELD-SUB`
calls implement `(slope^2-x_first)-x_second` in that order.  Total fixed
accessors make the result total, field-valued, and fixed with no classifier
test, nonzero guard, or curve hypothesis.  Consequently no decorative
`:distinct-x` theorem is published. Its non-rewriting rearrangement theorem
exposes the unconditional total identity `x3+x_first+x_second = slope^2`,
with the displayed left association matching later scalar-sum consumption. It
adds no executable boundary or curve-closure claim. Its named F11 operation is
the established
direct substitution of concrete operations into the same body, not a parallel
mathematical theory.

`affine-distinct-x-output-y(first, second)` is likewise an ordinary transparent
DEFUN.  One parallel `LET` independently binds the certified slope and output-x
operations, then computes exactly
`FIELD-SUB(FIELD-MUL(slope, FIELD-SUB(x_first, output-x)), y_first)`.
The ordered inner subtraction and final use of the first point's y-coordinate
are explicit.  Total fixed accessors and field operations give guard-`T`,
field-element, and fixed-result semantics on arbitrary inputs, so no classifier
or nonzero test is present.  No classifier restatement theorem is published,
and the non-rewriting rearrangement theorem proves the total,
unconditional identity `y3+y_first = slope*(x_first-x3)` directly from the
transparent definition and generic field addition laws. It introduces no
executable boundary and makes no curve-closure claim. The named F11 operation
is direct substitution into this same body; it is execution evidence rather
than another mathematical theory.

`affine-distinct-x-output(first, second)` is the transparent, total coordinate
assembly boundary. A parallel `LET` independently calls the certified output-x
and output-y operations, in that order, and passes them to the existing
`affine-coordinates-make`; it repeats no scalar arithmetic or redundant fixing.
Scalar fixed-result laws give recognizer closure, exact x/y accessor rules, and
affine-fixer stability without classifier, nonzero, or curve hypotheses. The
direct F11 substitution calls the existing F11 scalar outputs and constructor,
not a competing mathematical implementation. Equal-x and malformed executions
are programming semantics, not curve-membership or point-addition claims.

The proof-only `affine-distinct-x-secant-identity` composes both input curve
equations, the classifier-backed slope reconstruction, and both non-rewriting
scalar rearrangements. It exposes
`slope*(y_first-y3) = x3^2+x3*x_first+x_first^2+a` as one controlled generic
curve interface. Its difference-of-squares, difference-of-cubes, cancellation,
and reassociation support remains local to the book. It adds no operation, F11
mirror, executable boundary, or output curve-membership claim.

The following proof-only `affine-distinct-x-closure` book combines that public
secant identity with the output-y rearrangement, the first input curve equation,
and the assembled output's x/y projections.  Under curve membership of both
inputs and `:distinct-x` classification it certifies the existing untagged
coordinate output with `short-weierstrass-affine-point-p`.  Its elementary
field-algebra bridges remain local.  It introduces no operation, tagged point,
F11 mirror, executable boundary, dispatch, or group-law claim.

`affine-distinct-x-output-point(first, second)` is the next ordinary transparent
DEFUN.  It passes the already canonical coordinate output directly to
`curve-point-affine-coordinates`, so arbitrary inputs always produce an affine
tag and never infinity.  Structural recognition and coordinate projection are
unconditional; full short-Weierstrass curve membership is a separate
non-rewriting theorem under the two input-membership hypotheses and
`:distinct-x`.  The proof is only the existing affine closure theorem plus the
established affine-constructor semantic bridge.  Its named F11 substitution
checks the tagged boundary without defining another mathematical algorithm.

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

For `:same-point-non-opposite`, the structural classifier exports the
non-rewriting theorem that the exact future tangent denominator
`FIELD-ADD(y_first,y_first)` is nonzero.  The existing characterization
supplies that fixed `y_first` is not its own negation, and generic additive-
inverse uniqueness rules out a zero doubled value.  This uses no curve or
characteristic hypothesis.  The unary transparent total operation
`affine-same-point-non-opposite-slope` uses the left-associated field numeral
`((1+1)+1)`, multiplies it on the left by `x_first*x_first`, adds the explicitly
fixed constrained coefficient `a`, and divides by that exact doubled-y
denominator.  Its non-rewriting reconstruction theorem takes the classified
pair as its sole hypothesis and consumes the public denominator theorem.
Malformed, noncanonical, off-curve, wrong-branch, and zero-denominator inputs
retain total field semantics; they are not geometric tangent claims.  The
unary scalar boundary `affine-same-point-non-opposite-output-x` binds that
slope and computes the conventional `m*m-(1+1)*x_first`, using field subtraction
and the left scalar-factor convention.  The parallel-binding unary output-y
boundary reuses the slope and output-x operations and spells the conventional
formula exactly as `m*(x_first-x3)-y_first`, with `FIELD-SUB` at both ordered
subtractions and the slope as the left multiplication operand.  Matching the
distinct-x scalar interface, non-rewriting rearrangement theorems expose the
unconditional total equations `x3+(1+1)*x_first = m*m` and
`y3+y_first = m*(x_first-x3)`.  The field-two factor retains the definition's
left scalar-factor spelling, and both the inner subtraction and multiplication
operand order are unchanged for direct use by later algebra.  No explicit fixes
are needed because the accessors and both component operations are field-valued.
As in distinct-x output y, the independent composition means output x
recomputes its slope; no performance boundary is introduced.  The
unary coordinate constructor then independently binds those public scalar
operations and calls `AFFINE-COORDINATES-MAKE` in x-then-y order.  This matches
the distinct-x binding and evaluation order exactly, with unary arity as the
only structural difference.  The scalar fixed-result theorems make explicit
fixing unnecessary and yield unconditional recognition, exact projections,
and affine-fixer stability.  Thus malformed, noncanonical, off-curve, and
wrong-classifier inputs retain the component operations' total semantics and
produce a canonical pair; neither representation nor guard verification is a
geometric doubling claim.  The proof-only closure book then consumes the tangent
identity and input curve equation without changing this executable operation.

`affine-same-point-non-opposite-output-point(first)` is the corresponding unary,
ordinary transparent tagged boundary.  It passes the existing canonical output
directly to `curve-point-affine-coordinates`; it does not retain `second` because
neither construction nor execution depends on classifier selection.  Structural
recognition and coordinate projection are unconditional.  Its separate binary
semantic theorem retains `second` exactly where needed to select
`:same-point-non-opposite`, and combines that premise and input membership with
the existing untagged closure and affine-constructor membership theorem.  F11
checks the tagged `(2,4) -> (:affine (5 9))` integration and malformed total
execution.  No representation change, new identity, dispatch, infinity handling,
addition or doubling specification, or group-law claim is added.

`affine-opposite-y-output-point(first, second)` is the ordinary transparent
boundary for the already characterized `:opposite-y` classifier result.  Its
body ignores both arbitrary ACL2 inputs and returns the existing
`curve-point-infinity`; binary arity is intentional because branch selection is
relational and a later pair dispatcher will already hold both operands.  Exact
equality with canonical infinity, structural recognition, the infinity
predicate, and full short-Weierstrass membership are unconditional.  They need
no classifier or input-membership hypotheses because infinity is already a
valid full curve point.  The operation remains total on malformed, off-curve,
noncanonical, and wrong-classifier inputs; only a later dispatcher will control
selection.  F11 covers an on-curve opposite pair, the self-inverse fixed `(0,0)`
malformed case, and a wrong-branch call.  No affine accessor theorem, slope,
coordinate arithmetic, classifier change, representation change, dispatcher,
or group-law specification is introduced.

Before any slope or addition operation, the affine-coordinate layer classifies
two arbitrary objects after applying `affine-coordinates-fix` to both. The
canonical keyword result is selected by distinct x first, then opposite y,
then equal y, with `:same-x-other` as the total fallback. Thus an identical
pair satisfying `y=-y` is deliberately `:opposite-y`, not
`:same-point-non-opposite`. This structural boundary is independent of curve
coefficients and membership; malformed inputs inherit the existing `(0 0)`
fallback. No fixing-induced equivalence, infinity dispatcher, slope, division,
or addition boundary is introduced.
