# Proof plan

This document is forward-looking. Exact item-by-item status belongs only in
`obligations.md`; certified interfaces are summarized here only to establish
the starting boundary.

## Starting boundary

The shared generic field/polynomial kernel is certified through recursive
division, reduced representative arithmetic, GCD, XGCD, modular inverse,
logical irreducibility, the irreducibility-to-monic-GCD-one bridge, and
irreducible-modulus inverse laws. The concrete F7 stack carries those
algorithms through guard-verified modular inverse with exact execution
regressions, and `x^2+1` is certified irreducible over F7. A reusable
fixed-modulus field interface now packages canonical remainder representatives
and the complete GFIELD-shaped contract over a constrained nullary irreducible
modulus; an F7 regression simultaneously instantiates the coefficient field,
polynomial stack, modulus, and wrappers. A proof-only F7X2 regression also
simultaneously maps that complete stack and all nine existing F7X2 definitions
to the generic interface without changing their execution or public API.

F7X2 currently supplies canonical representatives, transparent
addition/negation/subtraction/multiplication, and a total executable inverse
candidate with an explicit zero branch. Its certified laws include
zero/one distinctness, the additive group laws and cancellation,
multiplicative identities and zero, associativity and commutativity of
multiplication, and distributivity. The generic nonzero inverse law is certified
for the unchanged operations under a regression-prefixed compatibility theorem,
but ordinary public F7X2 inverse theorems and formal field packaging remain
open; this is not yet a public field interface.

## Near-term shared algebra

1. The generated public field-power correspondence and the first narrow
   finite-field certificate are complete: a positive Frobenius exponent whose
   public q-power fixes every field representative. F7 and regression-local
   modulus 11 validate the interface; it does not certify cardinality,
   characteristic, prime-power metadata, or completeness of finite-field data.
2. The characteristic-not-2-or-3 prerequisite is complete: two and three
   copies of fixed field one are certified nonzero through total natural
   repeated addition.  No characteristic value or leastness theorem is
   introduced.  Enumeration/cardinality and prime-power metadata remain
   separate open interfaces.
3. The minimal short-Weierstrass parameter boundary is complete: two fixed-at-
   use coefficients, the total affine coordinate equation, and the adopted
   nonzero `4*a^3 + 27*b^2` certificate.  F11 validates the golden coefficients
   and total execution.  A separate point representation and all group
   operations remain open; characteristics two and three remain excluded by
   the preceding certified facts.
4. The finite affine-coordinate boundary is complete: canonical proper
   two-item lists contain field-fixed coordinates; malformed outer objects
   denote the zero-coordinate pair; and the affine recognizer applies the
   existing equation to the fixed accessors.  Fixing establishes representation
   only, not curve membership.
5. The minimal full-point representation is complete: `(:infinity)` is the
   unique infinity value and `(:affine coordinates)` reuses fixed affine
   coordinates.  Malformed outer values fix to infinity; off-curve affine
   values stay affine and fail only the separate curve-membership predicate.
   No curve operation or group law is included.
6. Full-point negation is complete.  It fixes infinity, negates only the fixed
   affine y-coordinate, preserves representation and curve membership by
   `(-y)^2=y^2`, and is involutive modulo point fixing.  No affine helper or
   fixing-induced point equivalence was needed.

General polynomial quotients used for Schoof coordinates are distinct from
irreducible quotients promoted to coefficient fields: their moduli need not be
irreducible.

## Parallel tracks after shared prerequisites

The common algebraic kernel supports both developments. Once the shared finite
field, polynomial, curve, and Frobenius prerequisites exist, proceed in
parallel:

### Manin-style Hasse track

Develop rational-function and valuation-at-infinity machinery, curve
endomorphisms and degree, Frobenius/scalar-map relations, kernel/fibre and
separability results, the point-count connection, and the integer quadratic
conclusion yielding Hasse's bound.

### Executable Schoof track

Develop quotient-coordinate arithmetic, Frobenius reduction, division
polynomials, trace-residue testing, and bounded incremental CRT reconstruction.
Completion of the Hasse proof is not an implementation prerequisite for this
track.

## Evidence and acceptance criteria

Certification establishes logical claims. Guard verification establishes that
an executable branch is admissible for its guard. Exact regressions establish
selected concrete behavior. None of these alone establishes practical
performance.

Before claiming a practical Schoof implementation, measure compiled ACL2
execution; polynomial remainder and modular-power workloads; normalization and
allocation costs in hot loops; quotient multiplication and Frobenius;
division-polynomial scaling as `ell` grows; incremental CRT; and end-to-end
results against direct point enumeration on small fields. These are future
acceptance criteria, not current certified achievements. Detailed performance
items are tracked in `obligations.md`.

## Historical records

Older audit and reconnaissance documents preserve design evidence and the
sequence appropriate at the revision when they were written. Their “next PR”
or proposed-sequence sections are historical unless restated above. They do
not override this plan or the status ledger.

## Next affine boundary

The affine exceptional-case classifier is complete as a four-way structural
boundary. After affine fixing it distinguishes distinct x, opposite y, equal
non-opposite coordinates, and the remaining same-x case, in that order. The
remaining case is intentionally retained for arbitrary and off-curve inputs.
Slopes and addition remain open.

The generic algebra and curve client needed to refine the remaining case are
complete: equal curve right-hand sides give equal y squares, and equal field
squares give equal or opposite fixed y representatives. Thus `:same-x-other`
is excluded for genuine same-curve points without an explicit equal-x
hypothesis. The denominator-nonzero boundary for `:distinct-x` is complete:
the classifier characterization and a generic additive zero-difference theorem
show that `x_second - x_first` is nonzero for arbitrary fixed-coordinate
inputs, without curve membership. The chosen orientation anticipates
`(y_second - y_first)/(x_second - x_first)`. The distinct-x secant-slope
boundary is now complete.  The transparent total
formula divides `y_second-y_first` by `x_second-x_first` without a classifier
test or nonzero guard; `:distinct-x` is used only by the non-rewriting
right-denominator reconstruction theorem.  F11 exercises the generic formula's
concrete substitution, including total equal-x and malformed semantics.  The
distinct-x output-x boundary is now complete: the transparent total operation
uses direct slope self-multiplication and left-associated subtraction, with
field closure, fixed-result, verified guards, and focused F11 execution.  No
classifier hypothesis is needed for closure or execution.  The distinct-x
output-y boundary is also complete: its parallel bindings reuse the certified
slope and output-x, and it computes exactly
`slope * (x_first - x3) - y_first`, with closure, fixing, verified guards, and
focused F11 execution.  The canonical coordinate-assembly boundary is now also
complete: `affine-distinct-x-output` uses a parallel `LET` and the established
`affine-coordinates-make` constructor to assemble x3 then y3. Recognition, both
accessor equations, fixer stability, guard verification, and focused F11
execution require no classifier hypothesis. This proves canonical representation
only. Both scalar rearrangement interfaces are now complete: the transparent
definitions and generic additive cancellation prove, unconditionally and
totally, `x3+x_first+x_second = slope^2` and
`y3+y_first = slope*(x_first-x3)`. They add no executable boundary, and no
claim is made that these identities alone prove curve closure. The generic
distinct-x secant identity is now complete: both input curve equations, slope
reconstruction and its classifier-supplied nonzero denominator, and both scalar
rearrangements derive `slope*(y_first-y3) = x3^2+x3*x_first+x_first^2+a`.
This is a proof-only curve-specific intermediate, not output curve membership.
Generic distinct-x curve closure is now complete: the secant identity,
output-y rearrangement, first input curve equation, and assembled output
projections prove that the existing untagged coordinate output satisfies the
affine-point predicate when both inputs are curve points classified as
`:distinct-x`.  This proof-only result adds no executable or F11 boundary.  The
independent `affine-distinct-x-secant-relation-p(first,second,slope,output)` is
now complete. It is a transparent affine-coordinate relation with an explicit
fixed slope witness, visible input/output curve membership and fixed-coordinate
x inequality, and the division-free slope, output-x, and output-y equations.
It contains no classifier or executable operation and is stable under fixing
all arguments. Its non-rewriting soundness theorem uses the existing slope and
coordinate output under the two input curve predicates and x inequality; a
classifier translation remains proof-local. F11 witnesses `(2,4),(3,5)`, slope
1, and output `(7 2)`.  Its uniqueness boundary is now complete through three
non-rewriting theorems: fixed-slope uniqueness from two relation instances,
fixed-output uniqueness from two instances at equal fixed slopes, and their
combined two-hypothesis consequence.  The proof derives the nonzero x
difference internally, cancels it on the right, cancels the two common x
addends, uses output-x equality in the y equations, and reconstructs equality
of affine fixers from accessor equality.  Only three small proof-local field
bridges are added; curve membership and characteristic assumptions do no work
in the algebra. Completeness remains a separate deferred semantic boundary;
full addition and group laws remain deferred. The
tagged distinct-x output boundary is also complete: a transparent wrapper uses
the established affine full-point constructor, is structurally valid and
projects to the canonical assembled output unconditionally, and satisfies the
full curve-point predicate under exactly the same three semantic hypotheses.
Its F11 substitution is execution evidence only.  Addition dispatch, every
other classifier case, and later group-law work remain deferred.

The independent affine doubling semantic boundary is complete.
`affine-doubling-relation-p(input,slope,output)` transparently combines input
and output curve membership, the mathematical domain `y != -y`, and the exact
division-free tangent/output equations.  It is classifier-free,
implementation-free, and stable under all argument fixers.  Under input
membership and that domain, the existing tangent slope and unary output satisfy
the relation through a proof-local classifier adapter.  Two-instance
non-rewriting theorems prove fixed slope uniqueness, fixed output uniqueness,
and their combined result.  The nonzero `y+y` denominator follows internally
from the domain without an extra characteristic premise.  F11 checks the
existing `(2,4)` doubling to `(5,9)` with slope 3.  No broader addition,
completeness, inverse/infinity, or group-law work is included.  Next, audit the
remaining affine inverse and infinity semantic cases required before a full
tagged addition relation.

The denominator-nonzero prerequisite and tangent-slope scalar boundary for the
equal non-opposite branch are now complete.  `:same-point-non-opposite`
supplies the non-self-inverse fixed y-coordinate, and additive-inverse
uniqueness proves that `y_first+y_first` is nonzero without curve-membership or
characteristic hypotheses.  The unary transparent total slope computes
`(((1+1)+1)*(x_first*x_first)+field-fix(a))/(y_first+y_first)`; its conditional
non-rewriting theorem reconstructs that numerator by consuming the public
denominator result and generic division reconstruction.  F11 checks the exact
intermediates at the on-curve point `(2,4)`.  The next scalar boundary is also
complete: unary `affine-same-point-non-opposite-output-x` reuses that slope and
computes exactly `m*m-(1+1)*x_first`, with unconditional field closure and
fixing and focused F11 execution yielding 5.  Unary
`affine-same-point-non-opposite-output-y` is now also complete: parallel
bindings reuse the slope and output-x operations and compute exactly
`m*(x_first-x3)-y_first`, with the same unconditional closure and fixing; F11
execution yields 9.  Their elementary rearrangement interface is also complete:
the unconditional non-rewriting equations are exactly
`x3+(1+1)*x_first = m*m` and `y3+y_first = m*(x_first-x3)`, proved from the
transparent definitions and existing generic field laws.  They add no geometric
or executable claim.  The first substantive tangent bridge is now complete:
under only the `:same-point-non-opposite` classifier hypothesis, tangent
numerator reconstruction and those two rearrangements prove
`m*(y_first-y3) = x3^2+x3*x_first+x_first^2+a`.  This proof-only identity does
not need the input curve equation.  Its separate closure consumer is now
complete: the identity, output-y rearrangement, input curve equation, and
assembled projections prove that the existing untagged unary output lies on
the affine curve under input membership and the same classifier hypothesis.
Output x consequently recomputes the slope internally,
matching the transparent distinct-x composition rather than introducing a
performance refactor.  The unary untagged coordinate constructor is also
complete: it uses parallel x-then-y bindings of those public scalars and the
existing affine constructor, with unconditional recognition, projection, and
fixer stability.  F11 checks `(5 9)` at `(2,4)`.  Total execution outside the
classifier branch is neither tangent nor geometric doubling correctness.  The tagged same-point-non-opposite boundary is also complete: the unary
transparent wrapper uses the established affine full-point constructor, is
structurally valid and projects to the untagged output unconditionally, and is
a full curve point under exactly input membership and binary classifier
selection.  Its focused F11 substitution is execution evidence only.  The exceptional
`:opposite-y` output boundary is now complete as well: a transparent total
binary operation returns canonical infinity, with unconditional exact-result,
representation, infinity, and full curve-membership theorems.  Existing
classifier characterization establishes equal fixed x and opposite fixed y;
its priority includes identical self-inverse y.  F11 checks `(2,4),(2,7)`,
malformed inputs fixed to the self-inverse `(0,0)` case, and total wrong-branch
execution.  The affine-input dispatcher boundary is now complete.  The transparent binary
`affine-pair-output-point` evaluates `affine-pair-classify` once and selects the
three established tagged output operations.  Its final `:same-x-other`/catch-all
case returns canonical infinity only as a total programming convention.  Generic
certification gives unconditional structural recognition and full curve
membership under exactly the two affine-input membership hypotheses; the
existing `affine-pair-classify-not-same-x-other-for-curve-points` theorem removes
the fallback without interpreting it geometrically.  F11 checks all three
reachable branches and the off-curve fallback.  The full tagged-point dispatcher
is now complete: `curve-point-pair-output-point` fixes each operand once,
implements the three infinity identity cases, and delegates its affine/affine
case to the affine dispatcher.  Its four branch equations, fixing congruence,
unconditional representation closure, and conditional full curve-membership
closure are certified; F11 also checks malformed-input fixer behavior.  An
independent addition specification and all group laws remain later mathematical
boundaries.
