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
next narrow boundary is only `x3 = slope^2 - x_first - x_second`; it must stop
before `y3` or an output point.
