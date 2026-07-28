# ACL2 Hasse--Schoof

ACL2 Hasse--Schoof is a certified foundation for two developments over a shared
algebraic kernel: a future Manin-style proof of Hasse's theorem and an
executable Schoof point-counting implementation. Neither development is
complete. Their initial curve scope is short Weierstrass curves in
characteristic greater than three.

## Current snapshot

The certified generic (`GFIELD`/`GPOLY`) layer provides a field interface and
canonical dense polynomials with arithmetic, evaluation, powers, degree and
leading-coefficient theory, recursive quotient/remainder, modular reduction
and congruence, reduced representative operations, Euclidean GCD, XGCD,
modular inverse, a logical irreducibility predicate, the
irreducibility-to-monic-GCD-one bridge, and two-sided inverse laws for nonzero
classes modulo an irreducible polynomial. The reusable
`FIXED-MODULUS-FIELD-*` interface packages that stack over a constrained
nullary irreducible modulus as transparent total field operations on canonical
remainder representatives.

The public generated field-power correspondence is complete, and the generic
field layer now has a minimal certificate for a positive Frobenius exponent
satisfying the unconditional fixed-representative equation `x^q=x`. F7 and a
regression-local modulus-11 power validate that interface. The exponent is not
yet certified as a field cardinality.

The generic field prerequisites now certify directly that two and three
copies of the fixed field one are nonzero.  This is the characteristic-not-2-or-3
boundary required by the initial short-Weierstrass scope.  F7 and a
regression-local modulus-11 client validate functional-instance transport; no
mathematical characteristic value or leastness theorem is claimed.

The first generic curve boundary now fixes two constrained coefficients at
every use, defines the total short-Weierstrass right-hand side and coordinate
equation, and assumes the standard nonzero `4*a^3 + 27*b^2` expression.  The
existing F11 golden coefficients validate the executable boundary.  A separate
finite-affine boundary uses canonical two-item lists, maps malformed outer
values to the zero-coordinate pair, and recognizes equation satisfaction
without manufacturing an on-curve point.  Full points now use the distinct
tagged value `(:infinity)` or `(:affine (x y))`, reusing affine fixing and
separating structural recognition from curve membership.  Full-point negation
now transparently maps infinity to itself and `(x,y)` to `(x,-y)` after point
fixing.  It preserves representation and curve membership, and double negation
returns the fixed input (literally the input when canonical).  No group
operation or general discriminant/smoothness theory is present.

The affine representation layer also provides a transparent total classifier
for two fixed coordinate pairs. It returns exactly one of `:distinct-x`,
`:opposite-y`, `:same-point-non-opposite`, and `:same-x-other`; opposite y is
tested before coordinate equality so an identical self-inverse pair enters the
opposite-y case. The classifier is structural, includes off-curve and
malformed inputs through affine fixing, and defines no slope or addition.
The equal, non-opposite branch certifies that the exact tangent
denominator `y_first+y_first` is nonzero, using only structural classification
and generic additive-inverse uniqueness.  The transparent total unary
`affine-same-point-non-opposite-slope` computes exactly
`(3*x_first^2+a)/(y_first+y_first)`, with field closure and fixing everywhere
and conditional right-denominator reconstruction under that classifier result.
Its F11 execution checks the on-curve point `(2,4)`: numerator 2, denominator
8, inverse 7, and slope 3.  The transparent total unary
`affine-same-point-non-opposite-output-x` reuses that slope and computes
`m*m-(1+1)*x_first`; it is field-valued and fixed without a classifier
hypothesis, and F11 checks slope/square/doubled-x/output values 3/9/4/5.
The corresponding transparent unary output-y scalar reuses the slope and
output-x operations and computes exactly `m*(x_first-x3)-y_first`; it is likewise
total, field-valued, and fixed, and F11 checks difference/product/output values
8/2/9.  The parallel bindings preserve the established compositional style,
although output x recomputes the slope internally.  The transparent unary
`affine-same-point-non-opposite-output` assembles those scalar results in
x-then-y order with `affine-coordinates-make`; unconditional recognition,
projection, and fixer theorems establish only canonical representation.  F11
checks the assembled `(5 9)` result at `(2,4)`.  Execution outside the selected
branch is only total field programming semantics, not a geometric tangent or
doubling claim.  No tagged doubled point, dispatcher, general addition, closure
theorem, addition or doubling specification, or group-law theorem is defined.

The generic field layer also certifies that equal squares have equal fixed
representatives or fixed representatives related by `FIELD-NEG`. The proof has
no characteristic restriction and remains valid in characteristic two.
The generic curve layer uses that result to exclude `:same-x-other` for two
affine points satisfying the same constrained short-Weierstrass equation; the
total classifier remains unchanged and retains that result off curve.
Classification as `:distinct-x` now also certifies, without curve membership,
that the ordered difference `x_second - x_first` is nonzero.  The transparent
total `affine-distinct-x-slope` is the conventional ordered quotient
`(y_second-y_first)/(x_second-x_first)`, and its non-rewriting reconstruction
theorem multiplies the slope by that denominator on the right.  F11 executions
cover canonical, noncanonical, malformed, and equal-x inputs; equal-x division
by zero returns zero by total programming semantics and is not a secant claim.
The transparent total boundary `affine-distinct-x-output-x` squares that
slope by direct self-multiplication and computes the left-associated formula
`(slope^2-x_first)-x_second`.  It is field-valued and fixed without a classifier
hypothesis. Its non-rewriting rearrangement theorem proves the unconditional
total identity `x3+x_first+x_second = slope^2`; F11 checks canonical,
noncanonical, malformed, and equal-x total executions. The following transparent
total boundary,
`affine-distinct-x-output-y`, reuses both certified scalar operations and
computes `slope*(x_first-x3)-y_first`; it too is field-valued and fixed without
a classifier hypothesis.  Its non-rewriting rearrangement theorem proves the
unconditional total identity `y3+y_first = slope*(x_first-x3)`. Focused F11
executions include every intermediate,
noncanonical and malformed fixing, and equal-x total programming semantics.
`affine-distinct-x-output` now assembles those closed scalar dependencies, in
x-then-y order, with `affine-coordinates-make`. Its parallel bindings and the
existing scalar fixed-result theorems yield a canonical proper two-list, public
x/y projection equations, and fixer stability on all ACL2 inputs. The F11
substitution reuses the named F11 scalar outputs and checks `(0 0)`, `(9 5)`,
`(6 10)`, noncanonical `(0 0)`, malformed-input `(1 9)`, and equal-x total
programming result `(7 7)`. Canonical representation is not curve membership.
The two scalar rearrangement identities now feed the non-rewriting generic
`affine-distinct-x-secant-identity`, which derives
`slope*(y_first-y3) = x3^2+x3*x_first+x_first^2+a` from both input curve
equations and `:distinct-x`. This proof-only intermediate introduces no new
operation.  The generic closure theorem combines it with the output-y
rearrangement, the first input equation, and the assembled output projections
to certify that the existing untagged output lies on the curve.  Both inputs
must lie on the curve and classify as `:distinct-x`.  The transparent
`affine-distinct-x-output-point` wrapper now passes that canonical output to the
established affine full-point constructor.  It is always a structurally valid
affine-tagged point, exposes the assembled coordinates through the existing
accessor, and satisfies the full curve-point predicate under exactly those
three closure hypotheses.  A focused F11 substitution checks the tagged
representation and total malformed/equal-x behavior.  No classifier dispatch,
addition, other classifier branch, or group law is defined.

Named executable prime-field instances include F2, F7, and F11. The concrete F7
polynomial stack includes guard-verified recursive division, raw and monic GCD,
raw and monic XGCD, and modular inverse, with exact execution regressions. The
polynomial `x^2+1` is certified irreducible over F7. A dedicated F7 regression
book checks simultaneous functional instantiation and total boundary behavior;
it does not introduce a public F7 quotient-field API.

F7X2 is the current concrete proving ground for `F7[x]/(x^2+1)`. It has a
canonical representative fixer, transparent guard-verified addition,
negation, subtraction, and multiplication, coefficient formulas, distinct
zero and one, additive laws and cancellation, multiplicative identities and
zero laws, multiplication associativity and commutativity, and both
distributive laws. A regression-prefixed theorem certifies its unchanged
nonzero inverse through the generic fixed-modulus interface, but ordinary
public inverse theorem promotion, formal GFIELD packaging,
enumeration/cardinality, and Frobenius remain open. F7X2 is not
the reusable field constructor: the generic fixed-modulus field is now that
certified boundary. F7X2 migration and its remaining field-specific work remain
separate.

`docs/obligations.md` is the sole detailed status ledger. In particular, an
executable definition, verified guards, an exact execution regression, and a
semantic correctness theorem are distinct kinds of evidence.

## Roadmap and scope

The common algebraic kernel supports both Hasse and Schoof. After shared field,
polynomial, curve, and Frobenius prerequisites, the Manin-style Hasse proof and
the executable Schoof development are parallel tracks; completing Hasse is not
an implementation prerequisite for Schoof.

The executable Schoof track still requires reusable quotient-coordinate
arithmetic, Frobenius, division polynomials, trace testing, and bounded,
incremental CRT. Practical execution evidence and benchmarks are acceptance
evidence distinct from certified logical correctness. See
`docs/proof-plan.md` for the forward plan and `docs/obligations.md` for exact
proved, open, and postponed items.

## Reproduce

On Debian/Ubuntu install `git make perl sbcl`, then run:

```sh
make setup
make check-trust
make certify-one BOOK=books/polynomial/base.lisp
make test
make certify
```

Setup installs ACL2 8.6 under ignored `.deps/`, builds it with SBCL, and uses
that checkout's Community Books and `books/build/cert.pl`. Complete
certification logs live in `.deps/logs/`; initial setup requires network access
and substantial disk space.

With Docker:

```sh
docker build -t acl2-schoof .
docker run --rm acl2-schoof
```

`books/` contains project books, `tests/` executable certification tests,
`scripts/` the reproducible driver, and `docs/` design records and the proof
ledger. The zero polynomial is `nil`; coefficients are stored in ascending
degree and canonical inputs have no trailing zero. The trust policy forbids
proof bypasses, axioms, trust tags, and raw Lisp.

## Polynomial architecture

GPOLY is authoritative for new polynomial algebra. HS/PFIELD polynomials remain
a legacy/root-count bridge unless a specific bridge requires them. New GCD,
derivative, quotient, and extension-field work must not be duplicated across
both stacks. A named prime field may support the first executable Schoof path;
arbitrary finite-field execution is a later architectural phase.
