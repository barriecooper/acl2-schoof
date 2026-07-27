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

The generic field layer also certifies that equal squares have equal fixed
representatives or fixed representatives related by `FIELD-NEG`. The proof has
no characteristic restriction and remains valid in characteristic two.
The generic curve layer uses that result to exclude `:same-x-other` for two
affine points satisfying the same constrained short-Weierstrass equation; the
total classifier remains unchanged and retains that result off curve.

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
