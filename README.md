# ACL2 Hasse--Schoof

ACL2 Hasse--Schoof develops certified algebra and elliptic-curve foundations for
a future Manin-style proof of Hasse's theorem and an executable implementation
of Schoof point counting. The initial curve scope is short Weierstrass curves
over fields of characteristic other than two and three. Neither Hasse's theorem
nor Schoof's algorithm is complete.

## Certified scope

The repository currently certifies these subsystem-level foundations:

- an unrestricted-by-characteristic generic field interface (`GFIELD`) with
  total fixing, natural powers, and a Frobenius-exponent assumption, plus an
  explicit curve-level predicate for the initial characteristic-greater-than-
  three short-Weierstrass scope;
- an executable PFIELD finite carrier and exact cardinality grounded in its
  certified exhaustive duplicate-free canonical residue enumeration, with F7
  and F11 specializations (not a generic finite-field cardinality theorem);
- a field-only X-CERT algebra layer with explicit residual generators, an
  output telescope, a factored remainder identity, and their composition, plus
  a curve-semantic specialization for the two ordered nested distinct-x trees;
- canonical dense polynomials (`GPOLY`) with arithmetic, evaluation, formal
  differentiation and its additive laws, degree, division with remainder,
  Euclidean GCD, extended GCD, modular inversion, irreducibility, and reduced
  arithmetic, plus a finite-field-prefixed recursive divmod and public
  remainder/reduced-representative interface, fixed-modulus coefficient vectors, exact-width coefficient-vector mixed-radix rank/unrank, exhaustive representative carriers, and representative-count cardinality for explicit finite-field moduli;
- a generic fixed-modulus quotient-field construction for an irreducible
  polynomial, plus concrete PFIELD/F7 clients and an F7X2 proving instance;
- a certified executable 49-element carrier and exact cardinality for the
  concrete presentation `F7[X]/(X^2+1)`, plus regressions connecting that presentation to the generic fixed-modulus representative-count formula;
- the first division-polynomial client boundary: a complete generic base, recurrence, table, sequence, and evaluator correspondence; explicit functional-instance transport of the bounded base and one-step recurrence to F11; and transparent F11 all-index execution evidence through all three recurrence branches.  F11 generated-table satisfaction, concrete sequence uniqueness, and generic-to-F11 all-index evaluator correspondence remain open;
- short-Weierstrass coordinates, canonical affine coordinates, tagged curve
  points (affine or infinity), and point negation;
- total affine branch classification and executable affine/tagged-point
  dispatchers, with independent semantic relations for the geometric branches
  and for full tagged-point addition; and
- executable output closure, literal left/right infinity identity,
  commutativity, associativity, a transparent point inverse with literal
  left/right inverse laws, and literal left/right cancellation for full
  tagged-point addition; and
- an abstract carrier-based abelian-group interface and a functionally
  instantiated package for valid tagged curve points under
  `short-weierstrass-characteristic-p`.

Concrete F7 and F11 books are focused executable and instantiation regressions.
They demonstrate particular computations; they do not by themselves establish
a generic theorem. The detailed proved/open ledger is
[`docs/obligations.md`](docs/obligations.md), and the current associativity
case matrix is [`docs/status-associativity.md`](docs/status-associativity.md).

The full tagged executable curve-point dispatcher has independently public
closure, identity, commutativity, associativity, inverse, and cancellation laws
for valid curve points.  The generic functional-instance endpoint
`def-curve-point-abelian-group-theorem` packages those points as an abelian
group under the maintained characteristic hypothesis. Natural scalar
multiplication is certified as transparent linear repeated addition; an
optimized scalar algorithm remains open.
There is no certified Hasse theorem, point-count correctness theorem, all-index F11 evaluator adapter, classical bivariate division-polynomial correspondence, Frobenius machinery for Schoof, or Schoof algorithm.

The generic field and polynomial layers intentionally continue to admit F2.
Curve results that require the initial short-Weierstrass characteristic scope
use `short-weierstrass-characteristic-p`, which states nonzero two and nonzero
three directly in the actual `field-*` operations.  Characteristics two and
three are not ruled out for elliptic curves or Schoof mathematically; they need
separate curve models and downstream formulas and are outside the first
implementation scope.

## Architecture

New algebra is built on the `GFIELD`/`GPOLY` stack. Dense polynomials store
coefficients in ascending degree, use `nil` for zero, and remove trailing zero
coefficients when normalized. Fixed-modulus field elements are canonical
remainders. The older HS/PFIELD polynomial layer remains a concrete and
root-count bridge rather than a second target for new generic algebra.

Curve code separates four roles: branch classifiers, executable branch outputs
and dispatchers, independent semantic branch relations, and the independent
full addition relation `curve-point-addition-relation-p`. Certified soundness
connects the dispatcher to the relation; fixed-output determinacy connects any
semantic witness to the dispatcher's canonical output. See
[`docs/architecture.md`](docs/architecture.md) for representations and
boundaries and [`docs/execution-boundaries.md`](docs/execution-boundaries.md)
for totalisation, fixing, guards, and logical/executable correspondence.

## Trust and proof integrity

Certification is the definition of done. Repository policy forbids skipped
proofs, unproved axioms, trust tags, raw Lisp, and equivalent escapes. The trust
scanner treats prohibited spellings even in comments and strings as failures.
Guard verification and execution regressions are execution evidence, not
semantic correctness; a logical/executable boundary also requires a certified
invariant or equivalence theorem. Contributor policy is in
[`AGENTS.md`](AGENTS.md).

## Reproduce the development

On Debian or Ubuntu, install `git`, `make`, `perl`, and `sbcl`, then run:

```sh
make setup
make check-policy
make certify-one BOOK=books/polynomial/base.lisp
make test
make certify
```

`make setup` installs ACL2 8.6 under the ignored `.deps/` directory and uses its
Community Books and certification tools. Initial setup requires network access
and substantial disk space. Complete certification logs are in `.deps/logs/`.

A container build is also available:

```sh
docker build -t acl2-schoof .
docker run --rm acl2-schoof
```

## Repository layout

- `books/` — certified ACL2 books; `books/top.lisp` registers the complete tree.
- `tests/` — executable certification tests.
- `scripts/` — setup, certification, test, trust, policy, and documentation
  checks.
- `docs/` — maintained architecture, status, execution, and planning records,
  plus focused audit and design records.

## Document ownership

- `README.md` owns high-level project scope and the current milestone.
- [`docs/architecture.md`](docs/architecture.md) owns stable design and
  dependency boundaries.
- [`docs/proof-plan.md`](docs/proof-plan.md) owns forward mathematical order.
- [`docs/status-associativity.md`](docs/status-associativity.md) owns the
  at-a-glance current associativity matrix.
- [`docs/obligations.md`](docs/obligations.md) is the concise authoritative
  certified/open/deferred ledger.
- [`docs/audits/`](docs/audits/) preserves detailed proof investigations,
  residuals, countermodels, and historical rationale.
- Git history and pull requests own chronological implementation history.

Resolved blockers are replaced in live status documents rather than appended
beneath obsolete statements. Focused audit records may retain the historical
question and explain how it was resolved, but must label it as history.

## Roadmap and limitations

Full tagged semantic associativity is certified, including infinity-input
reductions and the complete affine D/O/T case assembly.  Executable dispatcher
associativity and both executable inverse orientations for valid tagged inputs
are certified through the independent relation using soundness, determinacy,
closure, and canonical fixing. Algebraic left and right cancellation from the
public executable laws is also certified, and the resulting abstract
abelian-group package retains the characteristic premise. Scalar natural
multiplication by linear repeated addition is also certified; its fast variant
remains a later execution optimization. Generic formal differentiation is
certified with additive and product laws. Generic derivative-coprime
square-freeness and its nonconstant-square-divisor obstruction are also
certified; repeated-factor equivalence and root-based separability remain open.
There is
still no Hasse theorem and no
certified Schoof algorithm. See the [current matrix](docs/status-associativity.md) and
[forward proof plan](docs/proof-plan.md) for the maintained boundaries.
