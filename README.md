# ACL2 Hasse--Schoof

ACL2 Hasse--Schoof develops certified algebra and elliptic-curve foundations for
a future Manin-style proof of Hasse's theorem and an executable implementation
of Schoof point counting. The initial curve scope is short Weierstrass curves
over fields of characteristic other than two and three. Neither Hasse's theorem
nor Schoof's algorithm is complete.

## Certified scope

The repository currently certifies these subsystem-level foundations:

- a constrained generic field interface (`GFIELD`) with total fixing, natural
  powers, and characteristic-exclusion and Frobenius-exponent assumptions;
- a field-only X-CERT algebra layer with explicit residual generators, an
  output telescope, a factored remainder identity, and their composition, plus
  a curve-semantic specialization for the two ordered nested distinct-x trees;
- canonical dense polynomials (`GPOLY`) with arithmetic, evaluation, degree,
  division with remainder, Euclidean GCD, extended GCD, modular inversion,
  irreducibility, and reduced arithmetic;
- a generic fixed-modulus quotient-field construction for an irreducible
  polynomial, plus concrete PFIELD/F7 clients and an F7X2 proving instance;
- short-Weierstrass coordinates, canonical affine coordinates, tagged curve
  points (affine or infinity), and point negation;
- total affine branch classification and executable affine/tagged-point
  dispatchers, with independent semantic relations for the geometric branches
  and for full tagged-point addition; and
- output closure, infinity identity, inverse-to-infinity, and commutativity for
  full tagged-point addition.

Concrete F7 and F11 books are focused executable and instantiation regressions.
They demonstrate particular computations; they do not by themselves establish
a generic theorem. The detailed proved/open ledger is
[`docs/obligations.md`](docs/obligations.md).

The curve development is **not** yet a certified group law: associativity,
cancellation, group packaging, and scalar multiplication remain unproved.
There is no certified Hasse theorem, point-count correctness theorem,
division-polynomial theory, Frobenius machinery for Schoof, or Schoof
algorithm.

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

## Documentation guide

- [`docs/architecture.md`](docs/architecture.md): stable layers,
  representations, and dependency boundaries.
- [`docs/obligations.md`](docs/obligations.md): authoritative detailed ledger of
  certified, open, and deferred obligations.
- [`docs/proof-plan.md`](docs/proof-plan.md): forward dependency path toward
  Hasse and Schoof.
- [`docs/execution-boundaries.md`](docs/execution-boundaries.md): totalisation
  and logical/executable contracts.
- [`docs/references.md`](docs/references.md): principal external references.

Focused documents under `docs/` preserve technical audits and design rationale.
When their historical status language differs from the ledger, the certified
books and `docs/obligations.md` govern current status; Git history and pull
requests retain chronological completion narratives.

## Roadmap and limitations

The immediate mathematical task is not an associativity proof. It is an audit
of the algebraic identities and reusable field/coordinate lemmas that a
tractable associativity proof would require, followed by development of the
missing reusable prerequisites. Only then should full tagged-point
associativity be scoped. Later phases package the curve laws, build the
polynomial and rational-function machinery needed by the Hasse and Schoof
tracks, formalize Frobenius and division polynomials, and develop point
counting and CRT reconstruction. The dependency rationale is maintained in
[`docs/proof-plan.md`](docs/proof-plan.md).
