# ACL2 Community Books mathematics audit

## Purpose, authority, and baseline

This record preserves a read-only audit of mathematical material in the ACL2
Community Books that may shorten or reshape the Hasse--Schoof development.  The
upstream baseline is ACL2 commit
[`7a31c78f91fc4d54f5037e34aa2c4cf49556bf0e`](https://github.com/acl2/acl2/commit/7a31c78f91fc4d54f5037e34aa2c4cf49556bf0e).  The project baseline
is `27edf87409deacc9ff4165f1a40cdd79a61fd0b4`, the merge of PR #343, which
certified the fixed characteristic-11 quotient-coordinate additive Frobenius
boundary.

This is an evidence and decision-support record, not the authority for current
project status or implementation order.  Current status is maintained in the
[obligation ledger](../obligations.md), forward order in the
[proof plan](../proof-plan.md), and adopted boundaries in
[architecture](../architecture.md).

The audit inspected named source books and repository-wide code searches for
binomial mathematics, number theory and CRT, fields and polynomials, finite
groups and actions, quadratic residues, elliptic-curve infrastructure, and
several expected Schoof/Hasse dependencies.  “Not found” below means not found
by those searches or in the inspected books at the pinned revision; it is not a
claim that no relevant ACL2 development exists anywhere.

The labels used below are:

- **Verified upstream fact**: a definition or certified theorem present in the
  pinned Community Books revision.
- **Applicability conclusion**: an assessment of compatibility with this
  repository's maintained representations.
- **Recommendation**: proposed future work; not adopted architecture unless the
  maintained architecture document says so.

## Executive conclusions

1. The Community Books contain a complete concrete-arithmetic binomial proof
   whose *proof architecture* is highly relevant, but its final theorem is not
   directly a theorem about an abstract commutative ring.
2. The fixed exponent-eleven construction merged in PR #343 is an acceptable
   F11 bootstrap and is reusable for different curves and quotient moduli over
   characteristic 11.  Repeating fixed Pascal rows for each new characteristic
   is not an acceptable portability architecture.
3. The next generic Frobenius design should adapt the upstream binomial proof's
   interval-aligned recursion and separate multiplication branches to an
   abstract commutative ring, combine it with a theorem that a prime divides
   every interior coefficient, and derive `p^r`-power additivity by iteration.
4. The Community Books contain directly useful integer prime, divisibility,
   gcd, and CRT results.  They do not by themselves supply the centred
   reconstruction, Hasse-interval uniqueness, or modulus-product argument
   needed by the final Schoof boundary.
5. The `projects/fields` and `projects/groups` developments are
   mathematically substantial, but their explicit list/tower and operation-table
   representations do not match this repository's `GFIELD`, `GPOLY`,
   quotient-coordinate, or contextual curve-group interfaces.
6. Euler-criterion and Tonelli--Shanks books are useful as executable
   prime-field regression oracles.  They are not a replacement for generic
   field or curve semantics.

## Binomial theorem and Frobenius

### Verified upstream content

[`books/arithmetic/binomial.lisp`](https://github.com/acl2/acl2/blob/7a31c78f91fc4d54f5037e34aa2c4cf49556bf0e/books/arithmetic/binomial.lisp)
contains a complete proof of the ordinary binomial theorem.

Its public ingredients include:

- `choose`, defined by factorials with totalized malformed cases;
- non-rewriting `choose-reduction`, the Pascal recurrence for interior
  coefficients;
- recursive `choose-mk` and non-rewriting `choose-mk-choose`;
- `binomial-expansion`, an interval-indexed list of monomial terms;
- `binomial-expansion-times-x` and
  `binomial-expansion-times-y`, with correctness theorems;
- `binomial-expansion-triangle`, which interleaves the two multiplication
  branches;
- `binomial-expansion-pascal-triangle` and
  `pascal-triangle-binomial`, which collect adjacent Pascal contributions;
- `binomial-theorem-induction-lemma`; and
- `binomial-theorem`.

The important structural feature is that the row traversal, multiplication
lemmas, Pascal collection, and induction all recurse over compatible interval
parameters.  The proof first controls multiplication by each summand, then
interleaves and collects terms, and only then performs exponent induction.

### Direct-reuse limit

**Applicability conclusion.** The expansion terms use ACL2's concrete numeric
`+`, `*`, `expt`, and `sumlist`.  The theorem is therefore not directly
a quotient-coordinate theorem, and it is not immediately functionally
instantiable as a commutative-ring theorem merely by renaming operations.
Its `choose` recurrence and induction architecture are more reusable than its
final algebraic statement.

PR #343 tested two other generic representations before completing the fixed
row:

- a row descending in coefficient index while the proposed induction varied
  only the exponent; and
- a coefficient-list evaluator whose malformed/empty-list and length
  invariants dominated the proof before quotient-coordinate algebra was
  reached.

Those failures do not refute generic binomial algebra.  They show that the
recursive representation must be designed around the induction, as the
Community Books proof already does.

### Portability decision supported by the audit

**Recommendation.** Before supporting a characteristic other than 11, create an
abstract commutative-ring binomial layer with:

1. a ring-facing natural-scalar operation and natural power;
2. an interval-indexed expansion whose recursion aligns with its induction;
3. separate multiplication-by-left and multiplication-by-right lemmas;
4. an interleaved Pascal contribution form;
5. coefficient collection using the numeric Pascal recurrence; and
6. a public non-rewriting binomial theorem suitable for functional
   instantiation by quotient coordinates.

Then add the number-theoretic fact that, for prime `p` and
`0 < k < p`, `p` divides `choose(k,p)`.  Combining coefficient
annihilation with the abstract binomial theorem gives characteristic-`p`
additivity.  For `q = p^r`, use power-of-power and Frobenius iteration rather
than expanding to exponent `q`.

This generic layer is mandatory before changing characteristic, but it need not
interrupt the immediate F11 trace-congruence path.  The fixed theorem from PR
#343 remains a useful regression and a future client of the generic layer.

## Integer number theory and CRT

### Euclid, primes, divisibility, and factorization

[`books/projects/numbers/euclid.lisp`](https://github.com/acl2/acl2/blob/7a31c78f91fc4d54f5037e34aa2c4cf49556bf0e/books/projects/numbers/euclid.lisp)
provides an explicit integer/rational number-theory development.  Verified
public boundaries include:

- `divides` and basic closure/transitivity/modular characterizations;
- `primep`, least divisors, and least prime divisors;
- `infinitude-of-primes` via `greater-prime`;
- Euclidean gcd and a certified linear combination;
- Euclid's lemma `euclid`;
- lcm and relative-primality results; and
- existence and uniqueness of prime factorization.

**Applicability conclusion.** These integer theorems are plausible direct
dependencies for choosing torsion primes, proving pairwise coprimality, and
modulus-product arithmetic.  Namespace and totalization conventions must be
reviewed at the exact use site, but no field-representation bridge is required.

### Chinese remainder theorem

The same public book exports the construction from
[`books/projects/numbers/support/crt.lisp`](https://github.com/acl2/acl2/blob/7a31c78f91fc4d54f5037e34aa2c4cf49556bf0e/books/projects/numbers/support/crt.lisp).
For an integer residue list and a same-length list of pairwise relatively prime
integer moduli, `chinese-remainder-theorem` proves that `crt` is an integer
satisfying every requested congruence.  Supporting definitions include
`rel-prime-moduli`, `congruent-all`, `prod-list`, and `crt`.

**Applicability conclusion.** This is directly useful as the congruence
existence/construction core for Schoof.  The audited public endpoint does not
select a centred representative, prove uniqueness in a symmetric interval,
connect that interval to the Hasse bound, or prove that an accumulated product
of selected small primes is large enough.  Those remain project-specific
boundaries.

Older CRT developments also occur under `books/workshops/1999` and
`books/workshops/2000`.  The maintained `projects/numbers` interface is the
preferred candidate unless a later proof exposes a missing theorem that the
older books uniquely supply.

### CRT work still required

A final Schoof reconstruction layer still needs to certify:

- a canonical representative modulo the accumulated product;
- conversion to a centred representative;
- uniqueness of the trace in the Hasse interval when the product exceeds the
  required width;
- the precise product inequality for the chosen torsion primes; and
- composition with individually correct trace residues.

The numerical observation `3*5 > 4*sqrt(11)` is not a substitute for those
certified interfaces.

## Fields, polynomials, separability, and Galois theory

### Verified upstream content

The
[`projects/fields` overview](https://github.com/acl2/acl2/blob/7a31c78f91fc4d54f5037e34aa2c4cf49556bf0e/books/projects/fields/README)
and
[`galois.lisp`](https://github.com/acl2/acl2/blob/7a31c78f91fc4d54f5037e34aa2c4cf49556bf0e/books/projects/fields/galois.lisp)
describe and certify a substantial finite-field and extension-field stack.
Relevant public material includes:

- field operations, polynomial arithmetic, division, gcd, irreducibility,
  evaluation, homomorphisms, embeddings, and extension towers;
- `ntimes` and `fnat` for repeated addition and natural-number embedding;
- `fchar`, minimal positive characteristic when nonzero;
- `primep-fchar`;
- `ntimes-fchar-0` and `fnat-fchar-0`, relating annihilation to
  divisibility by the characteristic;
- preservation of characteristic across extensions;
- formal `derivative`, additive, scaling, product, homomorphism, lift, and
  embedding laws;
- `separablep` and no-multiple-root consequences;
- splitting fields and extension-by-roots constructions;
- field embeddings and automorphism groups; and
- a formal Fundamental Theorem of Galois Theory.

The root-counting and separability material is especially relevant as proof
architecture for future ambient-field fixed-point or kernel arguments.

### Representation mismatch

**Applicability conclusion.** These books represent fields, extension towers,
elements, polynomials, embeddings, and groups through explicit data structures
and lists.  This repository deliberately uses a different stack:

- constrained total `GFIELD` operations with fixing;
- canonical dense `GPOLY`;
- nullary fixed-modulus fields and separate explicit finite-field adapters;
- transparent rank-two quotient coordinates; and
- contextual curve groups with ordinary equality on fixed representatives.

Consequently, the `projects/fields` theorems are not drop-in replacements for
the maintained field or polynomial APIs.  Importing the whole representation
would create a second algebraic architecture.  Reuse should normally take one
of three forms:

- adapt a proof architecture into the maintained representation;
- prove a narrow bridge for a theorem whose value justifies the bridge; or
- use a concrete computation as an independent regression oracle.

The characteristic/divisibility theorem is a promising architectural guide for
the future generic Frobenius layer.  The separability/root-count chain is a
promising guide for the Hasse ambient-field seam.  A wholesale migration to the
explicit field-tower representation is not recommended.

## Finite groups, maps, actions, and list support

[`books/projects/groups/lists.lisp`](https://github.com/acl2/acl2/blob/7a31c78f91fc4d54f5037e34aa2c4cf49556bf0e/books/projects/groups/lists.lisp)
provides duplicate-free lists, indexing, sublists, disjointness, permutations,
and intersection machinery.  One small theorem already identified as
potentially useful is `len-1-1-equal`, which turns injectivity between finite
duplicate-free lists into an equality-of-length conclusion.

[`books/projects/groups/actions.lisp`](https://github.com/acl2/acl2/blob/7a31c78f91fc4d54f5037e34aa2c4cf49556bf0e/books/projects/groups/actions.lisp)
contains explicit finite group actions, orbits, stabilizers, class equations,
orbit--stabilizer divisibility, conjugation, normalizers, and induced
permutation representations.  Related maps and group books build a broad
finite-group theory over explicit element lists and operation tables.

**Applicability conclusion.** Small list lemmas may be directly reusable after
checking packages and hypotheses.  The higher group/action theory is valuable
as proof architecture, particularly for orbit and kernel counting, but it does
not directly instantiate the maintained contextual curve-group API.  A bridge
would have to connect:

- explicit enumerated carriers to the repository's carrier predicate;
- table/list operations to the maintained curve operation;
- membership equality to fixed-representative equality; and
- the explicit identity/inverse conventions to the contextual package.

Such a bridge should be introduced only for a named downstream theorem, not as
a speculative parallel group hierarchy.

## Quadratic residues and modular square roots

[`books/kestrel/number-theory/quadratic-residue.lisp`](https://github.com/acl2/acl2/blob/7a31c78f91fc4d54f5037e34aa2c4cf49556bf0e/books/kestrel/number-theory/quadratic-residue.lisp)
defines executable `has-square-root?` using Euler's criterion for an odd prime
and proves its relationship with modular squaring, including
`no-square-root-forall` and `has-square-root?-suff`.

[`books/kestrel/number-theory/tonelli-shanks.lisp`](https://github.com/acl2/acl2/blob/7a31c78f91fc4d54f5037e34aa2c4cf49556bf0e/books/kestrel/number-theory/tonelli-shanks.lisp)
implements modular square roots, while
[`tonelli-shanks-proof.lisp`](https://github.com/acl2/acl2/blob/7a31c78f91fc4d54f5037e34aa2c4cf49556bf0e/books/kestrel/number-theory/tonelli-shanks-proof.lisp)
certifies the loop invariants and correctness endpoints, including
`tonelli-shanks-is-sqrt-modp` and `tonelli-shanks-is-correct`.

**Applicability conclusion.** These are directly useful for executable
prime-field test generation and independent regression oracles—for example,
enumerating or checking affine points over concrete prime fields.  Their
integer-modular representation and odd-prime scope do not establish generic
`GFIELD` square-root semantics, extension-field square roots, curve
cardinality, or Schoof correctness.

## Negative search results at the pinned revision

Repository-wide searches and inspection of the likely mathematical projects did
not locate a project-suitable certified endpoint for the following:

- Hasse's theorem for elliptic curves;
- Schoof or Schoof--Elkies--Atkin point counting;
- elliptic-curve isogenies, dual isogenies, or isogeny degree;
- classical division-polynomial semantics suitable for this repository;
- a polynomial resultant library suitable for the maintained `GPOLY` stack;
- a generic abstract-commutative-ring Frobenius/binomial theorem;
- prime divisibility of every interior coefficient `choose(k,p)`;
- centred bounded CRT uniqueness in a Hasse interval; or
- a certified selected-small-prime product bound for Schoof.

Some search terms occur in comments, cryptographic curve books, workshop
material, or unrelated solver interfaces.  Those hits were not treated as the
missing mathematical endpoints.  These are scoped negative findings, not
global nonexistence claims.

## Prioritized recommendations

| Priority | Candidate source | Useful theorem or architecture | Repository destination | Action | Main risk |
|---|---|---|---|---|---|
| 1 | `arithmetic/binomial.lisp` | Interval-aligned binomial induction, separate multiplication branches, Pascal collection | A future generic commutative-ring algebra book | Adapt before supporting another characteristic | Abstracting concrete arithmetic without recreating list-invariant failures |
| 2 | `projects/numbers/euclid.lisp` and `support/crt.lisp` | Primes, divisibility, gcd, pairwise-coprime CRT construction | Future Schoof residue accumulation and reconstruction books | Use/adapt when residue correctness is available | Missing centred uniqueness and Hasse-bound composition |
| 3 | Current F11 trace books | Certified characteristic-11 additive Frobenius and algebraic trace predicate | Immediate Schoof critical path | Continue now to trace-congruence semantics | Classical torsion/ambient interpretation remains open |
| 4 | `projects/fields/galois.lisp` | Characteristic divisibility, derivatives, separability, root bounds, extension architecture | Generic Frobenius and Hasse ambient-field design | Adapt selected proof ideas later | Major representation mismatch |
| 5 | `projects/groups/lists.lisp` | Duplicate-free list and finite-cardinality lemmas such as `len-1-1-equal` | Finite carrier/cardinality support | Reuse narrowly when hypotheses match | Package and equality conventions |
| 6 | `projects/groups/actions.lisp` | Orbits, stabilizers, class equation, action-to-permutation architecture | Possible future kernel/orbit counting | Adapt only for a named theorem | Explicit operation-table representation mismatch |
| 7 | Kestrel quadratic-residue and Tonelli--Shanks books | Certified modular-square-root decision and computation | Concrete prime-field regressions | Regression oracle | Prime-field integer representation only |
| 8 | Older workshop CRT books | Alternative CRT proof developments | None by default | Defer/reject unless the maintained CRT interface is insufficient | Duplicated legacy interface |

## Effect on the live plan

This audit does not change the immediate proof-plan order established after PR
#343: the F11 track should next connect the algebraic cross-multiplied predicate
to the actual Frobenius trace congruence.  It does establish two portability
constraints for later work:

- do not repeat the fixed Pascal-row construction for a new characteristic; and
- do not expand directly to a prime-power exponent.

Before a different characteristic becomes an implementation target, the
abstract commutative-ring binomial/characteristic-`p` layer described above
must become a certified boundary.  CRT work becomes urgent after enough
trace-residue correctness clients exist to support reconstruction.

## Addendum: Cayley--Hamilton search (2026-08-13)

This addendum records a fresh, scoped search at upstream ACL2 revision
[`48f289ce50bcc88487fd3e85163e7afd8e9e6e7f`](https://github.com/acl2/acl2/commit/48f289ce50bcc88487fd3e85163e7afd8e9e6e7f)
(commit date 2026-08-12).  The revision was inspected by a sparse checkout of
`books/doc` and `books/projects/linear`, followed by case-insensitive searches
for Cayley--Hamilton, characteristic polynomials, eigenvalues, matrix trace,
and spellings of `2x2`, and by reading the linear books named below.  This is a
revision-pinned addition to the inventory, not a claim about all ACL2 books at
all times.

### Exact positive and negative evidence

* [`books/doc/100-theorems.lisp`](https://github.com/acl2/acl2/blob/48f289ce50bcc88487fd3e85163e7afd8e9e6e7f/books/doc/100-theorems.lisp#L345)
  contains “49. The Cayley-Hamilton Theorem” only as a commented-out catalogue
  entry.  It names no event or certified book.
* [`books/projects/linear/README`](https://github.com/acl2/acl2/blob/48f289ce50bcc88487fd3e85163e7afd8e9e6e7f/books/projects/linear/README#L43-L53)
  calls the development a work in progress and lists the ring of polynomials,
  eigenvalues, and the characteristic polynomial as planned work.
* The available ring side is substantial:
  [`ring`](https://github.com/acl2/acl2/blob/48f289ce50bcc88487fd3e85163e7afd8e9e6e7f/books/projects/linear/ring.lisp)
  constrains a commutative ring with unity,
  [`rmat`](https://github.com/acl2/acl2/blob/48f289ce50bcc88487fd3e85163e7afd8e9e6e7f/books/projects/linear/rmat.lisp)
  supplies rectangular matrices, transpose, addition, scalar multiplication,
  and matrix multiplication, and
  [`rdet`](https://github.com/acl2/acl2/blob/48f289ce50bcc88487fd3e85163e7afd8e9e6e7f/books/projects/linear/rdet.lisp)
  supplies permutation determinants, alternating/multilinear properties,
  multiplicativity, cofactor expansion, and the classical adjoint.
* The field side repeats and extends that infrastructure:
  [`field`](https://github.com/acl2/acl2/blob/48f289ce50bcc88487fd3e85163e7afd8e9e6e7f/books/projects/linear/field.lisp),
  [`fmat`](https://github.com/acl2/acl2/blob/48f289ce50bcc88487fd3e85163e7afd8e9e6e7f/books/projects/linear/fmat.lisp), and
  [`fdet`](https://github.com/acl2/acl2/blob/48f289ce50bcc88487fd3e85163e7afd8e9e6e7f/books/projects/linear/fdet.lisp)
  provide field operations, matrices, and determinants;
  [`reduction`](https://github.com/acl2/acl2/blob/48f289ce50bcc88487fd3e85163e7afd8e9e6e7f/books/projects/linear/reduction.lisp)
  adds reduced row-echelon form, row reduction as matrix multiplication,
  invertibility, linear systems, and Cramer's rule.

No theorem, definition, or comment implementing a specialized `2x2`
characteristic identity under another name was found in those inspected paths,
and the repository-wide filename list disclosed no separate characteristic-
polynomial book in `books/projects/linear`.  In particular, searches for the
four-entry identity, matrix trace terminology, `2x2` spellings, eigenvalues,
and characteristic polynomials led only to the planned-work README (apart from
ordinary determinant prose).  **Conclusion:** no suitable certified general or
fixed-`2x2` Cayley--Hamilton endpoint was found at the inspected revision and
within the paths and terms above.  This scoped negative result does not assert
that no differently encoded local algebra lemma exists anywhere in ACL2.

### Cost interpretation

For a literal matrix `((a b) (c d))`, the identity
`M^2 - (a+d)M + (ad-bc)I = 0` is four bounded commutative-ring normalizations.
It could probably be proved locally without characteristic polynomials,
permutation determinants, row reduction, or the complete `linear` stack.  That
small algebra fact is categorically different from proving that Frobenius acts
on a rank-two `E[3]`, that its determinant is `q mod 3`, and that its matrix
trace is `q + 1 - #E(F_q) mod 3`.  The latter are elliptic-curve, torsion,
fixed-point/cardinality, and semantic-identification obligations; importing a
matrix library or proving the four identities does not discharge them.  The
focused route comparison is preserved in
[the Schoof trace-congruence audit](schoof-trace-congruence-routes.md).
