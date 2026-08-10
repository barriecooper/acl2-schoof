# Arbitrary finite-field architecture

> **Historical design record.** Status and “next” sequences in this audit describe
> the revision at which it was written. Current status is maintained only in
> `obligations.md`; current sequencing is in `proof-plan.md`.

## Decision and scope

This audit is based on repository commit `e245553` and ACL2 8.6 / Community
Books commit `7585056a0647c1ab8a45b1573c5cfe524acbda3f`.  The latter is the exact
checkout made by `scripts/install-acl2.sh`, not a search of a newer Books tree.
The present certified implementation is a polynomial implementation over the
prime field `F_p`; it is not an implementation over an arbitrary field of
cardinality `q`.

**Decision: adopt Option D, followed incrementally by Option C.**  Define a
small project-local, equational field kernel and a generic dense-polynomial
theory for new algebraic results.  Keep the existing, executable,
explicit-modulus PFIELD functions as the prime-field backend and retain its
HS-facing theorem corollaries.  Prove that backend to be an instance rather
than rewriting all existing proofs at once.  Separately construct executable
extensions as `F_p[X]/(m)`.  Algorithms receive an explicit field
specification; abstract theorem books use constrained operations of matching
arity, and generated/manual instance books connect the two.  No stobj or
global encapsulated field constant is part of the semantic interface.

The current dependency boundary is concise: recursive finite-field divmod and
reduced representatives are certified; coefficient-vector coding, carrier
construction, and representative-count cardinality are certified; and the
field-facing bridge to the generic irreducible quotient-field package remains
open.

## Audit method and current dependency inventory

The project books, their include graph, and downstream `books/top.lisp` and
`tests/smoke.lisp` were read.  Searches covered qualified PFIELD operations,
`primep`, modulus parameters, zero/equality uses, and all project `defun` and
`defthm` events.  The relevant direct project surface is:

| File and principal events | Class | Reason / eventual home |
|---|:---:|---|
| `books/polynomial/base.lisp`: `poly-normalize`, raw length lemmas, `poly-one` | A | List trimming, convolution shape, lengths, and the constant-one list are structural once coefficient zero/one are supplied. |
| Same: `field-polynomial-p`, `canonical-polynomial-p`, `field-poly-p` | B | Their recursion is generic, but carrier recognition and trailing-zero equality must come from the field interface.  Today they call `PFIELD::FEP` and ordinary equality to integer zero. |
| Same: `poly-add-raw`, `poly-add`, `poly-scale-raw`, `poly-mul-raw`, `poly-mul`, and closure/ring theorems through `poly-mul-left-distributive` | B | Definitions call `PFIELD::ADD`/`MUL`; proofs use PFIELD closure, identity, associativity, commutativity, and distributivity rules.  Their mathematical content is generic commutative-ring/field algebra. |
| `books/polynomial/eval.lisp`: `poly-eval` and all eight evaluation theorems | B | Horner evaluation and its homomorphism laws are generic; the implementation directly calls `PFIELD::ADD`, `MUL`, `FEP`, and passes `p`. |
| `books/polynomial/degree.lisp`: `poly-zerop`, `poly-nonzero-p`, `poly-degree`, `poly-leading-coefficient`, list/normalization theorems | A/B | Degree and `last` are structural (A).  Zero and leading-coefficient facts are B because canonical coefficient equality/carrier are required. |
| Same: `fep-of-poly-leading-coefficient`, `fep-of-final-coefficient` | B | Generic carrier closure, merely named for PFIELD today. |
| Same: `final-coefficient-nonzero-modulus` | D | It unfolds `PFIELD::FEP` to conclude `(mod lc p) != 0`; the integer-modulus conclusion has no generic-field counterpart. |
| `books/polynomial/pfield-bridge.lisp`: `hs-to-pfield-polynomial` and its list/integer/length lemmas | A/D | The copying function is structural, but its target integer representation and its reconstruction under `field-polynomial-p` are specifically the PFIELD adapter. |
| Same: `mod-of-horner-step-when-tail-mods-agree`, integer evaluator lemmas | D | These reason about integer `mod`, an explicit `p`, and the nonstd integer polynomial evaluator. |
| Same: `eval-pfield-polynomial-agrees-with-poly-eval`, conversion/evaluation/root/non-trivial bridges | E | Their current statements name PFIELD, but evaluation preservation, roots, and nontriviality need generic analogues.  Keep these as concrete instance corollaries. |
| Same: `hs-pfield-polynomial-num-roots-upper-bound` | E | Imports `PFIELD::NUM-ROOTS-OF-POLY-UPPER-BOUND` under `DM::PRIMEP p`; the generic theorem is “a nonzero degree-`d` polynomial over a field has at most `d` roots.” |
| `tests/smoke.lisp` | D/E | Executable examples use moduli 5 and 7 and directly exercise the 2022 PFIELD root counter. |

Classes are: **A** pure list/polynomial structure; **B** generic field algebra;
**C** finite-field-specific but not prime-specific; **D** genuinely prime-field
specific; and **E** a presently PFIELD-tied imported/bridge theorem deserving a
generic statement.

There are currently no project calls to `PFIELD::NEG`, `PFIELD::INV`, or
`PFIELD::FEP-FIX` in executable HS polynomial arithmetic.  `FEP-FIX` occurs in
the imported 2022 definition of nontriviality and in bridge reasoning;
`NEG`/`INV` were inspected because future subtraction and division require
them.  Nor is there a separate PFIELD equality operator: canonical FEP values
are natural representatives and use ACL2 `equal`; before fixing, modular
equality is expressed with `mod`.  Polynomial zero is `nil`, while coefficient
zero is integer `0`.

The explicit parameter `p` occurs throughout the recognizers, arithmetic,
evaluation, theorem hypotheses, root enumeration, and tests.  `DM::PRIMEP`
appears in the final HS root bound and the imported zero-product/root proofs;
most lower polynomial ring laws require only the weaker PFIELD side conditions
used by Kestrel.  Thus “uses `p`” must not be conflated with “mathematically
prime-specific.”

## Exact Community Books candidates inspected

The whole revision was searched by both paths and concepts (`finite field`,
Galois, extension, quotient, irreducible, characteristic, Frobenius,
cardinality, primitive element, embedding, and `GF(p^n)`).  These were the
serious candidates rather than filename matches such as JVM record fields:

| Exact path (package) | Representation and operations | Size/characteristic/extensions | Reuse and trust result |
|---|---|---|---|
| `kestrel/prime-fields/{fep,fep-fix,add,mul,neg,inv,pow,prime-fields,prime-fields-rules}.lisp` (`PFIELD`) | Executable canonical naturals `< p`; explicit `p`; ACL2 equality after fixing; modular add, multiply, negate, inverse and power. | Size and characteristic are the explicit prime `p`.  No `p^n` representation, extension constructor, irreducibility, or general enumeration object. | This is the existing concrete backend and can satisfy a project-local field interface.  Ordinary certified books; already in the dependency closure. |
| `kestrel/prime-fields/prime-fields-alt.lisp` (`PFIELD`) | Same concrete arithmetic, but a constrained nullary `prime` closes unary/binary operations over one unspecified prime. | Only prime fields.  Fixed characteristic, no runtime field selection or extensions. | Demonstrates the arity needed for functional instantiation, but is symbol/arity-incompatible with the explicit-modulus PFIELD world (as `top.lisp` notes).  Do not include it; copy the *pattern* under an HS package. |
| `workshops/2006/cowles-gamboa-euclid/Euclid/fld-u-poly/coe-fld.lisp` and its chain through `fuquot-rem.lisp` (`FLD`, `FUTER`, `FUMON`, `FUPOL`, `FUNPOL`) | Abstract encapsulated carrier `fdp`, equivalence and representative choice, zero/one, `+`, `*`, unary `-` and `/`; sparse normalized polynomials; executable definitions relative to local ACL2-number witnesses. | No finiteness, cardinality, characteristic, Frobenius, extension construction, or selected concrete field. | The abstract laws are useful design evidence and include long-division theory, but definitions remain wired to constrained symbols.  Instantiation transports theorems, not executable bodies; explicit-`p` PFIELD arities do not match.  Clean ordinary certification, but a large old chain and unsuitable as the runtime implementation. |
| `workshops/2022/gamboa-primitive-roots/pfield-polynomial.lisp` (`PFIELD`) | Executable constant-first integer lists, integer evaluation modulo explicit `p`, FEP roots and countdown enumeration; includes nonstd polynomial operations and Kestrel PFIELD. | Domain size/characteristic are `p`; primality is explicit in root/product theorems.  No extension fields or abstract carrier. | Exact source of the certified root-count bridge.  Keep it for the prime instance only.  The system-dependency script certifies its full include closure without adding trust. |
| `nonstd/polynomials/{polynomial-defuns,polynomial-lemmas,polynomial-calculus}.lisp` (`ACL2`) | Executable dense rational/real polynomial functions and syntactic list equality; no coefficient interface or canonical modular form. | No finite size, characteristic, or extensions. | Useful structural/evaluation facts behind the 2022 book, not a finite-field implementation.  Calculus is analytic and not an algebraic derivative/separability package for this purpose. |
| `workshops/2020/gamboa-cowles-gamboa/number-field.lisp` (`ACL2`) | “Number field” is a finite list closed under an integer modular multiplication used for primitive-root group arguments, not a coefficient field API. | Finite list/order data, but no field addition/inverse interface, characteristic, polynomial quotient, or `GF(p^n)`. | The name is a false positive; it cannot instantiate HS field algebra.  Ordinary workshop certification. |
| `projects/groups/{groups,abelian}.lisp` and `projects/groups/support/abelian.lisp` (`DM`) | Concrete finite groups as operation tables/lists, with order, subgroups, powers, and abelian decomposition. | Cardinality is available for groups, but no distributive pair of operations, characteristic, field fixer, or extension constructor. | Potentially useful much later for multiplicative/additive group consequences, not as executable field arithmetic.  Translating every operation to tables would obstruct Schoof execution. |
| `workshops/2000/medina/polynomials/*` and `workshops/2018/greve-gacek/poly.lisp` (`TER`/`MON`/`POL`, `ACL2`) | Respectively rational sparse multivariate normal forms and rational symbolic sparse forms. | Neither has finite size, characteristic, field parameter, irreducibility, or extensions. | Serious quotient/normal-form search hits but wrong coefficient domain and representation; no clean PFIELD instance. |
| `projects/shnf/{top,support}.lisp` (`DM`) | Executable integer sparse Horner expression normalizer. | No field structure, cardinality, characteristic, or extensions. | Not a quotient-field implementation despite canonical-expression machinery. |

No reusable certified definition of a Galois field `GF(p^n)`, finite-field
Frobenius, polynomial quotient field, or algebraic field extension was found
at this revision.  In particular, neither “finite group” nor a book named
“number-field” supplies the required two-operation field.  Adding any future
Community Book must go through `scripts/certify-system-deps.sh`; no uncertified
include or generated certificate is to be committed.

## Required interfaces

### Equational field kernel

The theorem interface needs operations of fixed arity: `fieldp`, `fix`,
`equiv`, `zero`, `one`, `add`, `mul`, `neg`, and total `inv`.  Laws include:

* Boolean carrier; `fix` closure/idempotence; `equiv` equivalence and
  `equiv(x,y) <=> equal(fix(x),fix(y))`; congruence of every operation;
* distinct zero/one, closure, additive/multiplicative identities,
  associativity and commutativity, distributivity, additive inverse;
* for a carrier, nonzero `x`, `mul(x,inv(x))` equivalent to one; and a stated
  harmless value for `inv(zero)` so functions remain total;
* preferably canonical outputs, allowing executable instance corollaries to
  replace `equiv` with ACL2 `equal`.

Algorithms also need an explicit opaque `field-spec` argument.  ACL2 has no
first-class function record, so executable dispatch should be ordinary
project functions such as `ff-add(x,y,spec)`.  Abstract books instead constrain
same-arity operations including `spec`, or fix a constrained spec and use
same-arity wrappers.  Instance books then functional-instantiate algebraic
theorems.  A stobj is inappropriate: fields are immutable mathematical data,
and state-threading would infect every theorem.  A global encapsulated
constant prevents algorithms from selecting fields at runtime.  Records are
appropriate for *data* (`p,n,m`), not for storing ACL2 function values.

### Finite-field extension of the kernel

Add natural data `characteristic(spec)=p`, `cardinality(spec)=q`, a certified
prime-power relation `q=p^n`, and either `elements(spec)` with no duplicates
and exact carrier coverage or a rank/unrank bijection with `[0,q)`.  Enumeration
is required for executable root search but should not burden algebraic root
bounds.  Define exponentiation generically and `frobenius(x,spec)=x^q` for the
absolute `q`-power map.  Prove closure, homomorphism, bijectivity, and `x^q=x`
on `F_q`.  Also expose the characteristic-`p` Frobenius `x -> x^p`: on
`F_{p^n}` it is generally nontrivial, has order dividing `n`, and is the map
needed when reasoning about subfields and algebraic extensions.  These two
maps must not be confused.

### Polynomial and downstream contracts

Generic polynomials retain constant-first canonical dense lists, with `nil`
as zero, but normalization must use field equivalence/fixing rather than
integer zero.  The generic layer needs evaluation, degree, leading
coefficient, addition, multiplication and negation first; later PRs may add
division, gcd, formal derivative, separability, field root bounds, and
polynomial quotient rings.

Curves then depend only on carrier/equality/inversion for affine/projective
points, addition and scalar multiplication, followed by rational maps,
isogenies, kernels/torsion, degree/separability, and the `q`-Frobenius
endomorphism.  Hasse needs abstract finite cardinality and Frobenius facts, not
an integer-mod implementation.  Schoof additionally needs executable `F_q`
arithmetic, polynomial quotient-ring arithmetic, division polynomials,
Frobenius reduction modulo torsion polynomials, and `q` simultaneously as
executable data and a proved cardinality.

## Architecture options

| Option | Reuse / functional instantiation | Execution, termination, statements, certification | Hasse/Schoof and extensions | Decision |
|---|---|---|---|---|
| A: remain PFIELD, later port | Maximum short-term reuse, then duplicated proofs; no generic theorem instance. | Simple current execution/statements; duplicated termination proofs and rising certification cost. | Hasse becomes prime-only and Schoof extension arithmetic forks the stack. | Reject. |
| B: wholesale abstract migration now | Theoretically clean, but rewrites already certified ring/evaluation/root bridges before a second backend exists. | Abstract execution is awkward; large statements and one high-risk certification event. | Eventually suitable, but delays all progress and risks losing the good PFIELD executable path. | Reject as a single PR. |
| C: parallel generic theory + PFIELD instance | Strong forward reuse and functional instantiation; controlled duplication of small structural lemmas. | Generic definitions need deliberate dispatch/instance strategy; moderate certificates.  Concrete wrappers remain fast. | Good for Hasse and Schoof; supports multiple backends and later optimized instances. | Adopt incrementally. |
| D: abstract kernel, preserve wrappers | Smallest arity/axiom experiment and lowest immediate reproof. | Explicit spec keeps execution; theorem statements grow predictably; termination stays structural. | Establishes the seam needed by C and quotient extensions. | **Adopt first.** |
| E: only concrete `F_p[X]/m` | Reuses PFIELD base arithmetic but makes every theorem depend on a representation; generic reproof remains. | Executable and optimizable, but nested specs complicate statements/certification. | Supplies extensions, yet weak for representation-independent Hasse and alternative Schoof backends. | Use as an instance, not the architecture. |
| F: instantiate 2006 FUNPOL | Reuses abstract division results only after copying the reachable definition graph; explicit parameter arities mismatch. | Sparse conversions, old packages, evaluator gap, and expensive certification. | No finite-field metadata or extension implementation. | Reject; retain as theorem-design reference. |

## Concrete `F_{p^n}` representation

An extension specification is an immutable record/list
`(p n modulus-polynomial irreducibility-certificate-data)`.  Its recognizer
requires `DM::PRIMEP p`, positive `n`, a canonical monic PFIELD polynomial `m`
of degree `n`, and a proved irreducibility predicate.  Proof evidence is not a
trusted runtime token: admissibility is an ACL2 predicate and field theorems
assume or derive it.  For concrete named fields, instance books discharge that
hypothesis once.

An element is a canonical base-field coefficient list of length at most `n`
(degree `< n`), fixed by coefficientwise `FEP-FIX`, trimming, and remainder
modulo `m`.  Equality is ACL2 equality of fixed representatives (with an
equivalence theorem to polynomial congruence modulo `m`).  Addition and
negation use base PFIELD coefficients then reduce; multiplication convolves
then reduces.  Inversion may initially use exponentiation `a^(p^n-2)` for
nonzero `a`, avoiding a required extended-gcd implementation in the first
extension-field PR; a later optimized extended Euclidean backend can be proved
equivalent.  All operations are executable.

Certification proceeds in layers: reduction is canonical and congruence
preserving; quotient operations are well-defined; irreducibility makes every
nonzero residue invertible; field laws follow; base-`p` digit vectors of length
`n` give a bijection with `[0,p^n)`, proving cardinality.  Frobenius can execute
by repeated squaring/exponentiation and later be optimized using the image of
`X` modulo `m`.  Prove both `p`-power automorphism facts and the `q=p^n` identity.

### Mandatory stratification (avoiding circularity)

1. **Layer P:** the existing concrete PFIELD dense polynomials over integers
   modulo `p`.  A later, focused base-polynomial division/remainder book is
   allowed to construct quotient representatives; this architecture PR does
   not implement it.
2. **Layer Q:** extension elements are *data represented by Layer-P
   polynomials* reduced modulo a fixed irreducible `m`.  Layer Q may depend on
   Layer P, never on generic polynomials instantiated with Layer Q.
3. **Layer G:** generic dense polynomials parameterized by a coefficient-field
   interface.  Instantiate Layer G with PFIELD and, only after Layer Q is
   certified, with extension elements.  Generic `F_{p^n}[Y]` uses a distinct
   outer variable `Y`; its coefficients happen to be reduced `X`-polynomials.

Separate packages/books and names for base variable `X` and outer polynomial
`Y` make the dependency DAG enforce this stratification.  Do not define the
extension reduction in terms of Layer G's extension-field instance.

## Experiments and feasibility evidence

The preceding bridge-feasibility work certified inclusion of the complete 2006
abstract polynomial endpoint and tested functional substitution.  The include
succeeds, but replacing binary `FLD::+` by ternary `PFIELD::ADD` is rejected by
arity checking, and instantiated theorems do not rewrite FUNPOL executable
bodies.  Inspection of `prime-fields-alt.lisp` confirms that fixed-prime
same-arity wrappers work conceptually but clash with the already loaded
explicit PFIELD symbols.  Therefore a fresh HS package and matching explicit
spec arities are required.

The 2022 endpoint include and its dependency closure are certified by current
setup; the existing HS conversion/root bridge demonstrates clean concrete
reuse.  Source-level construction of `F_4` with `p=2`, `m=X^2+X+1` confirms the
intended four representatives `nil`, `(1)`, `(0 1)`, `(1 1)` and the relation
`X^2=X+1` in characteristic two, but no temporary field book is retained: a
four-element computation would not certify generic irreducibility,
cardinality, or the interface, and would become misleading scaffolding.  No
experiment used admission, axioms, trust tags, or raw Lisp.

## Historical migration plan and consequences

The certified dependency now includes
`finite-field context -> finite-field polynomial core`.  The core is the
ordinary transparent `finite-field-poly-*` target over the field-shaped part of
the context; polynomial correctness does not use rank, unrank, or bound.
Finite-field recursive divmod, fixed-modulus coefficient representation,
mixed-radix coding, carrier construction, and representative-count cardinality
are now certified.  The field-facing bridge to the generic irreducible
quotient-field package remains open.

The numbered plan below records the original architecture migration and is not
the current work queue; certified status and forward sequencing live in the
maintained documents named above.

1. Add a minimal abstract equational field signature and prove only structural
   generic polynomial normalization/carrier facts.
2. Add an explicit-`p` PFIELD adapter with same-arity wrappers and functional
   instances; preserve today's theorem names as corollaries.
3. Move generic add/multiply/evaluation/degree results in tight lemma groups,
   leaving the 2022 root bridge concrete.
4. State and prove the generic algebraic root bound independently of finite
   enumeration; instantiate it for PFIELD, then retire dependence on the 2022
   counter where appropriate without discarding its executable test value.
5. In a separate PR, specify base-polynomial remainder contracts.  Only later
   implement and certify Layer-P division.  Long division is deliberately
   deferred here.
6. Define extension specifications, irreducibility, reduction, and a named
   tiny instance; then prove field laws and cardinality in separate PRs.
7. Instantiate Layer G over extensions; add finite enumeration and Frobenius.
8. Only then add generic derivative/separability and gcd.  Curve coordinates
   and group laws follow the generic field API; Hasse consumes abstract finite
   field/Frobenius theorems; Schoof consumes the executable instances and
   polynomial quotient rings.

This sequence minimizes reproof: existing PFIELD definitions remain the
executable oracle while generic theorems become the source of new semantic
results.  Optimized extension multiplication, table-based tiny fields,
normal-basis Frobenius, or specialized primes can later implement the same
interface and prove equivalence without changing curve theorems.

## Risks and decision points

* ACL2 functional instantiation is arity-sensitive and does not provide
  modules.  Validate the precise explicit-spec encapsulate shape before moving
  any substantial theorem.
* An `equiv`-based interface is robust for quotient values but increases
  congruence proof cost.  Require canonical `fix` outputs so executable
  instances recover ordinary equality.
* Irreducibility is the largest missing mathematical dependency.  Decide
  whether the first named extensions use individually certified polynomials or
  a general executable irreducibility test before promising arbitrary input
  fields.
* Enumeration can make theorem statements and execution expensive.  Keep it
  out of the algebraic kernel and root-bound theorem.
* Dense quotient reduction may be slow for Schoof.  Establish correctness
  before adding sparse, packed, or normal-basis backends.
* The characteristic-`p` and cardinality-`q` Frobenius maps are easily
  conflated; give them distinct names and contracts.
* Extension construction depends on base polynomial remainder, while outer
  polynomials depend on extensions.  The P/Q/G book DAG is a hard review gate.
* The 2022 theorem counts only explicit prime representatives.  It remains a
  prime-field concrete theorem until a generic finite enumeration bridge is
  proved.

Open mathematics remains open in `docs/obligations.md`; this decision marks no
division, extension-field, Hasse, or Schoof obligation proved.

Current finite-field polynomial dependency chain: finite-field context → polynomial core → monomial/scalar-division support → division step → recursive divmod → reduced representatives → fixed-modulus coefficient vectors → mixed-radix coding → explicit carrier and representative-count cardinality.  The remaining bridge packages this explicit layer with the generic irreducible quotient-field interface.

## Finite-field division-step substrate

The finite-field-prefixed one-step polynomial division substrate is certified.
It uses transparent generated definitions for the core step and public term/next
projections, with verified guards, reconstruction, strict degree decrease, and a
strict core length theorem suitable for the future recursive divmod measure.  The
decisive cancellation proof is length/leading-coefficient based, not
coefficient-vector or coding based.  Recursive finite-field divmod, fixed-modulus coefficient representation, exact-width coding, carrier construction, and representative-count cardinality are certified; the field-facing quotient-package bridge remains open.
