# Ambient domain and degree representation audit

## Decision, scope, and evidence labels

This audit was performed on branch `work` at
`271afb2972d664201d9e719037a0d8fc06da17ca`, with a clean worktree.  That commit
is GitHub's merge commit for PR #314.  Its parents and changed-file inventory
confirm that the experimental two-field context, its F7/F7X2 functional
instance, the derived fixed-projection consequence, both `books/top.lisp`
registrations, and the plan, ledger, and earlier Hasse-audit updates are in the
merged tree.  The locally available unauthenticated GitHub API returned 404 for
this private repository, so the Actions result could not be independently
queried from this environment.  The merge commit was created by GitHub and the
checked-in books subsequently pass the repository certification reported in
this change; that is repository-integrity evidence, not a substitute for the
unavailable historical Actions record.

This document uses five deliberately different labels:

* **Certified** means a theorem is in a registered ACL2 book.
* **Ordinary mathematics** means the cited paper argument supports a claim,
  but this repository does not yet certify it.
* **Feasibility witness** means F7/F49 certifies consistency of an experimental
  premise; it is not a generic or geometric realization.
* **Realizable premise** means an abstract intermediate contract has an
  identified mechanically checkable discharge path.
* **Major realization obligation** means that path still requires a substantial
  new certified construction.  Enumeration is identified separately and is
  never promoted to a universal theorem.

**Architecture decision.** Adopt candidate D, a deliberately narrow hybrid:

1. point-level statements use an abstract geometric-point carrier over an
   algebraic extension of the finite base field, with the base embedding and
   `q`-Frobenius fixed-subfield property exposed only where fixed points and
   kernel cardinality require them; and
2. map equality, composition, the endomorphism group, separability, and degree
   use a separate symbolic/function-field-backed endomorphism package.  Its
   first public layer may be abstract, but the public Hasse theorem must be a
   functional instance of a certified concrete realization.

An algebraic closure is a conventional sufficient realization, not a minimum
premise of the final inequality.  A directed union of finite extensions (or an
abstract algebraic geometric-point carrier with equivalent closure and root
properties) is enough: each finite kernel used in the proof is contained in
some finite extension.  Conversely, F49 is not uniformly enough.  For example,
all prime-to-7 torsion kernels `E[ell] = ker([ell])` that underlie general
isogeny/degree theory need not be rational over F49; as `ell` varies their
coordinates require extensions of unbounded degree.  Likewise the quadratic
form is stated for every integer combination `[m] pi + [n]`, not only maps
whose kernel happens to split over F49.

This is an adopted dependency and representation split, not adoption of a
particular algebraic-closure encoding, normalized rational-map syntax, or
isogeny library.  Those remain implementation choices within the stated seam.

## Material inspected

The audit read `README.md`, the proof plan, architecture, obligation ledger,
execution-boundary policy, audit index, and the preceding Hasse audit.  It
checked the PR #312--#314 merge history and books added or changed there,
including the seventh-power, concrete Frobenius witness, experimental context,
functional regression, and top-level registrations.  It also inspected the
include directions for the field kernel, finite-field context,
Frobenius-exponent, finite-bijection/cardinality, generic polynomial core,
derivative, square-free, Euclidean/GCD/XGCD, fixed-modulus and finite-field
fixed-modulus books, curve points, curve abelian-group instance, and
`books/top.lisp`.  The relevant facts below are based on theorem events, not
file names.

The primary mathematical source remains Silverman, *The Arithmetic of Elliptic
Curves*, second edition: Theorem V.1.1, with the degree machinery of III.4--6.
In particular, Theorem III.6.3 says degree is a positive-definite quadratic
form on `Hom(E1,E2)`; the dual-isogeny theorem is III.6.1 in this edition, and
the separable-degree/kernel relationship is in III.4 (especially Theorem
III.4.10).  V.1.1 applies this to Frobenius.  These citations supersede the
older audit's loose attribution of the dual-isogeny input to III.5.  The source
works over algebraic closures when defining geometric kernels; that convention
is sufficient, but the proof below separates it from the weaker existential
content actually consumed.

Secondary evidence was treated cautiously.  Public mathlib source exposes
elliptic-curve, division-polynomial, and some isogeny infrastructure, but no
inspected declaration established this repository's desired Hasse endpoint.
The previously identified Isabelle Schoof host returned HTTP 403 during the
prior audit and remained unavailable as source evidence.  Neither a repository
name, generated program, nor a report is evidence of a mechanically checked
Hasse proof.

## Backward dependency from the squared Hasse bound

Let `pi` be `q`-power Frobenius, `N = #E(F_q)`, and `t = q + 1 - N`.
Silverman's route can be cut into the following dependencies, backwards from
`t^2 <= 4q`.

1. **Nonnegative quadratic.** Positive definiteness of degree gives
   `deg([m]pi + [n]) >= 0` for all integers `m,n`, with equality only for the
   zero homomorphism.  Polarization gives
   `deg([m]pi + [n]) = q*m^2 + t*m*n + n^2`.  Nonnegativity forces the
   discriminant `t^2 - 4q` to be nonpositive.  Cauchy--Schwarz is an equivalent
   presentation, not an additional geometric dependency.
2. **The cross term.** Quadraticity gives
   `deg(1-pi) = deg(1)+deg(pi)-2<1,pi>`.  Thus
   `2<1,pi> = q+1-N = t` once the three displayed degrees are known.
3. **Three degrees.** `deg(1)=1`; Frobenius has total degree `q` (separable
   degree one and inseparable degree `q`); and `deg(1-pi)=N`.
4. **Kernel to degree.** `ker(1-pi)` consists precisely of Frobenius-fixed
   geometric points.  The scalar fixed-subfield theorem identifies their
   affine coordinates with the embedded base field, while infinity is fixed,
   so this kernel is the embedded copy of `E(F_q)`.  Because `1-pi` is
   separable, geometric kernel cardinality equals total degree, giving
   `deg(1-pi)=N`.
5. **Separability.** In characteristic `p` with `q=p^r`, the differential of
   `pi` is zero and the differential of `1-pi` is the identity differential;
   hence `1-pi` is separable.  Equivalently, a purpose-built coordinate proof
   may show that the induced function-field extension has separable degree
   equal to total degree.  Merely showing a dense polynomial square-free does
   not establish this morphism fact.
6. **Maps.** Identity and coordinatewise `q`-power Frobenius are endomorphisms
   of the same geometric curve.  The hom-set must support zero, negation and
   pointwise curve-group addition, integer multiples, subtraction,
   composition, kernels, and equality compatible with degree.  Frobenius
   preserves the curve equation because it is a field homomorphism and fixes
   the embedded coefficients.
7. **Scalars and points.** The ambient scalar carrier must contain coordinates
   of every geometric kernel being counted, be closed under field operations
   and `q`-power, contain an injective base-field image, and satisfy
   `z^q=z` iff `z` lies in that image.  The tagged infinity point needs no
   scalar root.

Dual isogenies are not mentioned in the final two-line discriminant argument.
They are genuinely used by Silverman's proof of the general quadratic-degree
result (III.6.3 via III.6.1).  ACL2 may therefore either certify that supporting
fragment, or realize a narrower quadratic-degree theorem directly for the
subgroup generated by `1` and `pi`.  It may not take quadraticity as a
permanent unsupported axiom.

## Minimum property by use

| Use | Weakest property consumed | Where roots/out-of-base points enter | Repository status |
|---|---|---|---|
| Define `pi(x,y)=(x^q,y^q)` | Ambient field of characteristic `p`, `q=p^r`, embedded coefficients fixed by `q`-power | None beyond closure for evaluating a given point | Scalar shape tested by F7/F49; generic characteristic/cardinality bridge open |
| Prove curve closure | Frobenius preserves `0,1,+,-,*` and fixes `A,B` | No root existence | Experimental homomorphism premise and F7/F49 instance certified; no curve theorem |
| Fixed points equal `E(F_q)` | `z^q=z` iff `z` is in the embedded base image, plus injectivity and infinity handling | Converse quantifies over ambient coordinates | F7/F49 theorem certified only for that finite witness; generic realization open |
| Form map sums/differences | One geometric curve group and totalized map application | Inputs include non-rational geometric points | Curve group over one `GFIELD` certified; cross-field/geometric instantiation open |
| Equality of maps | Equality as curve morphisms, implemented by canonical symbolic/function-field equality or extensional equality on all geometric points | A finite base-point test is insufficient | Open |
| `ker(1-pi)` | All geometric zeros of the morphism on a common point carrier | Kernel points may lie in finite extensions not fixed in advance | Open |
| `#ker(phi)=deg_sep(phi)` | Algebraically sufficient geometric carrier plus finite-kernel enumeration/cardinality theorem | All roots of the kernel scheme's separable part must be represented | Ordinary mathematics; major realization obligation |
| `1-pi` separable | Nonzero differential / separable function-field extension | No enumeration, but the function-field notion detects multiplicity | Open |
| `deg(pi)=q` | Function-field or equivalent morphism-degree semantics; inseparable degree `q`, separable degree `1` | No need to list kernel points | Open |
| Quadratic degree identity | Endomorphism-group equality, integer action, total degree, and proved quadraticity/positivity | General proof may use kernels/torsion over algebraic extensions | Ordinary mathematics; major realization obligation |
| Derive discriminant bound | Ordered integer/rational arithmetic | None | Arithmetic substrate available; exact endpoint open |

### What the ambient choices do and do not provide

* A **single algebraically closed field** is sufficient and is Silverman's
  standard setting.  It is stronger than the logical consumption above and a
  certified construction would be a major layer.
* A **separable closure** is sufficient over a finite field because finite
  fields are perfect, hence their algebraic closure is separable.  This does
  not make the Frobenius morphism separable: morphism separability is a
  function-field statement, not separability of coordinate field elements.
* A **perfect closure** is not sufficient.  The finite base field is already
  perfect, so its perfect closure adds no non-rational torsion or kernel points.
* **One sufficiently large finite extension per finite kernel** is
  mathematically enough for each cardinality argument.  To express all maps
  and integer combinations in one first-order point semantics, however, ACL2
  needs a coherent directed family/union or an abstract carrier with the same
  compatibility; unrelated per-theorem fields do not supply extensional map
  equality or composition.
* A **single fixed finite extension**, including F49, proves only the kernels
  that split there.  It cannot uniformly support the unbounded family
  `ker([m]pi+[n])` or general prime-to-characteristic torsion used in the
  quadratic-degree development.
* A **symbolic function field** avoids requiring ambient roots for map equality,
  composition, inseparable degree, and `deg(pi)`.  It does not by itself count
  geometric kernels, so a root-sufficient carrier remains necessary at the
  kernel-cardinality bridge.
* An **abstract endomorphism/degree interface** is acceptable for an
  intermediate arithmetic theorem and cleanly tests the dependency cut.  It
  is not a final Hasse proof until the concrete curve/Frobenius package is a
  certified functional instance.

## Map representation and total semantics

The minimum responsible representation is not evaluation tables and not a
full library of arbitrary varieties.  It is a purpose-built short-Weierstrass
endomorphism representation whose semantics can be reduced to the rank-two
function field `K(E)=K(x)[y]/(y^2-(x^3+Ax+B))`, or an equivalent normalized pair
`R(x)+S(x)y` with rational-function coefficients.  Identity and Frobenius,
their integer linear combinations under the curve law, and compositions must
be representable.  A canonical symbolic equality or a proved normalization
extensionality theorem supplies map equality.

Equality only on `E(F_q)` is invalid: `pi` and identity already agree there,
although `deg(pi)=q` and `deg(1)=1` and the maps differ geometrically.  The
required equality is equality of morphisms, equivalently equality of induced
function-field homomorphisms (or extensional equality on all geometric points
plus a proved density/extensionality theorem).  Finite enumeration cannot
provide it.

The ACL2 boundary must make these conventions explicit:

* **Infinity:** use the existing tagged infinity externally; symbolic maps
  carry a certified value at infinity rather than treating it as malformed.
* **Poles/exceptional affine inputs:** rational expressions are partial
  presentations of a total projective morphism.  A raw denominator-zero
  fallback cannot define semantics.  Normalized projective/function-field
  semantics must prove that exceptional presentations extend to the correct
  point.
* **Fixing:** malformed syntax fixes to a canonical symbolic zero map (or other
  named canonical representative); malformed points continue to fix to tagged
  infinity.  Congruence theorems relate application to both fixers.
* **Addition/negation/zero:** map addition is induced by the certified curve
  group law on the generic point; zero is the constant infinity map, not the
  pair of zero affine coordinates.
* **Composition:** symbolic substitution followed by normalization, with a
  certified application law and associative/equality congruence.
* **Kernels:** a predicate on fixed geometric points satisfying `phi(P)=O`,
  with a finite duplicate-free carrier only when finiteness/splitting is
  proved.
* **Extensionality:** canonical syntax equality implies and is implied by the
  chosen morphism semantics for the supported map class.  Point testing over
  the finite base field is never the extensionality rule.

A representation only for formal words in `1` and `pi` is tempting but does not
remove the hard part: it must still prove that word equality is sound for curve
maps and must assign the genuine degrees and kernels.  It is useful as the
front-end subgroup, not as an independent realization.  Conversely, importing
all rational maps, divisors, and arbitrary curves would build unused theory.
The rank-two short-Weierstrass fragment is the narrow target.

## Degree and kernel certification boundary

Keep six statements separate:

1. a concrete geometric kernel carrier is finite and has cardinality `k`;
2. `k = deg_sep(phi)` for the supported nonzero isogeny;
3. `deg(phi) = deg_sep(phi) * deg_ins(phi)`;
4. `phi` is separable iff `deg_ins(phi)=1` (or via nonzero differential);
5. `1-pi` is separable, specifically because `d(1-pi)=1`; and
6. therefore `#ker(1-pi)=deg(1-pi)`.

The existing dense formal derivative, product rule, Euclidean GCD, and
square-free predicate concern univariate polynomials over `GFIELD`.  They can
later help normalize rational functions or prove a particular division
polynomial has no repeated roots.  They do **not** presently define the
Kähler/invariant differential of an elliptic-curve morphism, a function-field
extension, separable or inseparable isogeny degree, scheme multiplicity, or the
geometric kernel.  No current derivative theorem should be cited as progress
on item 5 without a new certified bridge.

The narrow concrete realization obligation is substantial but credible:
normalize the rank-two curve function field; define pullback for the supported
endomorphisms; define total/separable/inseparable degree; prove the differential
criterion for this fragment; prove the kernel/separable-degree theorem over a
root-sufficient directed ambient carrier; then prove quadraticity either via
narrow duals or directly for the `Z`-span of `1,pi`.  A false-guarded context
may stage the arithmetic consumer, but all these premises must be discharged
before a public generic Hasse result is claimed.

## Assessment of the PR #314 seam

| Component | Classification | Decision |
|---|---|---|
| Separate base and ambient scalar operations/fixers | Suitable after strengthening | Correct scalar separation; a production instance needs actual field contexts and characteristic/cardinality compatibility, not only individually constrained equations. |
| Injective operation-preserving embedding | Suitable unchanged in concept | Required for coefficient transport and rational-point injection; signatures may be repackaged. |
| `q`, ambient power, and Frobenius | Suitable after strengthening | Tie `q` to certified base cardinality and characteristic prime power; derive rather than merely assume the power homomorphism where possible. |
| Embedded-image predicate | Suitable unchanged in concept | This is the right coordinate-level fixed-subfield proposition and need not expose a witness. |
| Base projection | Witness-specific, not a minimum final primitive | F7X2 coefficient projection conveniently witnesses membership.  General embeddings need not come with a canonical total retraction; use existential/recognizer plus uniqueness, or add a projection only in a realization. |
| Nonidentity witness | Redundant for Hasse | `deg(pi)=q>1` supplies nonidentity when needed.  It was valuable for feasibility testing only. |
| False local context guard | Experimental only | Legitimately checks theorem packaging, but proves no generic inhabited context and cannot occur as the sole realization behind public Hasse. |
| F7/F49 instance and 49-element regressions | Witness-specific evidence | Certified consistency plus execution/enumeration evidence; not geometric sufficiency. |
| Fixed-projection consequence | Witness-oriented derived fact | Sound and certified, but the projection-shaped conclusion should not drive the final abstraction. |

Thus PR #314 survives as an experimental feasibility artifact, unchanged.  Its
base/ambient split and image proposition inform the production seam; the whole
interface is not promoted wholesale.

## Candidate comparison

| Candidate | Adequacy | Checked realization burden / ACL2 fit | Reuse and Schoof value | Overbuild risk | First discriminating theorem |
|---|---|---|---|---|---|
| A. Constrained algebraically closed ambient field | Sufficient | Very high: a functional instance needs a certified algebraic closure or equivalent; first-order totalization is possible but root choice/fixing is extensive | Reuses curve operations; little executable Schoof need | Very high | Every nonconstant supported polynomial has a represented root |
| B. Directed finite-extension family | Sufficient if embeddings are coherent and every finite kernel splits at some stage | High: tower indices, embeddings, common-stage operations, and cardinality transport; constructive finite-field fit is good | Some extension arithmetic may help Schoof, but general colimit does not | High | Every supported nonzero isogeny kernel has a duplicate-free carrier at some coherent stage |
| C. Symbolic rank-two function field plus ambient only for kernels | Sufficient and close to the source's degree semantics | High but focused: normalization, pullback, degrees, and kernel bridge; good totalized canonical-syntax fit | Polynomial reuse is strong; symbolic pieces may help quotient-coordinate proofs | Medium | Frobenius pullback is normalized and has total degree `q` |
| D. Hybrid scalar seam plus separate symbolic/abstract endomorphism-degree package | Sufficient, provided the abstract layer receives C/B-style concrete instances | Stages risk well: first-order abstract algebra is easy; concrete discharge remains high and explicit | Best reuse; lets Schoof proceed independently | Medium, controlled by refusing unsupported general maps | A concrete symbolic Frobenius instance satisfies the abstract degree facts, beginning with `deg(pi)=q` |
| E. Formal words generated by `1,pi` with an asserted positive quadratic | Arithmetically sufficient but not logically sufficient alone | Low until realization, then inherits C's hard obligations; excellent ACL2 syntax | Little Schoof benefit | High risk of disguising axioms | Functional instance of word equality/degree from concrete curve maps |

D is selected, with C's rank-two function field as the expected concrete map
realization and a B-like directed ambient only at the kernel bridge.  This does
not require constructing a global algebraic closure.  Candidate E is useful
only as an intermediate consumer theorem; A is unnecessarily broad; B alone
does not solve symbolic map equality or degree.

## Hasse versus executable Schoof

**Shared work:** actual finite-field cardinality/characteristic metadata;
canonical base polynomial and fixed-modulus arithmetic; short-Weierstrass
formulas; fixing discipline; and finite-field `q`-power laws.  A normalized
rank-two rational expression layer may later offer lemmas to both tracks, but
it is not currently a Schoof prerequisite.

**Hasse-only on the selected route:** a geometric-point carrier rich enough for
all relevant kernels; base embedding into it; general morphism equality;
geometric kernel cardinality versus separable degree; inseparable degree;
differentials of morphisms; dual isogenies or the replacement proof of degree
quadraticity; and the positive quadratic degree form.

**Schoof-only/independent:** division-polynomial recurrences, arithmetic in
`F_q[x]/(psi_ell)`, quotient-coordinate Frobenius and trace congruence tests,
incremental CRT, and the executable point-count wrapper.  These operate on
symbolic quotient coordinates over finite rings and do not wait for an
algebraic closure, a general geometric-point carrier, arbitrary rational maps,
or Hasse degree theory.  Hasse supplies a traditional reconstruction bound,
but a separately certified numerical point-count bound/specification can
support executable CRT without making the Hasse proof an implementation
prerequisite.

For dependency value and proof cost, the next implementation PR should switch
to the shared/Schoof substrate rather than begin the expensive Hasse-only
function-field realization.

## Reviewable implementation boundaries

The recommended dependency order deliberately permits the two tracks to run in
parallel:

1. **Shared/Schoof reduced-ring law:** certify finite-field remainder/add
   compatibility and reduced-add associativity for the existing explicit
   modulus interface.  No extension tower or curve map is involved.
2. **Schoof quotient-coordinate substrate:** complete the finite-field reduced
   ring instance needed to interpret coordinates modulo a supplied polynomial,
   with fixing and congruence laws.
3. **Hasse abstract consumer:** in a local/context-guarded book, certify the
   purely algebraic discriminant implication from named endomorphism/degree
   premises.  It is explicitly not a Hasse theorem and remains unregistered as
   a production realization until an instance exists.
4. **Hasse symbolic map slice:** define only the rank-two short-Weierstrass
   generic-function representation needed for identity and Frobenius pullback,
   with canonical equality, infinity contract, and composition for that slice;
   certify the first concrete endpoint `deg(pi)=q`.
5. **Hasse kernel/degree slice:** introduce the directed root-sufficient point
   realization and certify separability of `1-pi`, fixed-kernel/base-point
   correspondence, and `#ker(1-pi)=deg(1-pi)` before completing quadraticity
   and the squared bound.

Boundaries 1--2 are shared/Schoof; 3--5 are Hasse-only except for incidental
symbolic lemmas.  Each later logical/executable boundary remains subject to the
repository's specification, equivalence, guard, regression, and documentation
policy.

## Exactly one recommended next Codex task

**Task: finite-field reduced-add associativity boundary.**  Using the existing
`finite-field-poly-remainder` and `finite-field-poly-reduced-add`, certify the
minimum remainder/add compatibility lemmas and the public theorem
`finite-field-poly-reduced-add-associative` for arbitrary ACL2 inputs under the
existing finite-field context and nonzero normalized-modulus hypotheses.
Preserve current fixing and zero-modulus semantics, add a focused regression
functional instance, register the books in `books/top.lisp`, update only the
ledger/plan/execution-boundary owners affected, and run the full certification
policy.  Do not add division polynomials, curve Frobenius, extension towers,
rational maps, or Hasse assumptions.
