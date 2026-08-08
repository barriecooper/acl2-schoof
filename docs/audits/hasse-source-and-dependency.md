# Hasse source and dependency audit

## Purpose and authority

This record preserves the corrected conclusions of the read-only Hasse
source-and-dependency audit performed at commit
`1f2806aea5d9115ce037e879112a54d008e6e02f`.  That baseline already contained
the concrete F7X2 `GFIELD` packaging and 49-element cardinality work.  The tree
was clean, the branch was `work`, and no remotes were configured.

This is a decision and evidence record, not the current status authority.
Current status is maintained in the [obligation ledger](../obligations.md),
forward order in the [proof plan](../proof-plan.md), and adopted architecture
in [architecture](../architecture.md).  In particular, every representation
discussed below remains a candidate unless the architecture document later
adopts it.

The labels used below are deliberately distinct:

- **Certified repository fact** identifies an ACL2 boundary present in the
  certified books.
- **Required mathematics** identifies a fact used by the selected paper proof,
  not a theorem the repository currently has.
- **Project decision** records an accepted direction or exclusion.
- **Candidate** is a design worth testing but not adopted architecture.
- **Realization obligation** is missing work needed to justify a proposed
  premise or implementation.

## Selected source and logical chain

### Primary route

**Project decision.** The presently selected route is the Frobenius and
quadratic-degree proof in Joseph H. Silverman,
[*The Arithmetic of Elliptic Curves*](https://link.springer.com/book/10.1007/978-0-387-09494-6),
second edition, Chapter V, Theorem 1.1.  The selection remains subject
to checking theorem statements against the exact edition during proof design.
Its degree input is the positive-definite quadratic form on homomorphisms from
Chapter III, Section 6, especially Theorem III.6.3, built on the isogeny and
dual-isogeny results of Sections III.4 and III.5.

The intended mathematical chain is:

1. for the `q`-power Frobenius endomorphism `pi`, base-field rational points
   are precisely the fixed points, hence `E(F_q) = ker(1 - pi)`;
2. `1 - pi` is separable, so its kernel size is its degree;
3. `deg(pi) = q` and `deg(1) = 1`;
4. degree is a positive quadratic form, with pairing obtained by
   polarization;
5. if `N = #E(F_q)` and `t = q + 1 - N`, then
   `t = 2 <pi,1>`; and
6. Cauchy--Schwarz gives `t^2 <= 4q`.

**Project decision.** The preferred first ACL2 conclusion is the integer
inequality

```text
(q + 1 - N)^2 <= 4q.
```

The conventional `|q + 1 - N| <= 2*sqrt(q)` form should be a separate
arithmetic corollary.  This avoids making real square-root infrastructure part
of the elliptic-curve proof boundary.

### Why alternatives were deferred

- A cubic quadratic-character sum rewrites the point count, but the sharp
  character-sum estimate contains essentially the missing Hasse difficulty.
  No certified character-sum library makes it a smaller route here, and a
  prime-field-only Legendre-symbol formulation would unnecessarily narrow the
  theorem.
- A characteristic-polynomial proof through `pi + dual(pi)` and
  `pi*dual(pi) = [q]` aligns well with later Schoof work, but requires at least
  as much dual-isogeny infrastructure for the first Hasse endpoint.
- Coordinate descent could replace reusable degree theory with long bespoke
  identities.  It is not presently justified by the repository's generic
  finite-field goal or later Schoof seam.
- Broad rational-function, divisor, valuation, scheme, or general
  algebraic-geometry libraries are not authorized merely because they can
  support a classical proof.  Only the minimum representation demanded by the
  selected chain should be developed.

## Certified boundary at the audit baseline

The following are repository facts, not new claims from the mathematical
source:

- `books/field/kernel.lisp` supplies a total fixed-representative `GFIELD`
  interface and natural powers.
- `books/field/finite-field-context.lisp` jointly constrains field operations
  with bounded rank/unrank evidence.  It does not expose an exhaustive carrier
  list or identify its bound with `field-frobenius-exponent`.
- `books/algebra/finite-bijection.lisp` constructs an exhaustive,
  duplicate-free carrier and exact cardinality from a suitable bounded
  rank/unrank context.  Connecting that generic result to a particular field
  context is a separate interface step.
- PFIELD has certified exhaustive carriers and exact cardinalities; F7 and F11
  are concrete clients.
- the finite-field-prefixed polynomial books certify exhaustive fixed-modulus
  representatives and the count `q^n` for an explicit degree-`n` modulus.
  This representative result does not package those operations as the
  separate nullary irreducible fixed-modulus field.
- F7X2 is a concrete executable `GFIELD` client with a certified 49-element
  carrier.
- the curve books provide short-Weierstrass tagged points, the executable and
  relational addition layers, a contextual abelian group, and transparent
  natural scalar multiplication.
- generic polynomial derivative and the derivative-coprime square-free
  boundary are certified.
- `books/field/frobenius-exponent.lisp` supplies only a minimal assumed
  exponent/fixed-point certificate.  Its own contract does not identify the
  exponent as a cardinality, characteristic, prime power, or least exponent.

There is no certified ambient/base-field embedding, cardinality-derived
Frobenius theorem, curve Frobenius, rational-function or morphism equality,
isogeny degree, separable degree, dual isogeny, or Hasse theorem.

## The ambient/base-field obstruction

The existing generic curve points are coordinates in the one selected
`GFIELD`.  If that selected field is already `F_q`, then raising coordinates
to the `q`th power is extensionally the identity once the finite-field power
theorem is known.  Such an operation cannot simultaneously serve as the
nontrivial geometric Frobenius whose degree is `q`.

**Project decision.** Hasse design must therefore distinguish a finite base
field from an ambient field containing non-rational curve points.  This does
not decide whether the ambient object will eventually be an algebraic closure,
a constrained extension interface, a function field, or another purpose-built
semantic carrier.

### Correction: curve closure needs a homomorphism

An earlier audit suggestion incorrectly made base-field coefficient fixedness
sound sufficient for curve closure.  It is not.  Suppose an ambient point
satisfies

```text
y^2 = x^3 + A*x + B.
```

The ambient operation `Frob_q` must at least satisfy the relevant field
homomorphism laws:

```text
Frob_q(u + v) = Frob_q(u) + Frob_q(v)
Frob_q(u * v) = Frob_q(u) * Frob_q(v)
Frob_q(0) = 0
Frob_q(1) = 1
Frob_q(-u) = -Frob_q(u)       (when used by the chosen formulation)
Frob_q(A) = A
Frob_q(B) = B.
```

Applying `Frob_q` to the original equation and using these laws gives

```text
Frob_q(y)^2 = Frob_q(x)^3 + A*Frob_q(x) + B,
```

which is the curve equation for the image.  Fixedness of `A` and `B` alone
cannot distribute a power across the sums in the equation.

### Correction: the fixed-point converse is separate

An injective base-field embedding can support the easy direction once
base-field `q`-power fixedness is proved:

```text
embedded base-field element  ==>  ambient Frobenius-fixed element.
```

It does not prove the converse:

```text
ambient Frobenius-fixed element  ==>  embedded base-field element.
```

A normal realization proves that the `q` embedded elements are roots of
`T^q - T` and that a nonzero degree-`q` polynomial has at most `q` roots, or
provides an equivalent certified fixed-subfield interface.  The generic
polynomial stack has degree and evaluation infrastructure, but the audit found
no certified theorem that realizes this ambient fixed-subfield argument.
This stronger converse is indispensable for identifying Frobenius-fixed
ambient curve points with `E(F_q)`.

## Minimum candidate interface

The table classifies the minimum information that must be justified before a
Frobenius implementation boundary is selected.  “Small interface” means the
underlying mathematics appears certified but the needed composition has not
itself been checked as a public theorem.  “Proposed premise” is not permission
to leave an axiom permanently: a documented realization must eventually
discharge it.

| Interface item | Classification | Evidence or unresolved obligation |
|---|---|---|
| Finite base-field operations with bounded rank/unrank | Already available | The jointly constrained finite-field context supplies coherent field and coding operations. |
| Exhaustive duplicate-free base carrier of size `q` | Derivable by a small interface theorem | The finite-bijection theory supplies the construction from bounded rank/unrank; the exact field-facing packaging must be checked rather than assumed. |
| `q` positive and a prime power compatible with the characteristic | New mathematical development | Positivity follows from existing cardinality evidence in relevant contexts, but prime-power form and characteristic/cardinality compatibility are open. The public Hasse inequality may need only cardinality; Frobenius realization and inseparable degree may need the stronger metadata. |
| Ambient field | Unresolved design choice | No ambient-field or extension relationship is adopted. The minimum closure/perfectness/algebraic-closure strength must be determined. |
| Injective embedding from base to ambient | Proposed constrained premise requiring a documented realization | Injection alone is insufficient for fixed-subfield exhaustiveness. Concrete witnesses and generic realization obligations must be identified. |
| Embedding preserves zero, one, addition, multiplication, negation, and inverse where defined | Proposed constrained premise requiring a documented realization | These are the minimum field-homomorphism laws; their exact total/fixing semantics remain to be designed. |
| Ambient `q`-power Frobenius endomorphism | New mathematical development | It must be nontrivial on general ambient elements and must satisfy the homomorphism laws needed by curve closure. |
| Every embedded base element is Frobenius-fixed | New mathematical development | Requires base-field `x^q=x` derived from certified cardinality/characteristic facts and compatibility with the embedding. Cardinality must not simply be identified with the existing assumed Frobenius exponent. |
| Every ambient Frobenius-fixed element lies in the embedded base field | New mathematical development or proposed premise with realization | Requires the `T^q-T` root-exhaustion argument or an equivalent fixed-subfield theorem. Injection alone does not supply it. |
| Curve coefficients are embedded base elements | Derivable by a small interface theorem after the embedding is fixed | The chosen curve context must say how `A` and `B` enter the ambient curve and yield their Frobenius fixedness. |
| Frobenius preserves the short-Weierstrass equation | New mathematical development | Follows from ambient Frobenius homomorphism laws plus coefficient fixedness; it is not a consequence of fixedness alone. |
| Frobenius-fixed ambient curve points correspond exactly to `E(F_q)` | New mathematical development | Requires coordinate representation compatibility and both directions of the ambient scalar fixed-point theorem, including infinity. |
| Meaning of `E(F_q)` inside the ambient curve | Unresolved design choice | It might be an embedded finite point carrier, a coordinate predicate, or an isomorphic copy. Equality/fixing semantics must be explicit. |

No provisional ACL2 event names are assigned.  Naming an interface before its
carrier and fixing semantics are understood would falsely suggest a settled
design.

## Morphism and degree representation remains open

The selected mathematics eventually needs equality, addition, subtraction,
composition, kernels, separability, and degree for the maps containing
identity and Frobenius.  The audit considered, but did not adopt:

- normalized coordinate pairs of rational functions;
- a rank-two short-Weierstrass function-field representation;
- general rational maps;
- kernels plus separable degree; and
- an abstract endomorphism/degree interface with a later concrete realization.

Pointwise equality on the finite set `E(F_q)` is inadequate.  Two distinct
morphisms can agree on every rational point while differing on ambient points
and having different degrees.  Equality used by degree theory must therefore
be semantic over a sufficiently rich ambient domain or justified by a
canonical symbolic representation.

The first representation experiment must answer:

1. what ambient points and equality mean under ACL2 totalization;
2. how the base-field copy is recognized inside that carrier;
3. whether identity and nontrivial Frobenius can inhabit one map type;
4. whether map equality can be proved without evaluation on a finite carrier;
5. how zero, infinity, poles, composition, and cancellation would be treated;
   and
6. which concrete theorem will eventually realize any constrained premise.

No broad rational-function or isogeny library is authorized until this slice
shows which of those facilities the selected proof actually needs.

## Extension-field carrier/fixer bridge

**Project decision.** The bridge between the finite-field-prefixed exhaustive
`q^n` representative carrier and the separate fixed-modulus-field canonical
representatives remains a real open obligation.  It is deferred from the
immediate abstract Hasse critical path, not complete and not permanently
unnecessary.  It may later be required for generic quotient-field instances
of Hasse, for concrete realizations of the ambient/base-field interface, or for
Schoof.  The earlier extension-field audit is not reconstructed in this file;
see the [audit index](README.md) for the preservation status of that report.

## External-source limits and lessons

- Silverman's cited route is the mathematical authority selected above; its
  exact statements must be rechecked from the edition used when formal theorem
  statements are drafted.
- David Kurniadi Angdinata's public
  [*EllipticCurves* report repository](https://github.com/Multramate/EllipticCurves)
  was inspected as an explicit secondary exposition of inseparable isogenies,
  the quadratic degree form, Hasse, and Schoof.  It is a written mathematical
  report with Haskell material, not evidence of a Lean-certified Hasse theorem.
- Public mathlib material associated with elliptic curves, Frobenius, and
  division polynomials was inspected.  The audit did not find a completed Lean
  Hasse proof in that material; polynomial degree lemmas for division
  polynomials must not be confused with isogeny degree.
- The requested
  [Isabelle Schoof repository](https://git.logicalhacking.com/adbrucker/Schoof_Algorithm)
  was inaccessible
  through the audit environment (HTTP 403).  No Isabelle file, theorem, Hasse
  dependency, or proof-completeness claim is inferred from its title.

An external Schoof or SEA implementation should not be cited as proving Hasse
unless its inspected source contains that proof.  Host-prover libraries may
also account for dependencies that ACL2 should replace with a narrower local
interface rather than copy wholesale.

## Exactly one recommended next task

### Ambient/base-field feasibility specification

**Mathematical question resolved.** Determine whether a two-field ACL2 context
can state nontrivial ambient `q`-Frobenius, base-field fixedness, and the
fixed-point converse with explicit realization obligations, without first
building rational maps or general algebraic geometry.

**Exact intended endpoint.** Produce one explicitly experimental design book
and companion audit update that:

1. gives local candidate signatures for the base field, ambient field,
   embedding, `q`, and ambient Frobenius;
2. states the complete functional-instantiation obligations, including
   operation preservation and both fixed-point directions;
3. demonstrates consistency with one concrete finite extension witness or
   identifies the precise missing witness theorem; and
4. records a go/no-go decision for using that context in the first curve
   Frobenius slice.

No public Hasse or curve-Frobenius theorem is part of the endpoint.

**Likely files.** A narrowly named experimental book and regression/witness
book under a new or existing field design area, plus this audit and the live
ledger/plan if the experiment changes the decision.  Final paths should be
chosen only after checking include direction and package scope.

**Existing results reused.** The `GFIELD` kernel, finite-field coding context,
finite-bijection carrier/cardinality theory, field powers, characteristic
context, and concrete PFIELD/F7 or F7X2 clients.

**Proof obligations exposed.** Embedding injectivity and homomorphism laws;
cardinality/characteristic/prime-power compatibility; Frobenius homomorphism;
embedded-element fixedness; the converse fixed-subfield theorem; and all
fixing/congruence laws required for functional instantiation.

**Local or experimental scope.** Candidate constrained symbols, witness
functions, and exploratory signatures may remain local.  They must not be
advertised as adopted architecture or used to claim Hasse progress.

**Required witness.** At least one concrete, certified nontrivial ambient/base
pair must satisfy the proposed constraints, or the experiment must stop with
the exact unproved realization theorem recorded.  Execution alone is not a
consistency or semantic proof.

**Documentation impact.** Update adopted architecture only after a realizable
interface is selected.  Otherwise update this audit and the obligation ledger
with the diagnosed blocker; do not turn the experiment into forward-plan fact.

**Explicit exclusions.** No curve Frobenius, rational functions, morphisms,
degree, separability, isogenies, dual isogenies, Hasse theorem, division
polynomials, Schoof trace tests, CRT, nested general extension constructor, or
generic carrier/fixer bridge.

**Substantive stop condition.** Stop if the candidate either collapses ambient
Frobenius to the identity, assumes the fixed-point converse without a named
realization path, or requires an algebraic-closure/function-field library whose
necessity has not been demonstrated.  Record which premise caused the stop
rather than bundling the remaining field, curve, and Frobenius developments.

## Post-PR #309 bounded feasibility experiment (2026-08-08)

### Authoritative starting state

The experiment began on branch `work` at
`5a89c513bfb10fd5994453ea820edd33d0b61b17`, the merge commit for PR #309.
The worktree was clean, no remotes were configured, and the recent merged
baseline was PR #309 over PR #308.  Thus the F7X2 public `GFIELD` packaging and
49-element carrier audited by PR #309 were present.

### Candidate interface tested

A deliberately unregistered experimental book tested two independently fixed
operation families (base zero/one/add/mul/neg and ambient
zero/one/add/mul/neg), a fixed base embedding, a positive nullary `q`, ambient
power, ambient Frobenius, a base projection, and an image recognizer.  The
candidate constraints were:

- embedding stability under the base fixer and ambient-fixer closure;
- preservation of zero, one, addition, multiplication, and negation;
- injectivity stated as equality of embedded values iff equality of fixed base
  values;
- Frobenius stability under the ambient fixer, positivity of `q`, equality to
  ambient `q`-power, and preservation of addition and multiplication;
- fixedness of every embedded base value;
- image recognition as equality with the embedding of a fixed base projection;
- Frobenius fixedness iff that image predicate; and
- fixer stability of Frobenius and the image predicate.

The intended concrete definitions were the natural ones: F7 embeds as the
constant canonical residue class
`f7x2-fix(list(f7-fix(x)))`; `q` is 7; ambient power is repeated F7X2
multiplication; and Frobenius was tested both as seventh power and as the
coefficient conjugation `(a,b) -> (a,-b)` in
`F7[X]/(X^2+1)`.  The latter moves `X`, represented by `(0 1)`, to `(0 6)`, so
the proposed ambient map does not collapse to the identity.

### Outcome and first missing seam

**No certified experimental book is retained.**  The existing representations
are compatible with the natural constant embedding, and concrete evaluation
on the 49 canonical representatives agrees with conjugation, embedded-element
fixedness, and the expected seven-element fixed set.  However, evaluation is
not a theorem.

The first missing certified seam was a tractable theorem connecting existing
F7X2 repeated multiplication to the coefficient formula

```text
(a + bX)^7 = a - bX  (mod X^2+1).
```

Two bounded proof decompositions were attempted.  Direct exhaustive rewriting
of the 49 unary seventh-power cases, and a carrier-checker theorem that also
checked homomorphism laws, both expanded the current polynomial divmod-based
F7X2 operations without completing certification in repeated bounded runs.
Splitting the unary cases and replacing Frobenius by transparent coefficient
conjugation removed the binary seventh-power expansion but did not make the
seventh-power bridge certify.  No trust escape, unsupported constraint, or
execution-only replacement was retained.

The missing seam is now certified by `f7x2-seventh-power-is-conjugate`.  The
successful proof stays above the public multiplication projections, mirrors the
named square/fourth/seventh straight-line powers with a local coefficient-pair
calculation, exhausts the two F7 coefficients in 49 scalar cases, and
reconstructs the whole fixed value by coefficient extensionality.  Polynomial
multiplication, remainder, divmod, and the F7X2 fixer remain disabled throughout
the scalar and whole-value proof.  The fixed-point converse and candidate
functional instance remain absent rather than being admitted as constraints.

### Scope verdict

**NO-GO remains for the first curve-Frobenius slice.**  The certified F7X2
seventh-power formula resolves the first scalar seam but does not adopt the
two-field candidate as architecture.  The next bounded work must use the
existing exhaustive 49-element carrier to certify (not merely execute) the
fixed-point/image equivalence, and only then retry the functional instance.
This verdict does not authorize a generic extension-field constructor, the
deferred carrier/fixer bridge, or any curve, morphism, or degree theory.

Even a later successful F7/F49 witness would establish only consistency of the
base/ambient/Frobenius seam.  A single finite ambient extension need not contain
all geometric kernel points used by the eventual Hasse degree/kernel argument;
that argument may still require an algebraic closure, a sufficiently rich
family of extensions, or symbolic function-field semantics.
