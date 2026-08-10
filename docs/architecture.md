# Architecture

This document owns the stable design of the formalization. Exact proved and
open status belongs in the [obligation ledger](obligations.md), execution
contracts in [execution boundaries](execution-boundaries.md), and future
ordering in the [proof plan](proof-plan.md).

## Algebraic layers

### Generic fields and concrete adapters

`GFIELD` is the constrained equational field kernel. Every public operation has
total ACL2 semantics through `field-fix`; field laws therefore state equality
of fixed representatives where arbitrary ACL2 inputs are admitted. Natural
power, generated power correspondence, characteristic exclusions, and the
minimal Frobenius-exponent certificate extend this kernel without asserting a
field cardinality or an executable enumeration.

Field characteristic is a separate transparent contextual boundary.
`field-characteristic-p` combines annihilation of field one with a bounded
recursive check of every smaller positive scalar; no Skolem witness is used.
PFIELD is a functional instance of this generic theory, with
`pfield-modulus` as the least additive period, and F7/F11 inherit that PFIELD
boundary.  No independent parallel characteristic predicates are part of the
architecture.  This boundary does not strengthen the `GFIELD` encapsulate and
implies neither finiteness nor cardinality; it remains distinct from field
enumeration and `field-frobenius-exponent`.

PFIELD supplies canonical prime-field representatives. Named F2, F7, and F11
clients provide executable instances and regression evidence. Concrete
instances validate functional instantiation and execution, but generic claims
come only from the generic certified books.

PFIELD also supplies a transparent executable enumeration of its canonical
integer residues.  Its cardinality is defined as the length of that named
carrier list, whose true-list shape, canonical membership, absence of
duplicates, and unconditional coverage through `pfield-fix` are certified.
F7 and F11 inherit this evidence and execute as the expected lists of seven and
eleven residues.  This does not change `GFIELD`, identify characteristic with
cardinality generically, or establish generic or extension-field cardinality.
The actual-cardinality Frobenius theorem remains a separate open boundary, as
does the older, weaker `field-frobenius-exponent` interface.

### Bounded finite-bijection evidence

The field-independent bounded finite-bijection context constrains only a
fixer, rank, unrank, and positive bound.  Natural bounded ranks, fixed unrank
outputs, and the two inverse laws on the fixed carrier and bounded natural
indices make that bound sound cardinality evidence.  The theory transparently
maps unrank over a neutral half-open natural range, derives an exhaustive
duplicate-free carrier, and defines cardinality as the length of that carrier
before proving that the length equals the bound.

PFIELD and F7X2 are proving clients without changing their existing executable
carriers or total semantics.  In particular, only bounded rank-after-unrank is
generic: arbitrary-input unrank totalisation remains client-specific.  The
context is independent of `GFIELD` operations despite sharing the project
package, and adds no field, characteristic, polynomial, or Frobenius premise.
Generic coefficient reconstruction and extension cardinality remain open.

A separate `finite-field-*` context jointly constrains a renamed field-shaped
interface with coherent bounded rank, unrank, and bound operations.  It does not
extend the unrestricted `field-*` model: instead, its field laws make it a
functional instance of the generic kernel, while its coding laws specialize the
field-independent finite-bijection assumptions.  A local Boolean field is only
a consistency witness; PFIELD and F7 are proving clients.  The context exposes
no generic carrier or cardinality.  The GPOLY stack now has a
finite-field-prefixed polynomial core target over the renamed operations.  Its
recognizers, normalization, evaluation, coefficient projection, degree,
leading coefficient, and additive/multiplicative operations are ordinary
transparent definitions generated from the existing component templates where
available.  Narrow GPOLY semantic theorems are transported by explicit
functional instantiation; unrestricted GPOLY remains authoritative, and PFIELD
and F7 remain the executable clients.  Finite-field-prefixed division,
remainder, and fixed-modulus representation remain open.

The polynomial and division-polynomial definitions depend mathematically only
on the carrier/fixer, constants, arithmetic, inverse, and field laws.  ACL2's
functional-instantiation dependency is currently broader: the joint
`finite-field-*` encapsulate also constrains rank, unrank, and bound, and its
coding inverse laws mention the algebraic fixer.  Consequently, substituting
the algebraic symbols inherits coding obligations even when a client theorem
does not use coding operations.  The complete PFIELD-derived F11 instance is
certified with `f11-fix` as fixer, rank, and unrank and 11 as bound.  Its
conjunctive constraint seam certifies consistency and specialization, but an
actual polynomial functional-instance checkpoint still exposes the individual
joint constraints and stops at multiplication congruence.  A separately named
algebra-only constrained family is therefore the next architecture experiment;
the existing coding context remains authoritative for finite clients.

### Field-only X-CERT algebra

`books/field/xcert-algebra.lisp` defines total field expressions for the output
residuals and `xcert-dx`, `xcert-telescope`, `xcert-remainder`, `xcert-h`,
`xcert-s`, and `xcert-c`. The component identities and their opaque composition
form a field-only algebra layer: residuals are explicit expressions, never
assumed-zero hypotheses, and the layer has no curve, polynomial, classifier,
or executable dependency.

Reconstruction books expose small scalar interfaces for H, S, and the final
ordinate. Curve-semantic bridges instantiate those interfaces with ordered
secant/doubling relations and common-curve facts. Operand orientation and
nonzero factors remain explicit; proof-local normalization and cancellation do
not leak into the public semantic relation. This separation lets certificate
algebra be reused without treating a concrete curve regression as generic
proof.

The ordinary all-distinct-x tree is already connected through coordinate,
untagged, tagged, affine-dispatcher, and full-point boundaries. Exceptional
D/D and oriented D/T work uses the same design: certify division-free scalar
endpoints, then package them into semantic relations without replaying the
algebra. Exact completion status belongs in
[associativity status](status-associativity.md); the specialized mixed D/T
residual staging belongs in its [audit](audits/mixed-dt-certificate.md).

The ordered input-secant identity preserves the numerator and denominator
orientation of `affine-distinct-x-slope`. Reversal must use a certified symmetry
theorem rather than silently commuting operands. This is a stable interface
rule for every future X-CERT specialization.

### Canonical dense polynomials

`GPOLY` is authoritative for new polynomial algebra. A polynomial is a dense
constant-first coefficient list. `normalize` fixes coefficients and removes
trailing zeroes; `nil` is the unique canonical zero. Public arithmetic returns
canonical polynomials, while raw helpers exist only to support definitions and
proofs. Polynomial equality in the generic layer is literal equality of
canonical representatives, not merely agreement under evaluation.

Generated recursive divmod instances expose a named, non-rewriting one-step
equation theorem for functional-instantiation constraints. The public divmod
interface consumes it without globally unfolding the recursive core; generic
GPOLY remains the source of division semantics.

`poly-coefficient` is a total projection: indices are totalized with `nfix`,
represented values are field-fixed, and absent coefficients or coefficients
beyond a malformed dotted tail are field zero.  Normalization preserves every
coefficient.  Canonical dense polynomials are therefore literally equal when
their represented coefficients agree through the maximum of their lengths.
Polynomial addition and scaling have unconditional coefficient laws, while
`poly-mul` is characterized coefficientwise by the transparent finite
convolution `poly-convolution-sum`.  `poly-derivative` is characterized by
shifted natural coefficient scaling.  Canonical extensionality is the boundary
for lifting such coefficient identities to literal polynomial equality.
The derivative product rule is proved coefficientwise through finite convolution and canonical extensionality.

The certified stack is layered: arithmetic and evaluation; degree and leading
coefficient; division and remainder; congruence and reduced operations;
Euclidean and extended Euclidean GCD; logical irreducibility and modular
inverse. The HS/PFIELD polynomial layer is retained for concrete/root-count
bridges, not as a parallel home for new algorithms.

Formal differentiation also belongs to `GPOLY`.  `field-nat-mul` interprets a
natural coefficient index by total additive scaling in `GFIELD`, and the
transparent `poly-derivative` fixes coefficients, discards malformed atomic
tails, and normalizes its constant-first result.  Derivatives are canonical and
obey the additive, negation, and subtraction laws.  Exact degree decrement is
characteristic-sensitive: a leading natural multiplier can vanish, and in
positive characteristic a zero derivative does not imply that a polynomial is
constant.

`poly-square-free-p` is the total derivative-coprime predicate: it compares
the monic GCD of a polynomial and its formal derivative with canonical
polynomial one.  It rejects represented zero, accepts nonzero constants, and
inherits normalization semantics on arbitrary ACL2 inputs.  The explicit
relation `poly-has-square-divisor-p` records a supplied positive-degree square
divisor, and square-free polynomials are certified to admit no such divisor in
any characteristic.  The converse repeated-factor characterization and
root-based separability are not yet certified.

### Fixed-modulus quotient fields

The generic fixed-modulus construction constrains a nullary, canonical,
irreducible positive-degree modulus. Elements are canonical remainders and the
fixer is remainder modulo that modulus. Addition, negation, subtraction, and
multiplication use reduced operations; inverse is the total XGCD-derived
candidate with an explicit zero case. Certified irreducibility results provide
the nonzero inverse law.

F7X2, representing `F7[x]/(x^2+1)`, is a concrete public `GFIELD` proving
instance.  Its existing executable operations satisfy the complete nullary
kernel constraint set, with the nonzero inverse law inherited through the
fixed-modulus field functional instance.  It should not be confused with the
reusable constructor or treated as an arbitrary finite-field package.

F7X2 has a presentation-specific mixed-radix finite bijection.  Rank reads the
fixed constant and linear coefficients as radix-7 digits, while unrank decodes
`mod(nfix(k),49)`.  Mapping unrank over the indices 0 through 48 gives a
certified exhaustive duplicate-free executable carrier; F7X2 cardinality is
definitionally its length.  The resulting order is an execution convention,
not a semantic property.  Generic extension cardinality remains open.

Fixed-modulus representatives also have a generic exact-length coefficient
representation.  `fixed-modulus-coefficient-vector` fixes its arbitrary input
once, then emits the modulus degree's coefficients in ascending order, padding
short representatives with field zero and retaining those final zero slots in
the vector.  `fixed-modulus-reconstruct` separately normalizes that dense list,
and reconstruction of an extracted vector is the canonical remainder fixer.
Conversely, reconstructing and then extracting any proper coefficient list of
exactly the modulus degree recovers that list literally. Thus extraction then
reconstruction equals the quotient fixer, while reconstruction then extraction
equals the original canonical vector. Re-extraction restores trailing vector
zero slots removed by polynomial normalization. Equality of vectors implies
equality through the fixer; generic mixed-radix coding and extension
cardinality remain open beyond this representation boundary.

## Curve representations

The initial curve layer uses constrained short-Weierstrass coefficients and
total field operations.  The generic `GFIELD` interface remains unrestricted
by characteristic, because F2 and generic polynomial and quotient-field work
are legitimate clients.  The curve-level predicate
`short-weierstrass-characteristic-p` is the single explicit boundary for the
initial characteristic-greater-than-three model: it asserts that the canonical
field numerals two and three, expressed with the actual `field-*` operations,
are nonzero.  It also certifies the characteristic-dependent consequence that
a self-inverse field element is zero.

ACL2 cannot add assumptions about already constrained `GFIELD` symbols merely
by including a second encapsulate: a genuinely assumption-free constrained
extension would have to duplicate or regenerate the complete field signature.
The current least-invasive architecture therefore keeps existing
characteristic-independent curve definitions and theorems unchanged and uses
one named predicate premise only for results which need the restricted scope.
`short-weierstrass.lisp` includes that interface at the common equation root,
without making curve membership itself depend on it or changing executable
addition.  The nonzero standard discriminant remains the coefficient
constraint.

The short equation and its displayed derivative remain meaningful in
characteristic three (where the `3*x^2` term vanishes), so the checked-in basic
formulas alone do not force a characteristic-three exclusion.  Nonzero three
is nevertheless part of the declared first curve boundary to match the
project's characteristic-greater-than-three scope and avoid committing future
division-polynomial and Schoof work to small-characteristic special cases.
Characteristic two requires a different general Weierstrass model; supported
small-characteristic theories may be added separately later.

The dependency cut is deliberate.  Generic field fixing, affine/tagged
representations, the curve equation as a predicate, secant-only identities,
classifiers, dispatchers, semantic relations, structural associativity,
X-CERT, inverse/tangent, and DD-O retain their existing statements because
their certified proofs do not require nonzero two or three.  Tangent and
exceptional nonsingularity arguments that actually eliminate self-inverse or
repeated-root degenerations are the first consumers of the named premise.
Concrete F7 and F11 regressions discharge it directly.  F7X2 also discharges
it concretely through its quotient operations; a reusable theorem that an
arbitrary fixed-modulus extension inherits the base-field characteristic is
still open and should precede generic extension-field curve instantiation.

An **affine coordinate** is a canonical two-element list `(x y)` after field
fixing. Structural recognition is separate from satisfaction of the curve
equation. The affine fixer maps malformed outer values to the fixed zero pair;
it does not manufacture an on-curve point.

A **tagged curve point** is either canonical infinity `(:infinity)` or an
affine tag `(:affine (x y))`. Structural point recognition remains separate
from curve membership. The point fixer maps malformed tagged values to
infinity. Consequently public operations are total, and malformed inputs have
specified fixer-induced behavior rather than an implicit precondition.

Point negation fixes its input, preserves infinity, and negates the affine
`y` coordinate. Its involution and curve-membership results are modulo fixing;
raw equality follows when the input is already canonical.

## Full tagged-point addition layers

The addition development deliberately keeps execution and semantics separate.
The following names refer to different layers and should not be conflated:

1. **Branch classifier.** `affine-pair-classify` classifies fixed affine inputs
   as `:distinct-x`, `:opposite-y`, `:same-point-non-opposite`, or
   `:same-x-other`. Its ordering makes identical self-inverse points select the
   opposite-y branch. Classification is total and structural, including for
   off-curve inputs.
2. **Executable branch outputs.** Total slope and coordinate functions compute
   the distinct-x and doubling formulas. Tagged wrappers produce affine points
   or infinity. Outside a branch hypothesis, their values are programming
   semantics and are not geometric claims.
3. **Dispatchers.** `affine-pair-output-point` selects an affine branch;
   `curve-point-pair-output-point` first handles infinity and then delegates the
   affine/affine case. Both are transparent total executable operations. The
   affine fallback to infinity is unreachable for two on-curve affine inputs.
4. **Semantic branch relations.** Division-free relations independently state
   the secant, doubling, opposite/inverse, and ordered infinity cases. They do
   not call the classifier, slopes, executable outputs, or dispatcher.
5. **Independent full addition relation.** `curve-point-addition-relation-p`
   is the five-case semantic specification over two inputs and an output. It is
   independent of classifier priority and executable dispatch.

Branch soundness and case coverage prove that the dispatcher satisfies the
full relation for curve-point inputs. Fixed-output determinacy proves that two
semantic witnesses have equal fixed outputs. These theorems are the semantic
bridge to execution; guard verification alone is not that bridge.

## Algebraic-law architecture

The independent addition relation is the proof interface for geometric laws.
The executable dispatcher is connected to those laws through soundness,
determinacy, closure, and canonical fixing. Associativity therefore crosses
the same semantic-to-executable boundary as commutativity and inverse; it is
not established by expanding nested dispatcher branches.

### Associativity certificate organization

Associativity is organized by semantic geometry rather than a Cartesian
product of dispatcher tags. For valid affine inputs, equal-x curve points have
equal or opposite ordinates, opposite-y results cross to the tagged infinity
interface, and secant or doubling results remain affine by closure. Structural
fixing, symmetry, infinity, and representation reductions precede coordinate
algebra.

The proof interface is the existing division-free semantic relations:
`affine-distinct-x-secant-relation-p`, `affine-doubling-relation-p`, and
`affine-opposite-y-infinity-relation-p`. They expose line, curve, and output
equations without importing classifier priority, quotient computations, or
executable formulas. X-CERT remains a field-only algebra layer; curve books
supply the common-curve hypotheses that make its residual certificates
semantically applicable.

Certificate families reconstruct small scalar endpoints and then package them
into semantic relations without replaying their algebra. The family matrix is
maintained in [associativity status](status-associativity.md); residual
derivations and historical proof-engineering evidence remain in the
[associativity audits](audits/).

### Contextual abelian-group and scalar architecture

The generic abelian-group interface uses an explicit carrier predicate,
ordinary ACL2 equality, constrained identity, inverse, and binary operations,
and a nullary context predicate. Functional instantiation preserves the curve
context `short-weierstrass-characteristic-p` while reusing the executable
tagged-point operations. This avoids an unconditional group claim and avoids
the irrelevant finite operation-table representation of finite-group
libraries.

Natural repeated addition follows the same generic-to-curve path:

```text
abelian-group-nat-mul
    generic transparent specification
             ↓ functional instantiation
curve-point-nat-mul
    executable curve reference specification
             ↓ future correspondence theorem
curve-point-fast-nat-mul
    future optimized implementation
```

The reference specification is intentionally linear. Its simple recursion is
the logical baseline for algebraic laws and functional instantiation, while a
future double-and-add operation remains a separate implementation rather than
a redefinition of the specification. Totalisation, recursion orientation,
guards, and correspondence evidence belong in
[execution boundaries](execution-boundaries.md#natural-scalar-multiplication).

## Design constraints for later work

- Preserve total fixer semantics at public ACL2 boundaries and state clearly
  when equality is raw or modulo fixing.
- Keep generic theorems separate from concrete F7/F11 execution regressions.
- Do not replace an independent semantic relation with the executable
  dispatcher or its classifier.
- Keep guard/termination assurance separate from semantic correctness.
- Extend `GFIELD`/`GPOLY` rather than duplicating new algebra in HS/PFIELD.
- Treat the Hasse and Schoof developments as downstream tracks sharing the
  field, polynomial, curve, and Frobenius foundations; neither track is a
  prerequisite for the other after that seam.

Finite-field monomial/scalar-division support is now certified in the staged GPOLY target: scalar division, zero-prefix, shift, monomial degree/leading-coefficient facts, and scalar nonzero/division-denominator support are available without using finite-field coding/cardinality operations. The finite-field division-step substrate and recursive divmod/projection bridge are certified; the public remainder/reduced-polynomial layer is certified.  The finite-field fixed-modulus coefficient representation now extracts exact-width padded coefficient vectors from the canonical finite-field remainder and reconstructs by finite-field normalization; coefficient-vector rank/unrank is a separate certified mixed-radix boundary; carrier construction and cardinality remain separate.

## Finite-field division-step substrate

The finite-field-prefixed one-step polynomial division substrate is certified.
It uses transparent generated definitions for the core step and public term/next
projections, with verified guards, reconstruction, strict degree decrease, and a
strict core length theorem suitable for the future recursive divmod measure.  The
decisive cancellation proof is length/leading-coefficient based, not
coefficient-vector or coding based.  Recursive finite-field divmod and public quotient/remainder APIs are certified by direct accumulator invariants; fixed-modulus coefficient representation is now certified; coding/cardinality operations remain open and are not introduced here.

## Hasse ambient-point and degree architecture

The adopted Hasse representation is a narrow hybrid, as justified by the
[ambient-domain and degree-representation audit](audits/ambient-domain-and-degree-representation.md).
Geometric point semantics and symbolic morphism semantics are separate
boundaries:

- Frobenius fixedness and the `ker(1-pi)`/degree bridge use a separate
  point-level seam.  Its exact carrier remains an open realization question.
  Once fixed-subfield equivalence is established, the directly counted kernel
  is the embedded copy of `E(F_q)`; this dependency alone does not require a
  directed union of extensions.  Such a union or an algebraic closure remains
  a sufficient candidate if a general geometric-kernel theorem is selected.
- Equality, composition, separability, and degree use a canonical symbolic
  representation backed by the rank-two short-Weierstrass function field.
  Equality on the finite base-field point set is never map equality.
- An abstract endomorphism/positive-degree package may isolate the arithmetic
  consumer during development, but public Hasse must instantiate it with the
  certified symbolic maps and geometric kernel bridge.  A false context guard
  or the F7/F49 feasibility witness is not such a realization.

The adopted stable decision is the symbolic/point-level representation split,
not a directed extension family or other specific point carrier.  The
experimental two-field books remain unchanged evidence.  Their separate scalar
carriers, embedding, and embedded-image proposition are sound concepts;
the base projection and explicit nonidentity witness are not required generic
primitives.  Production `q` must be connected to certified base cardinality,
characteristic, and prime-power metadata.

This architecture intentionally does not put algebraic closures, general
geometric points, rational-map degree, or dual-isogeny theory on executable
Schoof's critical path.  Schoof may use division polynomials and quotient
coordinates over finite rings independently.  Shared work ends at finite-field
metadata, polynomial/fixed-modulus arithmetic, curve formulas, fixing
contracts, and the particular Frobenius laws demanded by both clients.


## Schoof division-polynomial representation

The executable Schoof track uses dense ascending-coefficient univariate polynomials in `x` over the constrained finite field.  For the short-Weierstrass equation `y^2 = x^3 + ax + b`, odd entries represent `psi_n`; even entries represent `psi_n/(2y)`.  Thus `psi_2 = 2y` is stored as the constant one.  This convention avoids a bivariate or rational-function layer while retaining the data needed by the standard odd/even recurrences and later trace tests.  It is the convention used by the certified base boundary through index four.

Natural integer constants are embedded by repeated finite-field addition of one; curve coefficients are fixed before use.  Dense coefficient order is ascending.  The retained formulas are

- `psi_0 = 0`, `psi_1 = 1`, and stored `psi_2/(2y) = 1`;
- `psi_3 = 3x^4 + 6ax^2 + 12bx - a^2`; and
- stored `psi_4/(2y) = 2x^6 + 10ax^4 + 40bx^3 - 10a^2x^2 - 8abx - 2a^3 - 16b^2`.

These are the standard division-polynomial initial values (Silverman, *The Arithmetic of Elliptic Curves*, division-polynomial formulas), algebraically adjusted only by removing `2y` from the even value.  Their elliptic-curve interpretation is restricted to the repository's short-Weierstrass characteristic-not-two-or-three scope.  The polynomial functions themselves remain total in every constrained finite field: `nfix` handles the index, field fixing handles `a,b`, and unsupported indices return the zero polynomial.

The first recurrence boundary is a transparent step over an ascending list of
already established entries.  Write `C=(2y)^2=4(x^3+ax+b)`.  Starting from the
standard identities
`psi_(2m+1)=psi_(m+2)psi_m^3-psi_(m-1)psi_(m+1)^3` and
`psi_(2m)=(psi_m/(2y))(psi_(m+2)psi_(m-1)^2-psi_(m-2)psi_(m+1)^2)`, substitute
`psi_k=F_k` for odd `k` and `psi_k=(2y)F_k` for even `k`.  If `m` is even, the
first odd product contains four factors of `2y`, giving `C^2` on that product;
if `m` is odd, the second product contains them instead.  In the even identity
the common factors cancel to the same stored formula in both parities.  This
derivation records the source and representation transformation; it is not a
formal bridge to a bivariate classical definition, which remains open.

The retained step uses `nth` only as a transparent table access.  The certified
sequential builder produces the ascending table through `nfix(n)`, binding its
single recursive prefix before extending it with one recurrence-step result.
Exact length, true-list output, newest-entry, stable lower-index lookup,
in-range access, coefficient/index fixing, and entry closure are certified.
Each polynomial is therefore constructed once; the transparent list extension
still traverses the prefix and carries the corresponding list cost.

The initial base computation needs normalization and coefficient-field arithmetic only.  It does not use quotient coordinates, so it creates no justification for another reduced-ring law.  The exact separated-`2y` recurrence step and its odd/even equations are certified.  A named recurrence-and-length sequence relation and transparent public evaluator expose fixing, closure, base values, and evaluator-only recurrence equations.  The generated table satisfies that relation, and every satisfying table agrees entrywise with the evaluator throughout its declared range.  This stored-sequence correspondence is not a correspondence with classical bivariate division polynomials, which remains open.
