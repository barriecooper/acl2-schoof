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

PFIELD supplies canonical prime-field representatives. Named F2, F7, and F11
clients provide executable instances and regression evidence. Concrete
instances validate functional instantiation and execution, but generic claims
come only from the generic certified books.

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

The certified stack is layered: arithmetic and evaluation; degree and leading
coefficient; division and remainder; congruence and reduced operations;
Euclidean and extended Euclidean GCD; logical irreducibility and modular
inverse. The HS/PFIELD polynomial layer is retained for concrete/root-count
bridges, not as a parallel home for new algorithms.

### Fixed-modulus quotient fields

The generic fixed-modulus construction constrains a nullary, canonical,
irreducible positive-degree modulus. Elements are canonical remainders and the
fixer is remainder modulo that modulus. Addition, negation, subtraction, and
multiplication use reduced operations; inverse is the total XGCD-derived
candidate with an explicit zero case. Certified irreducibility results provide
the nonzero inverse law.

F7X2, representing `F7[x]/(x^2+1)`, is a concrete proving instance. It should
not be confused with the reusable constructor or treated as an arbitrary
finite-field package.

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

## Present algebraic-law layer

For full tagged-point addition, the certified layer includes output closure,
left and right infinity identity, addition of a point and its negation to
infinity, semantic operand-reversal commutativity, and raw dispatcher
commutativity. The raw dispatcher theorem is possible because executable
outputs are canonical; semantic statements otherwise use fixer-level equality.

Associativity, cancellation, group or abelian-group packaging, and scalar
multiplication are absent. Until associativity is certified, documentation must
not call the dispatcher a certified group law.

### Associativity certificate boundary

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

D/D and the certified branches of oriented D/T demonstrate this architecture:
small scalar endpoints are reconstructed first, then packaged into a semantic
relation without replaying algebra. The complete current boundary matrix is in
[associativity status](status-associativity.md), and the mixed D/T derivation,
cancellation inventory, and countermodel are in the
[mixed D/T audit](audits/mixed-dt-certificate.md). These changeable completion
details are deliberately not architecture.

Semantic associativity must be assembled before any unrestricted executable
claim. The final dispatcher theorem is a representation lift through semantic
soundness, determinacy, closure, and canonical fixing; it is not a proof by
expanding branch formulas. Guard verification and execution regressions remain
separate evidence under [execution boundaries](execution-boundaries.md).

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
