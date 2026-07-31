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

`books/field/xcert-algebra.lisp` defines explicit output-coordinate residuals
and the field expressions `xcert-dx`, `xcert-telescope`, `xcert-remainder`,
`xcert-h`, `xcert-s`, and `xcert-c`.  The residuals are total expressions, not
assumed-zero hypotheses.  Certified component theorems establish the output
telescope and remainder identities, and `xcert-composition` combines those
components opaquely in the exact left-associated form.

`books/field/xcert-h-reconstruction.lisp` remains in the same field-only
layer.  Its public scalar theorem consumes exactly seven explicitly oriented
secant/output equations and the ordered nonzero factor `xc-xb`; proof-local
term-list normalization exposes the finite additive cancellations.  It adds no
executable definition or curve dependency.

`books/field/xcert-s-reconstruction.lisp` extends that field-only layer.  Its
public scalar theorem reuses the certified H equality and proves the remaining
finite residual with proof-local explicit sum normalization.  It retains the
ordered factors `xc-xb` for the H dependency and `xbc-xa` for final S
cancellation, and adds no curve or executable dependency.

The field-only book depends only on the generic field kernel.  The separate
`books/curve/xcert-semantics.lisp` bridge imports that book and the assembled
affine distinct-x output.  For inputs `A`, `B`, and `C`, it maps `xab` and `xbc`
to the x-coordinates of `AB = output(A,B)` and `BC = output(B,C)`, maps `xl`
and `xr` to the x-coordinates of `output(AB,C)` and `output(A,BC)`, and maps
`p,q,r,tt` to the ordered slopes `(A,B)`, `(AB,C)`, `(B,C)`, and `(A,BC)`.
It certifies the four residuals as zero from the existing output-x
rearrangement and specializes `D_x`, `H`, `S`, `C`, and the opaque composition.
It also instantiates the field-only scalar reconstructions with the ordered
curve slopes.  It certifies specialized `H` as zero from the three input curve
memberships and three relevant distinct-x classifications, and specialized
`S` as zero after adding only the fourth classification for `(A,BC)`.
The bridge adds no polynomial dependency and proves no associativity or
exceptional-case fact.

The bridge also certifies equality of the final x-coordinates of the two
untagged distinct-x trees under the four ordered distinct-x classifications.
This uses both semantic certificate-zero results through the maintained
composition.  The field-only final-y layer now contains the separate
output-x/H coordinate bridge `xl-xb=(q-r)(p+q)`; its proof has no curve or
nonzero premise.  Its separate six-residual y reduction derives the final
ordinate difference as two products from S-zero, three ordered slope equations,
and the two final output-y equations; the AB output-y equation is absent.  Their
composition is now certified as the field-only fixed final-y equality: the
coordinate bridge and maintained H equality substitute the two coordinate
differences, and a bounded opposite-product identity closes the result.  The
semantic theorem `xcert-final-y-coordinates-equal` instantiates that combined
field theorem from semantic H-zero and S-zero, the maintained slope and output
rearrangements, and a proof-local transport from final-right x to the already
equal final-left x.  The public theorem `xcert-untagged-outputs-equal` then
packages raw final-x equality and fixed final-y equality into equality of
`xcert-left` and `xcert-right`.  Generic accessor closure makes both actual y
coordinates fixed, and a proof-local affine-coordinate extensionality bridge
reconstructs the canonical outputs from their equal x and y accessors.
Semantic H/S zero, final x-coordinate equality, the output-x/H coordinate
bridge, six-residual reduction, combined field-only final-y reconstruction,
semantic final-y equality, untagged output equality, and tagged ordinary-output
equality remain distinct certified boundaries.  The tagged theorem uses the
same three curve-membership and four ordered `:distinct-x` hypotheses and lifts
the untagged theorem through `affine-distinct-x-output-point`; it replays no
coordinate or scalar algebra.  The separate ordinary affine-dispatcher theorem
`xcert-affine-dispatcher-outputs-equal` retains those exact seven hypotheses
and reduces its two outer calls through exactly two uses of the public
`:distinct-x` branch equation.  `xcert-tagged-outputs-equal` supplies all
semantic equality, so no coordinate or field algebra is replayed.  This does
not cover other affine classifier outcomes.  The separate
`xcert-full-point-dispatcher-associative-when-all-distinct-x` boundary lifts it
to two nested `curve-point-pair-output-point` trees whose leaves are
`curve-point-affine-coordinates` constructors for `a`, `b`, and `c`.  Under the
same three memberships and four ordered classifications, a proof-local inner
branch reduction and the public full-point affine/affine interface expose the
two affine dispatcher calls.  Their equality comes solely from
`xcert-affine-dispatcher-outputs-equal`; constructor and coordinate fixers are
removed by existing canonicality equations, with no semantic algebra replayed.
Exceptional classifiers, infinity inputs or results, arbitrary configurations,
unrestricted associativity, and group laws remain distinct open boundaries.

The ordered distinct-x theory also exposes the division-free input-secant
identity `slope*(y(second)+y(first)) = x(second)^2 +
x(second)*x(first) + x(first)^2 + a`.  It requires both ordered inputs to be
on the curve and that their classifier be exactly `:distinct-x`; its operand,
numerator, and denominator orientations are those of
`affine-distinct-x-slope` and are never silently reversed.  This is the first
reusable curve-level ingredient selected by the H/S audit, not an H- or S-zero
result.

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

### Associativity reduction boundary

Future associativity work is organized by semantic geometry, not by a Cartesian
product of dispatcher tags.  For valid affine inputs, equal-x curve points have
equal or opposite ordinates, so `:same-x-other` is unreachable.  An opposite-y
inner result crosses immediately to the full-point infinity interface; a
distinct-x or doubling result remains affine by branch closure.  These facts
determine whether an outer affine classifier even exists and constrain its
possible result.

Full commutativity supplies reversal symmetry and closes the all-equal
doubling/doubling composition, but it does not license cyclic reassociation.
Structural infinity, fixing, classifier, and representation reductions should
therefore be certified before new coordinate algebra.  The remaining algebra
belongs at the independent secant/doubling relation layer.  Candidate mixed
secant--tangent certificates should expose division-free line and curve
equations and derive exceptional outer outcomes rather than accepting four
unrelated classifier premises.  A shared branch-parametric certificate is an
architectural option only if its hypotheses and specialization remain
transparent; separate oriented certificates are preferable to an opaque
generalization.  Dispatcher associativity must ultimately be a lift through
semantic soundness, determinacy, closure, and canonical fixing, not a replay of
branch formulas.

The Stage 3 audit selects the existing semantic branch relations as the primary
exceptional-secants boundary.  In particular,
`affine-distinct-x-secant-relation-p` and `affine-doubling-relation-p` already
expose the required division-free line and output equations, while
`affine-opposite-y-infinity-relation-p` supplies the exceptional full-point
result.  `curve-point-addition-relation-p` is the correct eventual packaging
layer, but its internally selected quotient witnesses make it less suitable
for discovering and proving the scalar certificates.  No new chord predicate
is warranted unless an attempted relation-level proof reveals an equation that
these predicates cannot express.

Inverse translation and exceptional `D/D` composition are not presently one
certificate family.  Inverse translation is a short sign-reversal argument on
one secant or tangent witness, followed by a derived outer secant/doubling
split.  An outer-`O` `D/D` degeneration is instead a collinearity propagation
argument with one available nonzero secant denominator; an outer-`T`
degeneration replaces an outer secant equation by a tangent equation and needs
an independent-witness reconstruction.  The earlier proposed DD-T1 bridge was
incorrect: the secant result is the reflection of the chord's third
intersection, so equality of that result with the tangent input does not make
the secant witness a tangent witness.  The two inner secant witnesses and the
actual tangent witness must remain independent; the audited candidate for the
opposite-tree witness is `(p+t)-r`.  Its three certified distinct-x equations
are now packaged into the public semantic secant relation, with exact witness
`(field-sub (field-add (field-fix p) (field-fix t-slope)) (field-fix r))`.
This characteristic-independent, classifier-free DD-T outer distinct-x branch
is complete; the separate coincident-x/opposite-y analysis remains open.  A
common theorem should be introduced only if those oriented specializations
remain explicit and require no hidden nonzero premise.

The inverse/tangent specialization is certified at the semantic relation
boundary by `affine-inverse-tangent-translation`.  It negates the inner tangent
witness and derives an outer secant when fixed x differs, or outer doubling
when fixed x coincides.  The latter branch reconstructs the equal ordinate and
transports the tangent-domain fact across affine negation.  The derived `D/T`
disjunction excludes outer opposite-y without a classifier premise, extra
nonzero assumption, division, or new curve polynomial identity.

The inverse/secant specialization is likewise complete at that boundary.
`affine-inverse-secant-translation` negates the fixed inner witness and derives
an outer secant when the outer x coordinates differ, or outer doubling when
they coincide.  In the latter branch the inner output-y equation first proves
ordinate coincidence; the certified A-D4 equation supplies the tangent
numerator, and the characteristic predicate is used only through the existing
self-inverse exclusion theorem.  Thus the final D/T disjunction excludes outer
opposite-y without an outer classifier premise.  The branch equations remain
division-free, and all sign, square, reassociation, and fixing normalization is
proof-local.

The oriented outer-opposite `D/D` specialization is certified at the same
classifier-free boundary by `affine-dd-opposite-y-propagates-to-other-tree`.
Two inner distinct-x secant relations and the left outer opposite-y relation
derive the opposite outer relation.  Its sole multiplicative cancellation uses
the nonzero `(B,C)` secant difference; there is no outer denominator or outer
classifier premise.  The mirrored orientation is now exposed by
`affine-dd-opposite-y-propagates-to-left-tree`: it uses the public secant
operand-reversal and opposite-y symmetry interfaces plus reversed point order,
rather than a duplicate coordinate certificate.  This structural endpoint is
used by the characteristic-independent DD-T coincident-x boundary to turn a
temporary outer opposite-y alternative into a contradiction with the tangent
domain at `C`.

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
