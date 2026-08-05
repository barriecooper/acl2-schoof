# Execution boundaries

This document owns stable contracts between logical meaning and execution.
Representations and subsystem dependencies are in
[architecture.md](architecture.md); theorem status is in
[obligations.md](obligations.md).

## Evidence model

For an executable interface, keep these claims separate:

1. **Logical specification** — the mathematical meaning.
2. **Executable implementation** — the branch actually run by compiled ACL2.
3. **Correspondence invariant or theorem** — why execution implements the
   specification.
4. **Guard and termination verification** — why the executable path is
   admissible and safe for its declared guard.
5. **Execution regression** — evidence that a concrete path runs and returns
   expected values.

Guard verification does not prove semantic correctness, and a regression does
not replace a generic correspondence theorem. A new or changed public split
must document all applicable layers here.

## Totalisation and fixing

Public operations are total on ACL2 objects. Their intended carrier semantics
are expressed through fixers:

- `field-fix` maps arbitrary values to field representatives;
- polynomial normalization fixes coefficients, discards malformed tails, and
  removes trailing zeroes;
- fixed-modulus field fixing takes the canonical remainder;
- the affine-coordinate fixer maps malformed outer values to the fixed zero
  pair; and
- the tagged-point fixer maps malformed values to canonical infinity.

A theorem stated modulo a fixer is semantic equality of represented values, not
raw ACL2 equality. Raw equality is used only where canonicality or an explicit
canonical-input hypothesis justifies it.

## Canonical polynomial boundaries

Dense polynomial raw helpers may construct intermediate lists. Public GPOLY
operations normalize results, so canonical equality is the stable external
contract. Division, GCD, XGCD, modular inverse, and reduced arithmetic inherit
malformed-value behavior from normalization and total field operations. The finite-field-prefixed remainder/reduced interface mirrors that transparent totalisation over `finite-field-poly-remainder`: zero normalized modulus returns the normalized dividend, every remainder is canonical and fixed by normalization, and the reduced predicate is exactly the public fixer fixed-point relation.

The generic fixed-modulus field uses canonical remainder representatives.
F7X2 operations accept arbitrary ACL2 inputs, fix/reduce them, and return
canonical representatives. F7X2's inverse is an ordinary transparent,
guard-verified definition using the existing F7 modular inverse; the certified
fixed-modulus functional instance supplies semantic inverse evidence. Exact
F7X2 assertions establish execution only.

The generic fixed-modulus coefficient representation is likewise transparent
and guard verified.  Its coefficient count applies `nfix` to the normalized
modulus degree (and equals that positive degree in the certified context).  The
vector wrapper fixes its arbitrary input once, performs a single-pass traversal,
has exactly that many entries, and pads missing entries with actual field zero;
final zero slots remain present.  `fixed-modulus-reconstruct` only normalizes
its arbitrary dense coefficient list: it fixes encountered coefficients,
discards a malformed tail, and removes trailing zeroes.  It neither truncates a
long list nor reduces it modulo the fixed modulus.  Certified reconstruction
and fixer-level vector extensionality supply one inverse direction. The reverse
theorem requires a proper `coefficient-list-p` list of fixed entries whose
length is exactly the coefficient count. Reconstruction may remove its trailing
polynomial zeroes, but exact-length extraction restores those vector zero slots
literally. No arbitrary-vector fixing or long-input truncation is introduced.
Focused F7X2 evaluations cover zero, reduction, malformed values and tails,
padding, nonzero trailing coefficients, and trailing-zero recovery.

## Power fast/spec boundary

`DEF-POW-INSTANCE` generates a linear logical specification, a
square-and-multiply accumulator, and a public `MBE` wrapper. Public execution
fixes the base, applies `NFIX` to the exponent, and calls only the logarithmic
auxiliary. Negative or malformed exponents therefore have exponent-zero
semantics, and `0^0 = 1`.

Each productionized instance certifies an accumulator invariant and fast/spec
correctness before guard verification of the public wrapper. This applies to
the generic field and polynomial powers and their named PFIELD/F2/F7 clients.
There is no experimental unmatched fast branch.

## Field-only X-CERT logical layer

The X-CERT algebra book adds ordinary transparent total field expressions and
certified logical identities.  It introduces no `MBE`, attachment, alternate
executable branch, or new guard boundary.  Its residual generators are explicit
expressions and are not assumed to vanish; the curve-semantic bridge is
likewise a transparent logical layer.  It adds no executable branch or guard boundary; its four residual-zero results follow
from the total output-x rearrangement.

## Transparent executable interfaces

Most repository functions are ordinary transparent `DEFUN`/`DEFUND` events,
not logical/executable splits. Important examples include:

- PFIELD adapters and named F7/F11 field operations;
- generic and F7 polynomial division, GCD, XGCD, and modular inverse;
- generic field natural scaling and canonical polynomial differentiation;
- generic fixed-modulus operations and F7X2 arithmetic;
- affine and tagged-point fixers, constructors, accessors, and negation;
- affine classifiers, branch slopes and outputs; and
- `affine-pair-output-point` and `curve-point-pair-output-point`.

Verified guards and transparent definitions explain how these functions run.
Their semantic theorems, not transparency alone, justify mathematical claims.

`field-nat-mul`, `raw-derivative-aux`, and `poly-derivative` are transparent,
total, guard-verified definitions.  They have no alternate optimized branch or
logical/executable correspondence boundary.

`pfield-nat-mul` is likewise a transparent, guard-verified PFIELD adapter.  It
applies `nfix` to the scalar, fixes its field argument, and returns the
canonical modular product.  Its closed form on field one supports the logical
least-characteristic proof; it is not field enumeration or cardinality
metadata.

The generic and PFIELD characteristic predicates are transparent bounded
logical checks.  Their recursion checks only smaller scalar annihilation; it
does not enumerate field elements or certify field cardinality.

`pfield-natural-range-from-count` is the small project-local transparent range
used by PFIELD cardinality; it avoids importing the broad VL utility closure
for elementary list facts.  `pfield-elements` executes as the ascending
half-open range `[0,pfield-modulus)`, and `pfield-cardinality` is definitionally
`len(pfield-elements)`.  All three definitions are guard verified and have no
alternate executable branch.  Semantic cardinality follows from the
certified true-list, canonical-member, no-duplicates, unconditional
fixer-aware coverage, and exact-length theorems.  Literal F7/F11 list
evaluation and malformed-input checks are execution regressions, not
substitutes for those universal facts.

F7X2 finite-carrier functions are likewise ordinary transparent definitions.
`f7x2-rank` obtains total malformed-input semantics through the fixing constant
and linear coefficient projections.  `f7x2-unrank` decodes
`mod(nfix(k),49)`, so every input produces a fixed F7X2 representative and the
operation is periodic on natural indices modulo 49.  `f7x2-elements` maps this
decoder over indices 0 through 48, and `f7x2-cardinality` is definitionally the
length of that list.  The certified inverse, coverage, no-duplicates, and
length theorems establish the semantics; focused evaluations establish
execution evidence.  All five functions are guard verified and introduce no
alternate executable branch.

The generic `finite-field-*` coding context consists of constrained logical
symbols admitted with local Boolean field/coding definitions as consistency
witnesses only.  It adds no public Boolean runtime. PFIELD and F7 are ordinary
executable clients: explicit functional-instance evidence establishes semantics,
while focused evaluations establish execution only.  No generic carrier,
cardinality, attachment, or alternate executable branch is introduced.

The field-independent finite-bijection theory uses an ordinary transparent
half-open range with `nfix` start/count semantics, a transparent unrank-list
map, and transparent derived carrier and cardinality definitions.  Cardinality
is the carrier length, and its equality to the positive bound follows from the
bounded inverse laws and list proofs.  The generic contract requires rank after
unrank only for natural indices below the bound; arbitrary-input totalisation
is deliberately client-specific.  PFIELD continues to use its existing fixer
semantics and direct carrier, while F7X2 retains its stronger modulo-49 theorem
and existing carrier.  Their proving-instance regressions add no alternate
execution branch and do not replace the semantic inverse and carrier proofs.

The finite-field-prefixed polynomial core uses ordinary transparent definitions
generated from the existing GPOLY component templates; its raw helpers remain
inspectable and it introduces no `MBE`, `DEFEXEC`, attachment, or alternate
execution branch.  Because the underlying finite-field operations are
constrained, the family is a logical target.  Explicit functional instances
provide semantic evidence, while existing PFIELD/F7 functions and focused F7
evaluations provide execution evidence.  Verified guards do not replace the
semantic bridge.

Tagged point negation is the transparent total data transformation
`curve-point-neg`: it fixes its input once, preserves infinity, and changes
only the affine ordinate by `field-neg`.  It calls neither the curve classifier
nor an addition dispatcher.  `curve-point-fix-of-neg` and
`curve-point-neg-of-fix` state its canonical-output and fixing contracts;
closure and involution are separately certified.  Malformed inputs therefore
inherit the tagged-point fixer's canonical-infinity convention.

## Curve-addition correspondence

The executable dispatcher is intentionally not the logical specification.
Independent semantic branch relations omit the classifier and executable
formulas, and `curve-point-addition-relation-p` combines those relations without
calling either dispatcher.

For curve-point inputs:

- branch closure establishes executable output membership;
- dispatcher soundness establishes the full relation for the executable
  output; and
- fixed-output determinacy equates any semantic witness with that output after
  point fixing.

The dispatcher always returns a canonical tagged representation. This
canonical-output invariant is what permits raw executable commutativity after
semantic commutativity and determinacy are applied. Off-domain branch and
fallback executions remain total programming conventions, not geometric
claims.

Executable associativity follows the same separation.  Four applications of
dispatcher soundness, with closure for the two inner results, instantiate the
independent theorem `curve-point-addition-relation-associative`.  Its
fixed-output conclusion is converted to literal dispatcher equality only by
the canonical-output theorem
`curve-point-fix-of-curve-point-pair-output-point`.  The lift replays no
classifier case split or affine branch algebra.  Concrete F11 triples and
finite F7/F11 enumeration validate execution separately; they do not establish
semantic correctness.

Inverse correctness uses the same semantic separation.  The narrow theorem
`curve-point-addition-relation-p-of-point-and-neg` splits only the tagged
infinity/affine representation and establishes the independent opposite-y
relation with infinity output.  Dispatcher soundness and fixed-output
determinacy then give the executable right inverse; executable commutativity
gives the left inverse.  No dispatcher branch tree, secant algebra, or tangent
algebra is expanded in this lift.  Concrete F11 inverse checks are execution
regressions, not the proof of these laws.

Executable left cancellation is derived purely by translating an equality by
the executable negation, reassociating, and applying the executable inverse
and identity laws.  Right cancellation is then derived by executable
commutativity.  These algebraic proofs do not revisit the semantic addition
relation, dispatcher branches, classifiers, or affine/field proofs.

Abstract abelian-group packaging introduces no new geometric operation and no
new executable boundary.  The contextual generic interface is instantiated
with the already executable tagged-point operation, infinity, and negation;
its obligations are discharged solely by the independently certified public
closure, identity, inverse, associativity, and commutativity laws.  The
nullary context maps to `short-weierstrass-characteristic-p`, so functional
instances retain that hypothesis rather than asserting an unconditional group
law.  The packaging regression is logical reuse evidence, not a new execution
or performance claim.

## Natural scalar multiplication

Natural scalar multiplication is a transparent, guard-verified linear
recursive specification.  Both generic and curve operations totalise the
scalar with `nfix`, return identity/infinity at zero, and add the point on the
left at each successor.  It is deliberately not double-and-add; a future fast
implementation requires the distinct function `curve-point-fast-nat-mul` and
a certified correspondence theorem to `curve-point-nat-mul`. Focused concrete
regressions must demonstrate that the fast branch executes with practical
behaviour, but do not replace that correspondence proof.

## Guard and termination boundaries

Recursive polynomial division uses a certified strict decrease of the
canonical remainder measure. Concrete F7 recursion and its complete operation
chain have verified guards. GCD and XGCD reuse that division boundary;
nonrecursive wrappers do not constitute alternate algorithms.

Generated divmod cores additionally expose a `:RULE-CLASSES NIL` one-step
equation theorem for functional-instantiation proofs. It changes no executable
body and does not globally enable recursive unfolding; F7 execution is unchanged.

A `verify-guards` event establishes only guard correctness for the admitted
logical definition. Any staged `:verify-guards nil` generated for a power
instance remains acceptable only because the instance later supplies its
invariant, fast/spec theorem, dependency guard proofs, and final public guard
verification.

## Trust and scanner policy

The repository forbids skipped proofs, axioms, trust tags, executable
attachments, raw Lisp facilities, and equivalent escapes. The scanner is
intentionally lexical and also rejects prohibited spellings in comments and
strings. Ordinary sound ACL2 facilities such as `MBE`, `DEFEXEC`,
`ENCAPSULATE`, `VERIFY-GUARDS`, and functional instantiation are review
triggers rather than automatic violations.

The current project source uses `MBE` only through generated power instances
and contains no `DEFEXEC`, executable attachment, program-mode boundary, raw
Lisp inclusion, skipped proof, project axiom, or trust tag. Future changes to
this inventory must update this document and satisfy the evidence model above.

The finite-field monomial/scalar-division support layer adds only transparent logical definitions and theorems over constrained finite-field operations. It does not add MBE, DEFEXEC, attachments, raw Lisp, or coding/cardinality calls.

## Finite-field division-step substrate

The finite-field-prefixed one-step polynomial division substrate is certified.
It uses transparent generated definitions for the core step and public term/next
projections, with verified guards, reconstruction, strict degree decrease, and a
strict core length theorem suitable for the future recursive divmod measure.  The
decisive cancellation proof is length/leading-coefficient based, not
coefficient-vector or coding based.  Recursive finite-field divmod and public quotient/remainder APIs are transparent generated definitions with verified guards and public correctness from accumulator invariants. The finite-field public remainder/reduced representative layer is also transparent and guard verified, adding no alternate executable branch. The finite-field fixed-modulus coefficient representation is transparent and guard verified: it fixes an arbitrary polynomial input with `finite-field-poly-remainder`, emits exactly one fewer slot than the normalized modulus length when the normalized modulus is nonzero, pads missing slots with finite-field zero, returns `nil` at normalized-zero modulus, and reconstructs vectors by finite-field normalization. Exact-width coefficient-vector coding is now a transparent total mixed-radix layer: ranking reads each fixed coefficient digit, malformed coefficient entries inherit `finite-field-rank` fixing semantics, unranking uses `nfix` on the code and returns `nil` at width zero, and the in-range inverse theorem is stated below the radix power bound. Carrier construction and cardinality remain open.
