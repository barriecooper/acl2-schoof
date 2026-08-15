# Arbitrary-field executable Schoof architecture audit

## Scope and inspected baseline

This documentation-only audit was made at `ba852f3`, the merge of PR #360.
It asks what the repository actually certifies, rather than treating a name or
an executable example as an interface promise.  The inspected material was
`books/top.lisp`; the production and regression books named below and their
includes/consumers; `docs/architecture.md`, `docs/proof-plan.md`,
`docs/obligations.md`, `docs/execution-boundaries.md`; the maintained audits;
and the finite-field, polynomial, Hasse, and Schoof design notes.  No ACL2
event is added by this audit.

The target is one certified executable which receives a supported finite-field
description and short-Weierstrass coefficients, does not enumerate curve
points, and returns the cardinality of the independently specified finite set
of rational curve points.  “Arbitrary” therefore means arbitrary valid member
of an explicit, certified descriptor family at run time.  It does **not** mean
only that a developer can create and certify a new nullary ACL2 instance.

## Repository inventory and classification

The classifications below deliberately distinguish transparent functions with
ordinary data arguments from constrained, nullary-operation theorem contexts.

| Component | Exact certified evidence | Classification and limit |
|---|---|---|
| Equational field | `books/field/kernel.lisp`: constrained `field-element-p`, `field-fix`, `field-zero`, `field-one`, `field-add`, `field-neg`, `field-mul`, `field-inv`; derived `field-sub`, `field-div`, `field-pow`, and field laws | **Reusable constrained theorem layer** (`GFIELD`). Operations are first-order nullary/unary/binary symbols, not descriptor arguments. It has no carrier, order, or characteristic. |
| Generic polynomials | `books/polynomial/generic/base.lisp`, `add.lisp`, `mul.lisp`, `division.lisp`, `euclidean.lisp`, `xgcd.lisp`, `reduced-ring.lisp`, `irreducibility.lisp`, `fixed-modulus-field.lisp`; notably `poly-normalize`, `poly-divmod`, `poly-remainder`, `poly-monic-euclidean-gcd`, `poly-extended-euclidean-gcd`, and `fixed-modulus-field-*` | **Reusable constrained theorem layer** (`GPOLY`), with executable definitions after functional instantiation. `fixed-modulus-field-modulus` is constrained and nullary, so this is not a run-time descriptor package. |
| Joint finite field | `books/field/finite-field-context.lisp`: constrained `finite-field-*` operations plus `finite-field-rank`, `finite-field-unrank`, and `finite-field-bound`; laws through `finite-field-bound-greater-than-one` | **Reusable constrained theorem layer**. The prefix renames symbols; it does not add a descriptor parameter. It supplies coding laws but no generic `finite-field-elements` or `finite-field-cardinality` function. |
| Finite-field polynomial stack | `books/polynomial/generic/finite-field-instance.lisp` and `finite-field-{division-step,divmod,reduction,euclidean-gcd,monic-euclidean-gcd,xgcd,monic-xgcd,monic-xgcd-reduction,reduced-ring,modular-inverse}.lisp`; `finite-field-poly-*` operations | **Reusable constrained theorem layer** and, after an instance, **reusable executable algorithm**. Every coefficient operation is still the fixed `finite-field-*` symbol family. |
| Field-independent finite coding | `books/algebra/finite-bijection.lisp`: `finite-elements`, `finite-cardinality`, `finite-cardinality-equals-bound` from constrained fixer/rank/unrank/bound | **Abstract logical specification** plus transparent enumerator, instantiated per implementation. It is not itself a field descriptor. |
| Explicit quotient representatives and count | `finite-field-fixed-modulus-coefficients.lisp`: `finite-field-fixed-modulus-coefficient-vector`, `finite-field-fixed-modulus-reconstruct`; `finite-field-coefficient-vector-coding.lisp`: rank/unrank/bound; `finite-field-fixed-modulus-carrier.lisp`: `finite-field-fixed-modulus-elements`, `finite-field-fixed-modulus-cardinality`; `finite-field-extension-cardinality.lisp`: `finite-field-extension-representatives`, `finite-field-extension-representative-count-equals-degree-power` | **Explicit data-parametric executable layer**, but only in the polynomial/modulus argument. Coefficient arithmetic remains the constrained `finite-field-*` instance. The certified field-facing bridge to `fixed-modulus-field-*` remains missing. |
| Prime fields | `books/field/pfield-adapter.lisp`, `pfield-cardinality.lisp`, `pfield-finite-field-context.lisp`; `pfield-elements`, `pfield-cardinality-equals-modulus`; F7/F11 books | **Concrete parameterized prime-field substrate** and **concrete instances**. PFIELD functions take a modulus where defined by the imported library, but the downstream generic instances bind operation symbols; current Schoof functions do not carry that modulus/descriptor throughout. |
| Fixed quotient field | `books/polynomial/generic/fixed-modulus-field.lisp`: `fixed-modulus-field-fix/add/mul/inv` and field laws under a constrained irreducible positive-degree modulus | **Reusable constrained theorem layer**. Irreducibility is properly required for field inversion, not for reduced-ring Schoof computation. |
| F7X2 | `f7x2-representation.lisp`, `f7x2-field.lisp`, `f7x2-cardinality.lisp`; `f7x2-fix/add/mul/inv`, `f7x2-elements`, `f7x2-cardinality-equals-49`; Frobenius witness regressions | **Concrete field instance** and regression. It demonstrates `p^m`, but its literal modulus `x^2+1` over F7 and nullary operations are not an arbitrary extension-field API. |
| Curve equation | `books/curve/short-weierstrass.lisp`: constrained `short-weierstrass-a/b`, `short-weierstrass-rhs`, `short-weierstrass-affine-point-xy-p`; `short-weierstrass-characteristic.lisp`: `short-weierstrass-characteristic-p` | **Reusable constrained theorem layer**. `A` and `B` are nullary constrained symbols. The characteristic contract is nonzero field numerals 2 and 3 (characteristic neither 2 nor 3), not merely an ACL2 integer test. |
| Point representation | `affine-coordinates.lisp`: `affine-coordinates-make/fix`, `short-weierstrass-affine-point-p`; `points.lisp`: `curve-point-infinity`, `curve-point-affine`, `curve-point-fix`, `short-weierstrass-curve-point-p` | **Reusable executable representation** under the fixed field/curve context. Infinity is the tagged list `(:infinity)`; affine points carry fixed coordinate pairs. |
| Addition and group semantics | affine `*-slope`, `*-output-*`, closure books; `curve-point-addition-relation.lisp`; `curve-point-pair-output-point.lisp`; `curve-point-abelian-group.lisp`; `curve-point-natural-scalar.lisp`; quotient cross-add group composition books | **Reusable executable algorithm** plus **reusable constrained theorem layer**. Ordinary, doubling, opposite, and infinity cases exist, but descriptor and run-time `A,B` threading is absent. |
| Division polynomials | `books/schoof/division-polynomial-{base,recurrence-step,table,sequence}.lisp`; `finite-field-division-polynomial-generated-table-correspondence`, `finite-field-division-polynomial-sequence-p-entry-correspondence`; F11 functional instance/correspondence books | **Reusable executable generation** in the constrained finite-field context and a **semantic evaluator correspondence**. Runtime index generation exists; the current trace client remains fixed at `ell=3`. |
| Quotient coordinates | `books/schoof/quotient-coordinate.lisp`: pairs `u+vY`, reduced modulo a supplied polynomial, with `quotient-coordinate-add/mul`; `quotient-coordinate-power.lisp`, `quotient-coordinate-natural-scalar.lisp` | **Reusable executable reduced-ring algorithm** over the fixed GPOLY field. It correctly does not assume the division polynomial irreducible. |
| Trace program | `quotient-coordinate-trace-program.lisp`: constrained operations and `trace-program-candidate-p`; `quotient-coordinate-trace-predicate.lisp`: `quotient-coordinate-trace-candidate-p`; F11 trace regression accepting 2 | **Reusable constrained program schema**, **executable predicate**, and **concrete regression**. There is no runtime-`ell` search, general branch dispatcher, or residue-correctness theorem. |
| Frobenius | `books/field/frobenius-exponent.lisp`; `quotient-coordinate-ambient-soundness.lisp`: evaluation of Frobenius/iterate; `quotient-coordinate-additive-frobenius.lisp`: `quotient-coordinate-frobenius-eleven-of-add`; F7X2 witness books | Mostly **abstract logical specification** and **concrete witnesses**. The generic cardinality-`q` Frobenius automorphism, including `q=p^m`, and its point/group action are missing. The theorem named for eleven is concrete, not general. |
| Quotient semantic bridges | `quotient-coordinate-semantics.lisp`, `quotient-coordinate-semantic-soundness.lisp`, `quotient-coordinate-ambient-semantics.lisp`, `quotient-coordinate-ambient-soundness.lisp`, `quotient-coordinate-field-cross-add-group-soundness.lisp`, `quotient-coordinate-group-semantic-composition.lisp` | **Reusable constrained theorem layers**. They transport accepted cross equations to supplied roots/points and interpret conditional branches. They do not provide roots, torsion coverage, denominator facts, or trace identification. |
| Point enumeration/specification | `books/curve/f11-golden.lisp`: `f11-golden-enumerate-y/x`, `f11-golden-affine-points`, expected list and nonsingularity check | **Concrete regression/reference only**. There is no generic curve-point carrier constructed from a generic finite-field carrier, nor a generic cardinality specification for a run-time descriptor and curve. |
| Primes, CRT, bounds | Community Books prime facts are imported in PFIELD (`DM::PRIMEP`); `docs/audits/acl2-community-books-mathematics.md` records usable integer CRT material | **Scouting only** for Schoof assembly. Auxiliary-prime generation, product stopping rule, centered CRT implementation/correctness, and trace uniqueness are missing. |
| Hasse | `books/hasse/*` registered in `books/top.lisp` and the dependency described in `docs/audits/hasse-source-and-dependency.md` and `ambient-domain-and-degree-representation.md` | **Partial constrained theorem layers** only. The squared Hasse endpoint, Frobenius fixed-point/cardinality bridge, and the final bound consumed by Schoof are missing. |
| Registration/policy | `books/top.lisp` registers production and regression books; `docs/execution-boundaries.md` separates logical equivalence, guards, regressions, and performance | **Certified integration/policy boundary**. Registration means certification coverage, not that the top-level Schoof function exists. |

## Arbitrary finite-field input models

ACL2 is first-order: a value cannot directly contain callable field functions.
That fact makes the following models materially different.

### A. Certified per-field instantiation

A client introduces executable symbols for element recognition/fixing, zero,
one, addition, negation, multiplication, inverse, rank, unrank, and bound, and
functionally instantiates `GFIELD`, `finite-field-*`, and GPOLY theorems.  The
field order is the fixed bound; equality is equality after the client fixer;
canonicalization is the client fixer; and enumeration is the client unrank map.

This is closest to the repository today.  F7, F11, and F7X2 show that guards
and execution can work and that prime powers can be represented.  Validity is
proved when the instance book is certified, never checked at run time.  A new
field requires new instance proofs and a newly named executable Schoof wrapper,
although reusable mathematics can be functionally instantiated rather than
reproved.  Consequently it is genuinely executable *per field* but does not
satisfy the selected meaning of one function taking an arbitrary field value.
Proof cost is moderate per backend; execution can be efficient because calls
are direct.

### B. Explicit runtime descriptor

A value could encode `(p m modulus basis/representation-tag)`.  Every operation
would receive that value, for example `(ff-add fd x y)`, `(ff-fix fd x)`,
`(ff-cardinality fd)`, `(ff-elements fd)`, and `(ff-equal fd x y)`.  For the
polynomial-basis family, elements are exact-width or normalized base-`p`
coefficient vectors, equality is literal equality after `ff-fix`, the order is
`p^m`, and enumeration decodes indices below that order.  A proposed executable
`ff-descriptor-structure-p` would check only data shape, representation tags,
natural/positive size fields, and canonical encodings checkable by the
representation kernel.  A distinct proposed logical `ff-field-valid-p` would
require prime `p`, positive `m`, a monic modulus of degree `m`, and
irreducibility.  It must not trust certificate data merely stored in the
descriptor.  An optional future certified executable `ff-field-valid-check`
could decide that logical predicate, but no such checker exists or is required
for the initial interface.

The representative, coding, carrier, cardinality, PFIELD arithmetic, divmod,
and fixed-modulus field ingredients exist separately.  The uniform descriptor,
arity-threaded curve/polynomial/Schoof APIs, field-law theorem, verified guards,
and scalable validity story do not.  Initial correctness theorems must assume
`ff-field-valid-p`; execution must not claim to reject every composite `p` or
reducible modulus.  Named constructors can discharge the logical hypothesis,
and a validated-descriptor entry point may later use a certified checker.  This model
covers `p^m`, but converting all present constrained definitions directly would
cause broad arity churn and proof risk.  It gives the cleanest public runtime
contract at the highest initial engineering cost.

### C. Staged hybrid (selected)

Build one explicit polynomial-basis descriptor family and its executable
operations as in B.  Prove once, with logical descriptor validity as a parameterized
hypothesis, that those operations satisfy a descriptor-indexed field interface.
Use a small fixed-descriptor wrapper to functionally instantiate the existing
`GFIELD`, `finite-field-*`, GPOLY, curve, and group mathematics.  In parallel,
make the *algorithmic orchestration* explicitly pass the descriptor, curve
coefficients, and auxiliary primes.  Prove the explicit core equivalent to the
fixed-descriptor logical instance.

This represents operations by dispatch on the descriptor's representation tag
(initially only the polynomial-basis family); order by `p^m`; equality and
canonicalization by `ff-fix`; specification enumeration by rank/unrank; and
field validity by `ff-field-valid-p`.  The executable structural predicate and
fixer support guards and total representation semantics without deciding field
validity.  A new descriptor value in the certified family
does not reprove Schoof mathematics.  A new *representation backend* does need
one field-interface/equivalence proof.  Direct descriptor calls may cost more
than specialized wrappers, so performance claims require separate measurements.

The hybrid is the smallest defensible final architecture because it preserves
the substantial constrained theorem investment while meeting the single
runtime-input requirement.  Logical field validity is initially a correctness
hypothesis, not an executable promise.  Whether to add a certified executable
field validator remains unresolved and does not block the core: add it only
when a real caller requires validation of untrusted descriptors.

## Curve input and proposed final contracts

The existing curve context fixes `short-weierstrass-a` and
`short-weierstrass-b`.  The public runtime interface must instead accept fixed
elements `a` and `b`.  Its supported initial model is

```text
y^2 = x^3 + a*x + b,  characteristic != 2 and != 3,
4*a^3 + 27*b^2 != 0.
```

The last expression is interpreted by descriptor operations and compared with
descriptor zero after fixing.  The characteristic restriction should be
derived from descriptor characteristic `p` and connected to the existing
`short-weierstrass-characteristic-p`; it must not be hidden in a guard.

For failures that are executable, a proposed total top-level function should
return a tagged failure rather than silently count a fixed replacement curve.
Initially these are structurally malformed descriptors, unsupported
short-Weierstrass characteristic, malformed coefficients, and singular curves,
provided each check is certified executable.  It must not imply rejection of
every nonprime characteristic or reducible modulus before a field-validity
checker exists.  Inside a successful branch, `(ff-fix fd a)` and
`(ff-fix fd b)` are the canonical coefficients.  Names in the following
sketches are **proposals**, not existing ACL2 definitions:

```lisp
(schoof-count fd a b)
;; -> (:ok n) or (:error reason)

(curve-rational-points-spec fd a b)
;; -> infinity consed with all fixed affine pairs (x,y) from
;;    (ff-elements fd) satisfying the short equation
```

The specification list is finite, duplicate-free, and contains the existing
tagged infinity plus fixed affine points.  It may enumerate the field because
it is a non-executable/reference specification; the implementation theorem
must connect to it without using that enumeration as the algorithm.

```lisp
(defthm schoof-count-correct                       ; PROPOSED
  (implies (and (ff-field-valid-p fd)             ; logical hypothesis
                (ff-supported-short-weierstrass-characteristic-p fd)
                (ff-element-p fd a)
                (ff-element-p fd b)
                (ff-short-weierstrass-nonsingular-p fd a b))
           (equal (schoof-count fd a b)
                  (list :ok
                        (len (curve-rational-points-spec fd a b))))))
```

`ff-field-valid-p` implies structural well-formedness, but the executable need
not decide it.  Therefore the theorem is conditional even if `schoof-count`
returns `(:error ...)` only for its executable checks.  Logical correctness is
this equality plus the no-enumeration implementation invariant.  Guard verification only shows safe execution on described inputs.
Termination requires measures for division-polynomial generation, candidate
search, prime accumulation, and CRT loops.  Neither guards nor termination
imply the equality.  Concrete timings and asymptotic/operation-count bounds are
separate performance evidence and are presently absent.

## General Schoof dependency and status map

| # | Required endpoint | Certified endpoint now | Exact missing obligation / dependency | Kind |
|---:|---|---|---|---|
| 1 | Descriptor representation, then field validity | Constrained field/finite-field contexts; PFIELD and F7X2 clients; explicit coefficient-vector carrier/count | First structural shape/fixing, reduced operations, rank/unrank and `p^m` count; then inverse/field laws under logical validity, characteristic/order, and fixed-descriptor correspondence | Logical + executable |
| 2 | Runtime nonsingular curve | Fixed-symbol short curve, tagged points, characteristic predicate, general addition/group laws | Thread `fd,a,b`; descriptor equivalence; discriminant and failure contract | Logical + executable |
| 3 | Enough primes `ell`, prime and `ell != p` | `DM::PRIMEP` available; characteristic exclusions are generic field facts | Executable generation/selection, pairwise coprimality, stopping-product theorem | Logical + executable |
| 4 | Runtime `psi_ell` | Generated finite-field table and all-index evaluator correspondence | Descriptor instance/equivalence and required degree/shape facts for general odd prime `ell` | Both; largely present in constrained form |
| 5 | Compute modulo `psi_ell` as a ring | Reduced-ring and quotient-coordinate operations take a modulus | Descriptor version and correspondence; no irreducibility premise should be added | Both; algebra largely present |
| 6 | Determine residue mod `ell` | `quotient-coordinate-trace-candidate-p`; F11 residues 0/1 rejected, 2 accepted | Runtime `ell` candidate range/search, complete exceptional dispatcher, existence/uniqueness of accepted residue | Both |
| 7 | Quotient result is Frobenius equation on all relevant torsion | Evaluation/ambient soundness at each supplied root/point | Universal divisibility/root semantics or torsion-coordinate coverage; connect generated `psi_ell`; depends on 1, 2, 4–6 | Logical |
| 8 | All group-law branches | General affine/tagged addition and conditional cross-add/opposite composition | Schoof-specific exhaustive branch theorem including zero denominators, equal/opposite, doubling, infinity, sign and `trace=0` cases | Logical + executable dispatcher |
| 9 | `q`-Frobenius on `F_q` and ambient torsion | Minimal exponent interface; concrete eleven/F7X2 facts; ambient evaluation iteration | Cardinality Frobenius theorem, automorphism and curve/addition/scalar preservation for `q=p^m`; suitable ambient carrier/base embedding | Logical + executable power |
| 10 | Accepted residue equals actual trace modulo `ell` | No such theorem; F11 cardinality gives an independent numerical check | Define trace through `q+1-#E(F_q)` and prove torsion characteristic equation identifies it (torsion module/determinant, isogeny-degree, or equivalent universal theorem); depends on 7–9 and fixed-point/cardinality bridge | Logical |
| 11 | Repeat until product bound | No Schoof loop | Accumulator invariant preserving every certified residue and pairwise-coprime product | Both |
| 12 | Centered CRT | Only audited Community Books ingredients | Data representation, executable CRT, congruence correctness, centered representative | Both |
| 13 | Hasse uniqueness | Hasse prerequisites are partial | Certify `t^2 <= 4q` (or equivalent) and unique centered trace once modulus product exceeds the required bound | Logical |
| 14 | Return actual point cardinality | Concrete F11 list only | Generic rational-point specification/carrier; fixed points/trace identity `#E(F_q)=q+1-t`; compose all preceding steps | Logical + executable final wrapper |

The critical mathematical gap is not polynomial arithmetic.  It is the chain
from quotient equality, through all torsion and Frobenius semantics, to the
cardinality-defined trace, followed by Hasse/CRT uniqueness.

## Reassessment of the specialized F11 route

F11/`ell=3` remains valuable as a focused execution regression: it exercises
the generated `psi_3`, production remainder stack, quotient coordinates,
11-power computation, trace predicate orientation, and ordinary/exceptional
semantic interfaces.  Its failed-to-generalize seams—root/torsion coverage,
ordinate existence, semantic cancellation, Frobenius preservation, and trace
identification—are genuine general obligations.

Constructing `F_11[x]/(psi_3)` as an irreducible root field is nevertheless a
specialized classical witness.  It would supply one universal x root only
after irreducibility, and would still not supply both y coordinates, all
torsion, group branches, or actual-trace identification.  It can remain a
bounded validation exercise after the general interfaces say exactly what a
witness must discharge.  It is not on the critical path to the runtime-field
algorithm.  Continuing it now would delay the descriptor/curve seam and could
incorrectly make irreducibility a prerequisite of quotient-ring computation.

F7 is retained as the cheap prime-field functional-instantiation regression.
F7X2 is retained as the essential prime-power representation/cardinality and
Frobenius regression.  None may own a theorem valid for all fields or curves;
such a theorem belongs in a constrained or descriptor-parametric production
book, with these three as clients.

## Generality and scalability findings

| Finding | Disposition |
|---|---|
| `field-*`, `finite-field-*`, short-curve coefficients, and fixed-modulus-field modulus are first-order fixed symbols; prefixes do not make them runtime-parametric. | **Immediate architectural correction:** first establish a descriptor representation kernel, then a field-law/functional-instantiation bridge, then the runtime curve bridge. |
| The explicit coefficient vectors/carrier/count are not connected to the generic irreducible quotient field. | **Immediate**, within the same descriptor-family boundary; avoid a second arithmetic implementation. |
| Production F11 division-polynomial and quotient clients duplicate fixed names and literals. | **Accurate labelling now; later generalization.** Preserve as instances/regressions while runtime orchestration is built. |
| `quotient-coordinate-frobenius-eleven-of-add` is tied to 11 and does not establish `q=p^m`. | **Later generalization, prerequisite before residue correctness.** F7X2 should test the prime-power statement. |
| The trace program's meaningful client is `ell=3`; there is no general candidate loop or exceptional dispatcher. | **Next after the input seam**, not evidence of a generic Schoof algorithm. |
| F11 exhaustive point enumeration proves the fixture count, not Schoof correctness. | **Accurate labelling only.** Use it as the final independent oracle regression. |
| Fixed quotient-field irreducibility is useful for constructing fields, but `R[x]/(psi_ell)` in Schoof needs only a quotient ring. | **Immediate design constraint:** do not impose irreducibility or prioritize Rabin testing for the trace computation. |
| Current trace theorems quantify over supplied ambient roots/points, hiding absence of a general ambient/torsion carrier. | **Later generalization**, explicitly required in steps 7–10. |
| CRT and Hasse endpoints are documentation/audit plans, not certified Schoof components. | **Later**, after correct general residues; do not scaffold a top-level that suggests otherwise. |

No production theorem discovered in this audit needs to be moved merely because
it has a concrete regression.  The problem is where general claims are absent,
not the existence of concrete clients.

## Route comparison

| Route | Cost and ACL2 risk | Reuse/scalability | Relation to target |
|---|---|---|---|
| Continue F11 root/torsion witness | Moderate implementation, high risk of further instance-only lemmas | Low; validates one curve/prime | Useful later regression, not critical path |
| Build explicit arbitrary-field input layer first | Moderate/high arity and equivalence engineering; bounded mathematics | Highest; resolves meaning of public input and `p^m` early | **Selected as three staged boundaries, beginning with the representation kernel** |
| Generalize trace program to runtime `ell` first | Moderate recursion/branch proof; awkward over fixed field/curve symbols | High after descriptor and curve seams | Begin only after the first three input boundaries |
| Generic Frobenius/torsion correctness first | Very high mathematical and representation risk | Essential and highly reusable | Follow runtime-`ell`, after its data/algorithm statement is stable |
| CRT/top-level scaffolding first | Low/moderate programming, but proof invariants would be conditional on nonexistent residues/Hasse | Reusable integer layer | Defer until residue theorem; otherwise misleading |
| Staged combination | Controls risk if boundaries remain separate | Best overall | Adopt the ordered stages below |

## Selected architecture and forward boundaries

Adopt the **staged hybrid**.  The public meaning is one executable over an
explicit certified polynomial-basis finite-field descriptor family; existing
constrained mathematics remains the logical theorem layer through a
fixed-descriptor functional instance and an execution-equivalence theorem.

### Next implementation boundary: descriptor representation kernel

Build only the polynomial-basis descriptor shape/fixer, element
representation/fixing/equality, addition, negation, multiplication, rank,
unrank, and the `p^m` representative/carrier count, with prime and extension
concrete regressions.  This is deliberately a **reduced-ring/representation
boundary**.  It neither defines field inversion nor claims field laws, a
`GFIELD` instance, or executable detection of prime/irreducible descriptors.

The executable structural predicate should recognize safely processable data;
the separate logical field-validity predicate may already be stated but is not
decided by this kernel.  Reuse the certified PFIELD/divmod/representative stack
and do not introduce a second arithmetic implementation.

### Post-PR #361 implementation finding: runtime coefficient seam

An implementation pass found a narrower prerequisite that the inventory did
not make explicit.  The representative, coding, carrier, and reduction books
accept a runtime polynomial modulus, but coefficient arithmetic and the coding
base remain the nullary constrained `finite-field-*` family.  Conversely,
Community Books PFIELD arithmetic accepts runtime `p`, while the repository
adapter deliberately closes over nullary `pfield-modulus`.  No certified
production interface can therefore thread both runtime `p` and runtime
polynomial modulus through normalization, multiplication, reduction, and
coefficient-vector coding in one call.

Copying the generic polynomial implementation into a descriptor book would
create a parallel reduction stack.  The prerequisite is therefore implemented
as two reusable boundaries.  The first certified book,
`runtime-p-representation.lisp`, provides coefficient arithmetic, unreduced
polynomial normalization/addition/negation/scaling/multiplication, and
fixed-width radix coding.  The second—runtime-`p` monic reduction and fixed-`p`
remainder correspondence—remains open.

The implementation audit found that the Community Books PFIELD primitives are
most safely called after supplying an integer modulus at least two and fixing
coefficient operands.  The total convention is `p` itself exactly when it is
an integer at least two, and `2` otherwise.  Thus non-integers, negative
integers, 0, and 1 execute modulo 2, while composite values at least two are
preserved.  PFIELD `fep-fix` supplies canonical residues and PFIELD `add`,
`neg`, and `mul` receive fixed operands and the effective modulus.  This does
not alter or validate the original descriptor value: later structural
recognition must inspect the original `p`.

Polynomial recursion follows the existing generic templates exactly: atoms
and dotted tails terminate and are discarded, coefficient order is ascending,
normalization fixes coefficients then removes trailing zeroes, and
multiplication uses shifted scaling plus raw addition.  Fixed-`p`
correspondence is staged through recursive equations, with public
non-rewriting endpoints for normalization and multiplication.  Radix unrank
uses `nfix` on width and rank; an out-of-range rank is truncated to the
requested low-order width rather than rejected.

No descriptor definitions were introduced.  Structural descriptor validity,
logical field validity, and any future executable validator remain separate.
An implementation attempt selected the smallest execution interface: normalized
length/degree and leading coefficient, a monic predicate that is exactly
equality of the normalized leading coefficient with canonical coefficient one,
one inverse-free cancellation step, and one fuel-bounded divmod recursion whose
public fuel is the normalized dividend length.  The nonmonic (including zero)
fallback is `(nil . normalized-dividend)`; constant one reduces to zero.  The
same core supplies both projections, and reduced multiplication reduces its
unreduced product exactly once.  This total execution prefix certifies guards,
canonical remainders, malformed/dotted/trailing-zero behavior, and prime,
composite, and malformed-`p` executions.

The attempt did **not** close the representation-level Euclidean proof.  The
exact residual is the reusable runtime-`p` commutative-ring polynomial algebra
needed to prove one-step reconstruction and strict normalized-length decrease;
from those, core reconstruction, strict remainder bound, idempotence,
reduced-operation invariance, and fixed-PFIELD divmod/remainder correspondence
must still be staged.  The existing inverse-based division stack was rejected:
copying it would introduce an irrelevant inverse and would be invalid for
composite `p`.  Accordingly, the maintained boundary remains open and the
descriptor kernel remains blocked rather than being started prematurely.

### Following dependency order

1. **Descriptor field-law bridge:** add inverse; prove field laws under logical
   descriptor validity, characteristic/order facts, and fixed-descriptor
   correspondence/functional instantiation into `GFIELD` and `finite-field-*`.
2. **Runtime short-curve bridge:** thread descriptor and runtime `a,b` through
   discriminant/nonsingularity and point fixing, and prove correspondence with
   the existing fixed-symbol curve context.
3. **Runtime-`ell` quotient trace boundary:** descriptor/curve-threaded
   division-polynomial generation, reduced quotient computation, bounded
   candidate search, and an exhaustive ordinary/exceptional branch dispatcher;
   prove equivalence to the constrained operations, not trace correctness yet.
4. **Generic cardinality-Frobenius/torsion residue boundary:** `q=p^m`
   Frobenius, curve/group preservation, all relevant `ell`-torsion coverage,
   and the theorem that the accepted quotient candidate is the
   cardinality-defined trace modulo `ell`.
5. **Prime accumulation and reconstruction boundary:** auxiliary-prime loop,
   residue accumulator invariant, centered CRT, then consume the independently
   certified Hasse bound to obtain the unique trace and compose the proposed
   point-cardinality theorem.

Each item should be split further if its first theorem statement reveals an
independent missing mathematical theory; in particular the torsion residue
boundary may require a separately reviewed module/determinant or degree route.

## Explicit nonclaims and deferred work

This audit does not claim an existing descriptor, generic rational-point list,
general `q`-Frobenius theorem, general trace residue, torsion completeness,
auxiliary-prime loop, CRT implementation, Hasse bound, top-level Schoof
function, complexity bound, or final cardinality theorem.  It does not claim
that guard verification proves semantics or that F11 enumeration proves the
algorithm.  It does not select executable descriptor validation, Rabin
irreducibility, a general algebraic closure, a torsion-module basis, Weil
pairing, or isogeny-degree machinery.

The remaining architectural choice is the trace-identification proof route:
torsion-module/determinant versus a degree/isogeny theorem versus an equally
strong universal torsion theorem.  Selection should wait until the descriptor
and runtime-`ell` boundaries provide the exact Frobenius equation and branch
statement.  The decision criterion is the smallest route that proves the
cardinality-defined trace for all supported descriptors and primes without
enumerating curve points, not whichever route closes the F11 fixture first.
