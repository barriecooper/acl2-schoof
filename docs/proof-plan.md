# Proof plan

This document owns forward mathematical dependency order. Current theorem-level
status is in the [obligation ledger](obligations.md); stable design is in
[architecture](architecture.md).

## Destination and shared seam

The long-term destinations are a Manin-style proof of Hasse's theorem and an
executable, certified Schoof point-counting algorithm. They share field,
polynomial, curve, rational-function, and Frobenius foundations. Beyond that
shared seam they are parallel: Hasse is not an implementation prerequisite for
Schoof.

## Completed foundations

The current certified base includes the generic field kernel, canonical dense
polynomial arithmetic, Euclidean division, GCD and XGCD, modular inversion,
irreducible fixed-modulus quotient fields, short-Weierstrass representations,
and the executable and independent semantic layers for full tagged-point
addition. Output closure, infinity identity, inverse-to-infinity, and full
commutativity are complete. Concrete F7, F7X2, and F11 books supply focused
instantiation and execution regressions rather than additional generic scope.

## Completed semantic H reconstruction

The field-only theorem `xcert-h-scalar-reconstruction` derives the exact
factor-ordered equality `(p-r)(p+q)=xa-xc` from the audited seven scalar
equations and only `xc-xb != field-zero`; E2 is unused.  Its semantic
instantiation `xcert-h-curve-zero` maps `p`, `q`, and `r` to the ordered slopes
`(A,B)`, `(AB,C)`, and `(B,C)` and certifies the existing specialized H
expression as `field-zero`.  The field-only exact S reconstruction is complete as
`xcert-s-scalar-reconstruction`, and `xcert-s-curve-zero` specializes it to the
four ordered nested distinct-x pairs.  Its two ordered nonzero premises serve
the H and final-S cancellations separately.
The same seven-hypothesis configuration now also certifies equality of the two
final x-coordinates by simplifying the maintained composition with both H-zero
and S-zero.  Field-only final-y reconstruction is complete: the output-x/H
coordinate bridge and exact six-residual reduction compose through one bounded
opposite-product cancellation to give fixed equality of the final ordinates.
Its semantic instantiation is now complete as
`xcert-final-y-coordinates-equal`, under the same three curve memberships and
four ordered nested distinct-x classifications as final x equality.  The
theorem `xcert-untagged-outputs-equal` packages those coordinate results and
certifies equality of the assembled untagged affine outputs under exactly the
same semantic interface.  `xcert-tagged-outputs-equal` lifts that literal
payload equality through the existing tagged distinct-x constructor, without
replaying coordinate or scalar algebra.  The ordinary affine-dispatcher case
is complete as `xcert-affine-dispatcher-outputs-equal` under the same exact
seven hypotheses.  It instantiates the existing `:distinct-x` branch equation
once for each outer dispatcher and uses `xcert-tagged-outputs-equal` for all
semantic equality, without replaying coordinate or field algebra.  Other
classifier outcomes remain later work.  The theorem
`xcert-full-point-dispatcher-associative-when-all-distinct-x` now lifts this
result to the literal nested `curve-point-pair-output-point` expressions with
tagged affine `a`, `b`, and `c` leaves, under those same exact seven
hypotheses.  Existing affine/affine and distinct-x branch interfaces, plus a
proof-local canonical inner reduction, remove the dispatcher and fixer layers;
all semantic equality is the affine-dispatcher theorem, with no coordinate or
field algebra replayed.  The next phase is an audit and decomposition of the
remaining associativity configurations, not a presumption that one further
branch theorem will cover them.  Exceptional same-x, opposite-y and doubling
interactions, infinity inputs and intermediate infinity, arbitrary classifier
combinations, unrestricted associativity, and group structure remain later
work; the already certified identity and inverse laws are structural inputs to
that work.

## Phase 1: complete associativity

Before characteristic-dependent exceptional certificates resume, use the
certified curve boundary `short-weierstrass-characteristic-p`.  It states
nonzero two and nonzero three in the same `GFIELD` operations used by the curve
equation, while leaving generic field and polynomial clients—including F2—
unchanged.  Existing representation, secant, classifier, dispatcher, X-CERT,
inverse/tangent, and DD-O theorems remain at their certified generic scope;
only new arguments that exclude a small-characteristic degeneration should
consume the named predicate.  Inverse/secant and DD-T remain separate later
PRs and are not resumed by the characteristic-boundary work.

The structural audit is recorded in the
[associativity case ledger](obligations.md#associativity-case-audit).  It
reduces the valid affine inputs to `D`, `O`, and `T`, rather than a formal
four-by-four classifier product.  Work should now proceed in these reviewable
PR boundaries:

1. **Structural interface (complete).** The certified interface provides
   unconditional classifier symmetry, fixed opposite-y coordinates and fixed
   same-point equality, closure-derived outer `:same-x-other` exclusions for
   secant and doubling outputs, and one combined associativity theorem for a
   valid triple with any original input at infinity.  These proofs use only
   classification, fixing, closure, representation, and infinity equations.
2. **Opposite/opposite and repeated triples (complete).** The certified `O/O`
   endpoint theorem chains the two fixed negation equations (including
   self-inverse ordinates), and the full-point theorem reduces both inner calls
   to infinity.  The certified `T/T` theorem fixes all three inputs equal,
   identifies the inner doubles through fixing congruence, proves their validity
   by doubling closure, and closes the reversed outer calls by full-point
   commutativity.  These are structural proofs with no new coordinate algebra.
3. **Exceptional secant structure (partially implemented).** Work in
   four stopping-bounded subdivisions: (a) inverse translation with a secant
   inner output (**semantic certificate complete**), including the derived
   outer secant/doubling split and exclusion of outer `O`; (b) inverse
   translation with a tangent inner output
   (**semantic certificate complete**), deriving rather than assuming the outer
   outcome; (c) `D/D` outer `O` by collinearity propagation
   (**semantic certificate complete**); and (d) `D/D`
   outer `T` by a separate independent-witness reconstruction.  The former
   proposed bridge `p*(yc+yc)=3*xc^2+a` is false: a secant output reflects the
   third chord intersection, and its witness is independent of the tangent
   witness at that output.  The corrected audit keeps both inner secants and
   the actual tangent triple and identifies `s=(p+t)-r` as the candidate
   opposite-tree witness.  Certify its three outer-secant equations first;
   separately establish the coincident-x ordinate and opposite-y exclusion,
   then its three doubling equations, before semantic packaging.  Use the
   existing division-free secant and doubling relations as the scalar interface
   and package results through `curve-point-addition-relation-p` only
   afterwards.  The exact oriented
   equations and residual conclusions are recorded in the obligation ledger.
   Stop an implementation PR after one subdivision certifies; stop earlier if
   the opposite-tree outcome cannot be derived without an additional nonzero
   assumption or an independent outer classifier premise.
4. **Mixed secant--tangent certificate.** Certify one coherent division-free
   family for `D/T`; obtain `T/D` by the already certified commutative mirror.
   Reuse the individual secant and tangent relations.  A branch-parametric
   residual framework is preferred only if its hypotheses remain explicit;
   otherwise use two small, oriented certificates.  Stop when mixed semantic
   output equality and all genuinely derived exceptional outcomes are covered.
5. **Finite semantic assembly.** Combine infinity, impossible, `O`, `T`, and
   `D` families into semantic associativity for valid curve points, relying on
   `curve-point-addition-case-coverage`.  This PR must add no new coordinate
   algebra; a need for such algebra means phase 3 or 4 is incomplete.
6. **Executable lift.** Derive unrestricted
   `curve-point-pair-output-point` associativity from semantic soundness,
   fixed-output determinacy, closure, and canonical representation.  Keep this
   representation proof separate from the semantic case proof.
7. **Group packaging.** Only after unrestricted associativity certifies,
   develop cancellation consequences, scalar multiplication, and an abstract
   abelian-group interface.

The stopping conditions are intentional: they prevent an “assembly” PR from
becoming a hidden coordinate proof and prevent executable dispatcher expansion
from replacing the independent semantic boundary.  It remains open whether
one chord-and-tangent certificate covers all exceptional degenerations; phase
3 must settle that interface before phase 4 is sized.

## Phase 2: common curve and function-field infrastructure

Once the curve laws are adequate for downstream use, develop only the common
infrastructure demanded by the two tracks: scalar multiplication when its
specification is clear, polynomial derivatives and separability, rational
functions and their equality/cancellation theory, and the required Frobenius
facts. Exact sequencing within this phase depends on the associativity audit
and on the chosen primary Hasse reference; no completion is implied here.

## Phase 3A: Manin-style Hasse track

Select and record the exact primary exposition, then formalize the needed
function-field or morphism degree theory, Frobenius/dual relationships, and the
degree inequality from which Hasse's bound follows. Reuse the common polynomial
and curve layers rather than rebuilding them inside the proof.

## Phase 3B: executable Schoof track

Develop division polynomials, quotient-coordinate arithmetic, Frobenius action,
trace-congruence tests, and bounded incremental CRT reconstruction. Each
logical/executable boundary needs an independent specification, a certified
correspondence theorem, verified guards, and focused execution evidence.
Practical benchmarks are performance evidence, not proof of point-count
correctness.

## Completion criteria

A phase is complete only when its books certify under the repository trust
policy and its open obligations are updated in the ledger. Concrete examples
may validate execution and functional instantiation, but cannot substitute for
generic correctness. Chronological PR narratives belong in Git history, not in
this plan.
