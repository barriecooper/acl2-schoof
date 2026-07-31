# Proof obligation ledger

This is the authoritative detailed ledger of certified, open, and deliberately
deferred work. Architecture is described in [architecture.md](architecture.md),
future order in [proof-plan.md](proof-plan.md), and logical/executable contracts
in [execution-boundaries.md](execution-boundaries.md).

Status labels mean:

- **Certified** — admitted by a registered book and covered by repository
  certification.
- **Open** — required or plausibly required by the current route, but not
  certified.
- **Deferred** — intentionally outside the present boundary.

A concrete regression is listed as execution or instantiation evidence, never
as a generic proof. Guard verification is likewise distinct from semantic
correctness.

## Generic field kernel and prime-field clients

### Certified

- Total field-element fixing and the constrained commutative-field laws,
  including additive and multiplicative closure, identities, inverses,
  distributivity, cancellation, and congruence modulo fixing.
- Natural powers and their generated fast/spec correspondence.
- Equal-squares alternatives, characteristic-two and characteristic-three
  exclusions used by the short-Weierstrass layer, and a minimal positive
  Frobenius exponent satisfying the fixed-representative power equation.
- PFIELD adaptation and named executable F2, F7, and F11 instances.

### Qualifications and non-claims

- The Frobenius exponent is not certified as a cardinality, least exponent, or
  prime power. No generic field enumeration is supplied.
- F7/F11 computations validate concrete execution and functional
  instantiation; they do not enlarge the generic theorem statements.

### Open or deferred

- Generic finite-field cardinality/enumeration metadata and a connection from
  that metadata to the Frobenius exponent are open.
- Characteristics two and three are deferred for the initial curve scope.

### Relevant public interface

`field-fix`, the `field-*` operations, `field-pow`, the PFIELD adapter, and the
named F7/F11 operations.

## Canonical dense polynomials

### Certified

- Constant-first dense representation, coefficient fixing, normalization, and
  unique canonical zero `nil`.
- Canonical addition, negation, subtraction, multiplication, evaluation,
  natural powers, degree, and leading coefficient, with the commutative-ring
  and evaluation laws.
- One-step and recursive quotient/remainder with reconstruction and strict
  remainder bounds for normalized nonzero divisors.
- Remainder congruence, divisibility, reduced representatives, and reduced ring
  operations.
- Euclidean GCD, monic GCD, raw XGCD, monic XGCD, Bézout identities, the
  XGCD-derived modular-inverse candidate, logical irreducibility, and the
  irreducibility-to-monic-GCD-one and nonzero modular-inverse results.
- Guard-verified concrete F7 division, GCD, XGCD, and modular inverse with exact
  execution regressions.

### Qualifications and non-claims

- Generic theorems quantify over the constrained field kernel. Concrete F7
  books are instances, not replacements for those proofs.
- Public polynomial operations return canonical representatives. Raw helper
  equalities and evaluation equality must not be presented as canonical
  polynomial equality without the corresponding normalization theorem.

### Open or deferred

- Derivative and separability theory required downstream is open.
- Rational-function equality, cancellation, and degree theory is open.
- Further HS/PFIELD bridges are deferred until a downstream theorem requires
  them; new generic algebra belongs in GPOLY.

### Relevant public interface

`normalize`, `poly-add`, `poly-neg`, `poly-sub`, `poly-mul`, `eval`,
`poly-divmod`, `poly-remainder`, `poly-euclidean-gcd`,
`poly-monic-extended-euclidean-gcd`, `poly-modular-inverse`, and
`poly-irreducible-p`.

## Fixed-modulus quotient fields and F7X2

### Certified

- The generic `FIXED-MODULUS-FIELD-*` interface over a constrained canonical,
  irreducible, positive-degree modulus: canonical remainder fixing, total
  arithmetic, zero/one distinction, additive and multiplicative laws,
  distributivity, and two-sided nonzero inverse correctness.
- Irreducibility of `x^2+1` over F7 and concrete compatibility of F7X2 with the
  generic fixed-modulus interface.
- F7X2 canonical representation and total guard-verified addition, negation,
  subtraction, multiplication, and inverse execution, with focused exact
  regressions.

### Qualifications and non-claims

- The generic constructor is the reusable quotient-field result. F7X2 is a
  concrete proving instance.
- The regression-prefixed fixed-modulus theorem establishes semantic
  compatibility of the present F7X2 operations; execution assertions alone do
  not establish field correctness.

### Open or deferred

- Ordinary public F7X2 inverse theorem promotion and formal packaging as a
  `GFIELD` client remain open.
- F7X2 cardinality, enumeration, and Frobenius metadata remain open.
- A general executable constructor for arbitrary finite fields is deferred.

## Short-Weierstrass and point representations

### Certified

- Fixed-at-use coefficients, total right-hand side and coordinate equation,
  and the constrained nonzero discriminant expression in the supported
  characteristic scope.
- Canonical affine-coordinate constructor, accessors, fixer, structural
  recognizer, and separate curve-membership predicate.
- Tagged point representation with canonical infinity and affine tags,
  point fixer, structural recognition, and separate full curve membership.
- Total point negation, structural and curve closure, and involution modulo
  fixing (raw involution for canonical representations).

### Qualifications and non-claims

- Malformed affine coordinates fix to the zero pair; malformed tagged points
  fix to infinity. Neither convention asserts that an arbitrary affine fixed
  value lies on the curve.
- F11 golden-curve books are concrete execution fixtures.

### Open or deferred

- Characteristics two and three, general discriminant/smoothness development,
  and alternative curve models are deferred.

## Field-only X-CERT algebra

### Certified

- Transparent total definitions for the four output-coordinate residuals and
  `xcert-dx`, `xcert-telescope`, `xcert-remainder`, `xcert-h`, `xcert-s`, and
  `xcert-c`.
- The unconditional output-telescope and remainder component identities for
  arbitrary ACL2 objects under field fixing.
- Their opaque composition as
  `D_x = (T - (H + H)) + C*S`, with the specified left association.

### Curve-semantic bridge certified

- For ordered inputs `A,B,C`, `xa,xb,xc` are their x-coordinates; `xab,xbc`
  are the x-coordinates of `AB=output(A,B)` and `BC=output(B,C)`; and `xl,xr`
  are those of `output(AB,C)` and `output(A,BC)`.
- `p,q,r,tt` are respectively the ordered slopes `(A,B)`, `(AB,C)`, `(B,C)`,
  and `(A,BC)`.  No slope operands are swapped.
- The four specialized coordinate-sum-minus-square residuals are zero
  unconditionally, directly from `affine-distinct-x-output-x-rearrangement`.
- `D_x`, `H=(p-r)(p+q)-(xa-xc)`, `S=(p+q)-(r+tt)`, and
  `C=((p+q)-r)+tt` have exact curve specializations, and the curve composition
  consumes `xcert-composition` opaquely.

### Open

- The H/S audit found no directly available zero result.  The smallest missing
  bridge, formerly proof-local, is now certified publicly as
  `affine-distinct-x-input-secant-identity`:
  `slope*(y(second)+y(first)) = x(second)^2 +
  x(second)*x(first) + x(first)^2 + a`.  Its only hypotheses are curve
  membership of the two ordered inputs and classification of that same ordered
  pair as `:distinct-x`; the classification supplies the nonzero denominator
  used by the theorem's cancellation step.  Regressions instantiate it without
  operand reversal at `(A,B)`, `(B,C)`, and `(AB,C)` for `p`, `r`, and `q`.
- The field-only scalar bridge `xcert-h-scalar-reconstruction` now certifies
  `(p-r)(p+q)=xa-xc` from exactly E1, E3, E4, E5, E6, E7, and E8 plus the
  single nonzero premise `xc-xb != field-zero`.  E2 remains unused, and no
  nonzero premise for `(A,B)` or `(AB,C)` is present.  Its certified residual
  identity is `(xc-xb)K = E1-E3-q*E4-(p+q)*E5+p*E6+
  (xa+xb-xc-xab)*E7+(q-p)*E8`, for
  `K=(p-r)(p+q)-(xa-xc)`.  A local explicit 52-term field-sum representation
  permutes the expansion into 20 adjacent inverse pairs and the 12 expanded
  target monomials; all list and normalization machinery remains proof-local.
  The seven equations reduce the residual side to zero, one explicit instance
  of `field-mul-left-cancel-forward` cancels `xc-xb`, and the kernel's
  subtraction/equality bridge gives the displayed reconstruction.  The stated
  premise minimality is relative to this audited proof, not a formal logical
  minimality theorem.
- The semantic bridge `xcert-h-curve-zero` instantiates that scalar theorem
  with the ordered slopes `(A,B)`, `(AB,C)`, and `(B,C)`.  Its hypotheses are
  curve membership of `A`, `B`, and `C`, plus `:distinct-x` classification of
  `(A,B)`, `(B,C)`, and `(AB,C)`.  Closure supplies curve membership of `AB`;
  the input-secant identity supplies E1 and E3, slope reconstruction supplies
  E4--E6, and the unconditional output-x and output-y rearrangements supply E7
  and E8.  The `(B,C)` classification also supplies the sole nonzero premise
  `xc-xb != field-zero`.  E2 is not used.  The result is the existing
  specialized `xcert-h` expression equal to `field-zero`.
- `H` has not been used in composition, and composition simplification, `S`,
  coordinate equality, exceptional cases, and associativity were not attempted.
- The field-only theorem `xcert-s-scalar-reconstruction` now certifies the
  exact `S=(p+q)-(r+tt)=0` reconstruction.  Direct S algebra consumes the
  ordered `q` and `r` slope equations, AB/BC output-x equations, the BC
  output-y equation, and the public H equality; the H theorem encapsulates the
  ordered `(A,B)` and `(AB,C)` input-secant equations, the `p` slope and AB
  output-y equations, and cancellation of `xc-xb`.  The `tt` slope and both
  AB/BC output-coordinate pairs connect the staged product to this residual.
  The scalar theorem therefore has two distinct nonzero premises: `xc-xb` for
  H reconstruction and `xbc-xa` for the final S cancellation.  The `(B,C)` and
  `(A,BC)` input-secant equations are not direct scalar hypotheses.
- The semantic bridge `xcert-s-curve-zero` instantiates the scalar theorem with
  the exact ordered slopes `(A,B)`, `(AB,C)`, `(B,C)`, and `(A,BC)`.  Its public
  hypotheses are curve membership of `A`, `B`, and `C`, and `:distinct-x`
  classifications of those four pairs.  Distinct-x closure derives membership
  of both `AB` and `BC`; the secant, slope-reconstruction, output-coordinate,
  and classifier theorems discharge all ten equations and both ordered
  nonzero differences.  The result retains the exact grouping
  `(p+q)-(r+tt)=0`.  An F11 regression uses `A=C=(2,4)`, `B=(3,5)`, and
  `AB=BC=(7,2)`, with ordered slopes `1,4,1,4`.
- The four output-x residuals were already zero before this input-secant step.
  The X-CERT composition is now simplified with both public H-zero and S-zero
  results to certify `xcert-final-x-coordinates-equal`.  Its hypotheses are the
  three input curve memberships and the four ordered `:distinct-x`
  classifications used by `xcert-s-curve-zero`; it adds no nonzero premise.
- The field-only theorem `xcert-output-x-h-coordinate-bridge` now derives
  `xl-xb=(q-r)(p+q)` from exactly the maintained final-left output-x equation
  `xl+xab+xc=q*q`, the AB output-x equation `xab+xa+xb=p*p`, and the H equality
  `(p-r)(p+q)=xa-xc`.  Its proof adds the short common block `xb+xab+xc`,
  transports the three equations one at a time, and uses only bounded additive
  cancellation and the difference-of-squares step.  It has no nonzero premise
  and performs no multiplicative cancellation.
- The field-only theorem `xcert-y-difference-six-residual-reduction` certifies
  `yl-yr=(p-r)(xl-xb)+(r-q)(xa-xc)` from exactly six equations: S-zero
  `(p+q)-(r+tt)=0`; the ordered slope equations
  `p(xb-xa)=yb-ya`, `r(xc-xb)=yc-yb`, and
  `q(xc-xab)=yc-yab`; and the final output-y equations
  `yl+yab=q(xab-xl)` and `yr+ya=tt(xa-xl)`.  The proof certifies the
  documented six-residual decomposition by separating its ordinate telescope
  from its product balance, then cancels each zero residual.  The AB output-y
  equation is absent.  All support algebra is proof-local; there are no curve,
  classifier, nonzero, or multiplicative-cancellation hypotheses.
- The public theorem `xcert-field-only-final-y-equal` now composes the two
  preceding public theorems.  Its exact interface is the union of their needed
  hypotheses: final-left and AB output-x; maintained H equality; S-zero; the
  ordered A-to-B, B-to-C, and AB-to-C slope equations; and final-left and
  final-right output-y.  It concludes `field-fix(yl)=field-fix(yr)`.  The
  coordinate bridge substitutes `xl-xb=(q-r)(p+q)`, while maintained H directly
  substitutes `xa-xc=(p-r)(p+q)`, leaving
  `(p-r)((q-r)(p+q))+(r-q)((p-r)(p+q))`.  A bounded proof-local three-factor
  lemma rewrites `r-q` as the negation of `q-r`, associates and commutes only
  those products, and applies additive inverse; no multiplicative cancellation
  is used.  The AB output-y equation remains absent.  There is no geometric,
  classifier, nonzero, inverse, division, additional-certificate, or
  multiplicative-cancellation premise, and the six residual equations are not
  re-expanded by this composition.
- The semantic theorem `xcert-final-y-coordinates-equal` now instantiates
  `xcert-field-only-final-y-equal` once under exactly the three input curve
  memberships and four ordered `:distinct-x` classifications already used for
  final x equality.  It concludes fixed equality of the y coordinates of
  `xcert-left` and `xcert-right`.  The semantic map is `p/q/r/tt` to the
  `(A,B)`, `(AB,C)`, `(B,C)`, and `(A,BC)` slopes; `xa/xb/xc` and `ya/yb/yc`
  to input coordinates; `xab/yab` to the coordinates of `AB`; and `xl/yl/yr`
  to left x, left y, and right y.  The nine premises come respectively from
  the output-x rearrangements for `(AB,C)` and `(A,B)`, semantic H-zero plus
  its specialization, semantic S-zero, slope reconstruction for `(A,B)`,
  `(B,C)`, and `(AB,C)`, and output-y rearrangement for `(AB,C)` and `(A,BC)`.
  Two proof-local bridges reverse the H residual's zero equality and transport
  the last output-y equation across the already-certified final-x equality.
  No scalar equation becomes a public premise, and the AB output-y equation
  remains absent.
- Semantic final-y equality is complete.  The public theorem
  `xcert-untagged-outputs-equal` now concludes literal equality of `xcert-left`
  and `xcert-right` from exactly the three input curve memberships and four
  ordered `:distinct-x` classifications used by both final-coordinate results.
  It packages the raw final-x equality and fixed final-y equality rather than
  replaying their scalar algebra.  Since affine y accessors are field elements,
  `field-fix-when-field-element-p` removes both final-y fixers; a proof-local
  generic extensionality lemma then reconstructs the two canonical maintained
  outputs from their equal accessors.  This is the semantic payload equality
  used by the next representation boundary.
- Tagged ordinary distinct-x output equality is complete.  The public theorem
  `xcert-tagged-outputs-equal` retains exactly the same three input
  curve-membership and four ordered `:distinct-x` hypotheses and concludes
  equality of the two `affine-distinct-x-output-point` results.  Its semantic
  content is a direct use of `xcert-untagged-outputs-equal`; controlled unfolding
  of the existing tagged constructor and maintained tree abbreviations is the
  entire representation lift, so no constructor bridge and no coordinate or
  scalar algebra is added.
- Ordinary affine-dispatcher equality is complete for the maintained
  four-`:distinct-x` X-CERT configuration.  The public theorem
  `xcert-affine-dispatcher-outputs-equal` assumes exactly affine curve
  membership of `a`, `b`, and `c`, plus `:distinct-x` classification of
  `(a,b)`, `(b,c)`, `(xcert-ab a b,c)`, and `(a,xcert-bc b c)`.  It reduces
  the two outer `affine-pair-output-point` calls through exactly two instances
  of the existing `:distinct-x` branch equation, then uses
  `xcert-tagged-outputs-equal` for all semantic equality.  It replays no
  coordinate, scalar, or field algebra.
- Full-point dispatcher associativity is complete for affine leaves in that
  same ordinary four-`:distinct-x` configuration.  The public theorem
  `xcert-full-point-dispatcher-associative-when-all-distinct-x` has exactly the
  three affine curve-membership hypotheses for `a`, `b`, and `c` and the four
  ordered classifications `(a,b)`, `(b,c)`, `(xcert-ab a b,c)`, and
  `(a,xcert-bc b c)`.  It proves literal equality of
  `((affine a + affine b) + affine c)` and
  `(affine a + (affine b + affine c))`, where every `+` is
  `curve-point-pair-output-point` and every leaf is constructed by
  `curve-point-affine-coordinates`.  A proof-local inner distinct-x reduction
  removes constructor and coordinate fixers; the existing full-point
  affine/affine equation and affine distinct-x branch equation reduce the two
  outer calls.  All semantic equality then comes directly from
  `xcert-affine-dispatcher-outputs-equal`; no coordinate or field algebra is
  replayed.
- Scalar certificate semantics, final coordinate equality, untagged output
  equality, tagged ordinary-output equality, and this affine-dispatcher
  ordinary-case equality and its full-point lift are separate completed
  boundaries.  The next phase is an audit and decomposition of the remaining
  associativity configurations.  Exceptional same-x, opposite-y and doubling
  interactions, infinity inputs or intermediate infinity, arbitrary classifier
  combinations, unrestricted associativity, group structure, cancellation, and
  any later use in Schoof machinery remain open.  The certified identity and
  inverse laws are available structural inputs, not open obligations.

## Affine addition branches

### Certified

- The exhaustive, pairwise-disjoint `affine-pair-classify` interface and the
  proof that `:same-x-other` is unreachable for two on-curve inputs.
- Total executable slopes and coordinate outputs for distinct-x secants and
  same-point non-opposite doubling, including reconstruction identities and
  output closure under their branch hypotheses.
- Tagged branch outputs for secant, doubling, and opposite-y/infinity, plus the
  total `affine-pair-output-point` dispatcher.
- Independent division-free semantic relations for secant and doubling, with
  fixing stability, soundness witnesses, and fixed slope/output uniqueness.
- Independent exceptional semantic relations for inverse-to-infinity and the
  two ordered infinity identity cases.

### Qualifications and non-claims

- Classifiers operate on fixed structure and remain meaningful off curve.
- An executable branch value outside its classifier/domain hypothesis is only
  total programming behavior.
- Semantic branch relations do not call classifiers, executable slopes,
  outputs, or dispatchers.

### Open or deferred

- No affine-only branch result should be cited as full tagged-point
  associativity or group structure.

## Full tagged-point addition

### Certified semantic specification

`curve-point-addition-relation-p` is the independent five-case relation. It
requires curve-point inputs and output and combines ordered infinity identity,
affine inverse-to-infinity, distinct-x secant, and non-opposite doubling cases.
It does not call the branch classifier or either dispatcher.

`curve-point-addition-case-coverage` establishes semantic case coverage.
`curve-point-pair-output-point-satisfies-addition-relation` proves dispatcher
soundness. `curve-point-addition-relation-output-determinate` proves equality
of fixed outputs for two relation witnesses. Together these results connect
independent semantics to the total executable dispatcher.

### Certified algebraic laws

- **Stage 1 associativity structural interface:**
  `affine-pair-classify-symmetric` is unconditional;
  `affine-pair-classify-opposite-y-implies-fixed-coordinates` exposes fixed x
  equality and the maintained second-y/negated-first-y orientation; and
  `affine-pair-classify-same-point-non-opposite-implies-fixed-equal` exposes
  equality of the fixed affine objects.  The closure-derived theorems
  `affine-pair-classify-distinct-x-output-not-same-x-other` and
  `affine-pair-classify-doubling-output-not-same-x-other` exclude the invalid
  outer class in one orientation, with classifier symmetry covering reversal.
  `curve-point-pair-output-point-associative-when-infinity-input` proves the
  literal nested dispatcher equality for three valid full points whenever any
  original input is infinity.  All are structural proofs: no secant, tangent,
  X-CERT, cancellation, division, or coordinate-composition algebra is used.
- **Closure:** the dispatcher returns a curve point for curve-point inputs.
- **Identity:** infinity is a left and right identity. The semantic relation
  contains both ordered identity clauses, and the dispatcher has unconditional
  fixed-input equations.
- **Inverse:** a curve point combined with `curve-point-neg` satisfies the
  independent relation with infinity; the dispatcher returns canonical
  infinity.
- **Commutativity:**
  `curve-point-addition-relation-p-commutative` reverses semantic operands
  without changing the output, and
  `curve-point-pair-output-point-commutative` proves raw equality of the two
  canonical executable outputs.

Focused F11 books exercise finite branch cases, infinity, inverse pairs,
malformed-value fixing, identity, and operand reversal. They are concrete
regressions, not the generic proofs above.

### Equality qualification

The relation and determinacy use fixed representatives: semantic witnesses are
unique after `curve-point-fix`. The executable dispatcher always returns a
canonical tagged representation, permitting the final commutativity theorem to
state raw ACL2 equality. These two equality levels must remain explicit.

### Open

- Stage 2 associativity is certified for both-inner-opposite (`O/O`) and
  repeated-triple (`T/T`) structural cases.  Single-`O`, mixed secant/tangent,
  exceptional secant, finite assembly, and unrestricted associativity remain
  open.
- Cancellation laws.
- Abstract group or abelian-group packaging.
- Scalar multiplication and its laws.

Associativity is not ready for a direct proof.  The completed structural audit
below and its [proof order](proof-plan.md#phase-1-complete-associativity) govern
the prerequisite structural and algebraic lemma groups before finite case
assembly begins.

### Associativity case audit

The following is the authoritative structural ledger for the remaining case
proof.  Write `D`, `O`, and `T` for the affine classifier results
`:distinct-x`, `:opposite-y`, and `:same-point-non-opposite`, respectively,
and write `AB` and `BC` for the two inner outputs.  This is not a Cartesian
product of four classifier values.  For on-curve affine operands,
`affine-pair-classify-not-same-x-other-for-curve-points` removes
`:same-x-other`; output closure then removes it again for any outer affine pair
whose inner operand came from a `D` or `T` branch.  The proof of that theorem
uses the generic curve equation and `field-equal-squares-implies-equal-or-neg`,
not an F11 enumeration.

The outcome of an outer call is meaningful only when its inner result is
affine.  An inner `O` result is canonical infinity by
`affine-pair-output-point-when-opposite-y` and
`affine-opposite-y-output-point-is-infinity`, so the corresponding outer call
uses `curve-point-pair-output-point-of-infinity-left` or
`curve-point-pair-output-point-of-infinity-right`; it has no outer affine
classifier premise.  Conversely, closure
(`short-weierstrass-affine-point-p-of-affine-distinct-x-output` and
`short-weierstrass-affine-point-p-of-affine-same-point-non-opposite-output`)
justifies classifying a `D` or `T` inner result against the remaining affine
input.

| Family and precise input condition | Inner and outer dispatcher outcomes | Status and certified support | Exact missing boundary | Suggested PR |
| --- | --- | --- | --- | --- |
| At least one of the three valid full-point inputs is infinity. | Each call touching that input returns the fixed other operand; the remaining inner call is retained on both sides. | **Pure identity reduction.** The two unconditional infinity equations, `curve-point-pair-output-point-of-fixes`, output representation/closure, and fixing canonicality are sufficient in principle. No affine classifier is involved. | A single public three-input associativity-when-an-input-is-infinity theorem (or three small lemmas) is not yet present. | A |
| Three valid affine inputs, with either inner pair classified `:same-x-other`. | No dispatcher outcome is geometrically reachable. The executable fallback would be infinity only off the stated domain. | **Impossible**, already supported generically by `affine-pair-classify-not-same-x-other-for-curve-points`. | Only convenient full-point/outer corollaries may be needed for case assembly; no new mathematics. | A |
| Both inner pairs are `O`: `b=-a` and `c=-b` in fixed affine coordinates (including the self-inverse priority case). | `AB=BC=infinity`; left is `c`, right is `a`. The two `O` consequences imply `a=c` after fixing. | **Proved structurally.** `affine-pair-classify-opposite-y-chain-implies-fixed-endpoints-equal` uses the two Stage 1 fixed-coordinate consequences, negation involution, and fixed-object reconstruction without a nonzero-y premise. `curve-point-pair-output-point-associative-when-both-inner-opposite-y` uses the affine branch and infinity equations to retain the equal fixed endpoints. No coordinate-composition algebra is used. | None for this family. | complete |
| Exactly one inner pair is `O`, while the other is `D` or `T` (the reversed family is obtained by operand/order reversal). | The side with inner `O` reduces to the untouched endpoint. The other side is an outer affine call on the endpoint and a secant or tangent output; its outer result may be `D`, `O`, or `T` but not `:same-x-other`. | **Not a pure infinity identity.** This is the inverse-translation equation `a+((-a)+c)=c` (or its reversal). Existing inverse and identity theorems do not prove it without associativity/cancellation. Commutativity supplies only the left-right mirror. | A semantic inverse/secant and inverse/tangent certificate (or a general chord-and-tangent lemma) proving the outer result equals the endpoint, including exceptional outer `O`/`T` consequences. | D/E |
| Both inner pairs are `T`. Classifier characterization forces fixed `a=b=c`, with non-self-inverse ordinate. | `AB` and `BC` are the same doubling output. The two outer calls have swapped valid operands `2a` and `a`; their common outer class may be `D`, `O`, or `T`. | **Proved structurally.** `affine-pair-classify-repeated-doubling-implies-fixed-triple` chains the two Stage 1 fixed equalities. `curve-point-pair-output-point-associative-when-both-inner-doubling` reduces both inner branches, identifies their tagged outputs by fixing congruence, obtains validity from doubling closure, and applies `curve-point-pair-output-point-commutative`; it neither classifies the outer pair nor introduces tangent/composition algebra. | None for this family. | complete |
| One inner pair is `T` and the other is `D`; the reversed tree/order is its commutative mirror. | One inner output is a tangent result and the other a secant result. Each outer affine classifier is derivable only after computing its valid inner result and is in `D/O/T`. | **Genuine mixed tangent/secant algebra.** Existing tangent and secant identities certify each individual line/output, but no theorem relates the two compositions. | A mixed semantic certificate covering equality when both outer results are affine and the derived exceptional outer results (`O`/`T`). Do not assume outer `D`. | E |
| Both inner pairs are `D`, and both derived outer pairs are `D`. | All four affine calls select the secant branch. | **Already proved** by `xcert-full-point-dispatcher-associative-when-all-distinct-x` under its exact three memberships and four ordered classifications. | None for this subfamily. | complete |
| Both inner pairs are `D`, but at least one derived outer pair is `O` or `T`. | Inner outputs are affine secant outputs. Outer outcomes are in `D/O/T`; an `O` output is infinity and a `T` output is a doubling result. The outcome on the other tree is a consequence to prove, not an independent arbitrary classifier choice. | **Genuine exceptional secant composition.** X-CERT currently requires both outer `D` classifications and therefore does not cover it. Closure and impossibility eliminate only `:same-x-other`. | Chord/secant consequences showing the matching outer outcome and output equality. Determine during certificate design whether these are degenerations of one division-free certificate or need small representation lemmas. | D/E |

The table deliberately does **not** claim that “inner opposite-y collapses the
case” in general: only the side containing that inner call collapses.  Nor does
it list outer classifications as four independent choices.  The curve equation,
inner branch relations, and closure constrain them, and the future semantic
certificate must derive the matching exceptional outcome.

The available symmetry is strong but limited.  The generic public theorem
`curve-point-pair-output-point-commutative` gives raw equality for two valid
curve points, while `curve-point-addition-relation-p-commutative` gives the
semantic reversal.  Classifier symmetry is evident from the characterizations
and is used internally by the commutativity development, but there is no named
public theorem asserting `affine-pair-classify first second` equals its swap.
There is likewise no separately named affine-dispatcher commutativity theorem.
Full commutativity can identify the mirror of an associativity family and
closes the all-equal `T/T` family; it does not justify cyclic permutation of an
associativity equation before associativity itself is known.  A small public
classifier-symmetry interface is therefore useful for case assembly, but
re-proving commutativity is not a prerequisite.

The least-risk algebra plan is to stay at the independent semantic-relation
boundary and add a small family of division-free chord-and-tangent
certificates.  First test a shared residual/telescope framework parameterized
by certified line equations, but do not make branch selection executable or
hide classifier reasoning in the certificate.  If that parameterization makes
ACL2 instantiation or hypotheses opaque, prefer two explicit certificates:
secant--tangent (its reversal supplies tangent--secant) and inverse/exceptional
secant composition.  Extending the current X-CERT theorem by merely replacing
secant slopes with tangent quotients is not yet justified: its seven residual
equations and nonzero factors encode four ordered distinct-x calls.  Whether
the exceptional outer `O/T` degenerations follow from the same polynomial
identity remains an **open feasibility question**, not a certified claim.

### Stage 3 exceptional-secant certificate audit

This audit fixes an oriented scalar notation.  Write
`A=(xa,ya)`, `B=(xb,yb)`, and `C=(xc,yc)`.  For a secant witness `m` from
`P=(xp,yp)` to `Q=(xq,yq)` with output `R=(xr,yr)`, the maintained semantic
relation supplies exactly

```text
m (xq-xp) = yq-yp
xr+xp+xq = m^2
yr+yp = m (xp-xr),
```

plus curve membership and `xp != xq`.  For a tangent witness `t` at
`P=(xp,yp)`, the doubling relation supplies

```text
t (yp+yp) = 3 xp^2 + a
xr+2 xp = t^2
yr+yp = t (xp-xr),
```

plus curve membership and `yp != -yp`.  These are already the exact
classifier-free, division-free equations in
`affine-distinct-x-secant-relation-p` and
`affine-doubling-relation-p`.  They are the selected proof layer.  The full
`curve-point-addition-relation-p` remains the later packaging and determinacy
layer; its fixed quotient witnesses are unnecessary for the field algebra.  No
new chord predicate, executable branch, or dispatcher premise is justified by
this audit.

#### A. Inverse translation with an inner secant

Assume the inner `O` facts orient `B=-A`:

```text
xb = xa
yb = -ya.
```

Let `U=(xu,yu)` be the secant output of `(B,C)` with witness `r`.  After the
`O` substitutions, its three equations are

```text
r (xc-xa) = yc+ya                         (A-D1)
xu+xa+xc = r^2                            (A-D2)
yu-ya = r (xa-xu).                        (A-D3)
```

The desired outer line through `(A,U)` has witness `s=-r`.  Equation A-D3 is
exactly `s(xu-xa)=yu-ya`; A-D2 is exactly the outer x-output equation with
output `C`; and A-D1 is exactly the outer y-output equation
`yc+ya=s(xa-xc)`.  Thus, when `xu != xa`, the existing secant relation can use
`C` itself as its output witness, with no curve polynomial identity and no
multiplicative cancellation.

When `xu=xa`, A-D3 forces `yu=ya`.  The outer affine pair is therefore the same
fixed point, not an independent tag choice.  If `ya != -ya`, its derived class
is `T`; the still-missing tangent-premise bridge must prove

```text
(-r)(ya+ya) = 3 xa^2+a,                   (A-D4)
```

while A-D2 and A-D1 already give the tangent output equations for `C`.
If `ya=-ya`, classifier priority would suggest `O`, but an affine `C` and the
inner secant condition `xc != xa` must make A-D1--A-D3 together with the curve
equations inconsistent.  This exclusion is an explicit required theorem; the
outer `O` case must not be assumed and cannot return `C`.  The next
inverse/secant implementation PR stops unless it certifies both A-D4 in the
coincident-x subcase and this self-inverse impossibility, generically.

#### B. Inverse translation with an inner tangent

Here `B=-A` and inner `T` also fixes `C=B`; hence
`xb=xc=xa`, `yb=yc=-ya`, and `yb != -yb`.  Let `U=(xu,yu)` be the tangent
output at `B` with witness `t`.  Its exact equations are

```text
t (yb+yb) = 3 xa^2+a                     (A-T1)
xu+2 xa = t^2                             (A-T2)
yu+yb = t (xa-xu).                        (A-T3)
```

The outer witness is `s=-t`.  If `xu != xa`, A-T3 is its secant line equation;
A-T2 gives the output-x equation for `C=B`; and the output-y equation is the
zero identity `yb+ya=s(xa-xa)`.  If `xu=xa`, A-T3 gives `yu=ya`, so the outer
pair fixes to `(A,A)` and is derived `T` because A-T1's domain gives
`ya != -ya`.  Negating A-T1 supplies the tangent numerator equation at `A`,
and A-T2 plus the same zero identity supply output `B`.  Consequently outer
`O` is excluded directly in this family.  The classifier-free theorem
`affine-inverse-tangent-translation` now certifies precisely this derived
`D/T` split, using the existing secant and doubling relations with witness
`-t`.  Its coincident-x branch reconstructs `U=A` and transports the tangent
domain across negation.  No additional polynomial composition certificate or
independent nonzero premise is used.  The full-point case remains deferred to
semantic assembly and the later executable lift, so dispatcher algebra is not
replayed here.

#### C. Exceptional `D/D` degenerations

Let `P=AB=(xp,yp)` have inner secant witness `p`, and
`Q=BC=(xq,yq)` have witness `r`.  Both inner `D` hypotheses provide
`xa != xb` and `xb != xc` and their two triples of secant equations.

The certified theorem `affine-dd-opposite-y-propagates-to-other-tree` completes
the oriented `DD-O` family from exactly the two inner secant relations
`(A,B,p,P)` and `(B,C,r,Q)` and the outer opposite-y relation `(P,C,infinity)`.
If the left outer pair `(P,C)` is `O`, its semantic content is
`xp=xc` and `yp=-yc`.  Substitution in the `(A,B)->P` output-y equation gives

```text
yc-ya = p (xc-xa).                        (DD-O1)
```

Together with `p(xb-xa)=yb-ya`, DD-O1 implies
`p(xc-xb)=yc-yb`.  Comparison with `r(xc-xb)=yc-yb` and the certified nonzero
factor `xc-xb` derives `p=r`.  The `(B,C)->Q` output equations then derive

```text
xq=xa
yq=-ya,                                  (DD-O2)
```

so the opposite tree's outer pair `(A,Q)` is derived `O` and both trees return
infinity.  The only multiplicative cancellation is
`field-mul-left-cancel-forward`, after commuting the products, and its nonzero
factor `xc-xb` comes solely from the `(B,C)` secant relation.  No outer
classifier, outer denominator, division, or independent nonzero premise is
used.  This is a small oriented collinearity certificate.  It is not the
four-`D` X-CERT theorem: it uses the inner `(B,C)` denominator only, and no
outer denominator exists.  The mirrored left/right result should later follow
by semantic secant operand reversal and opposite-y symmetry together with
order reversal, not by replaying the field proof or adding a second outer tag
premise.

If `(P,C)` is `T`, its semantic content is `P=C` with `yc != -yc`.  The missing
certificate must first derive that the chord through `A,B` is tangent at `C`:

```text
p (yc+yc) = 3 xc^2+a.                     (DD-T1)
```

It must then combine both inner secant triples, DD-T1, and the tangent output
triple at `C` to prove the opposite-tree result.  In particular it must derive,
from coordinates rather than an independent public classifier premise, exactly
one of:

```text
xq != xa, and a secant relation for (A,Q) with the same tangent output 2C; or
xq = xa, yq = ya, ya != -ya, and a doubling relation at A with output 2C.
```

An opposite-y conclusion on `(A,Q)` would make that tree infinity and must be
proved impossible because `C` is in the non-opposite tangent domain.  The
needed DD-T1 repeated-root bridge and this derived `D/T` opposite-tree split
are open.  They materially replace an outer secant equation and its nonzero
denominator, so they are not currently a direct specialization of
`xcert-h-scalar-reconstruction`, `xcert-s-scalar-reconstruction`, or the
four-`D` semantic X-CERT theorem.

#### Certificate decision and stopping boundaries

One large common chord certificate is **not currently justified**.  The
inverse families are witness-negation/output-reuse arguments; `DD-O` is
collinearity propagation with one legitimate cancellation; and `DD-T` needs a
new repeated-root tangency bridge.  A future shared polynomial lemma may factor
some curve algebra, but the public interfaces should remain separate oriented
certificates unless ACL2 experiments show transparent specializations with no
hidden nonzero hypotheses.

Stage 3 therefore remains partially open and is subdivided into: (1) inverse/secant,
including A-D4 and the self-inverse impossibility; (2) inverse/tangent with its
derived outer `D/T` split (**semantic boundary complete**); (3) `DD-O`
collinearity propagation (**semantic boundary complete**); and (4) `DD-T`
tangency plus its derived opposite-tree outcome.  Each implementation PR must
stop after one subdivision, must expose only semantic relations or their exact
scalar equations, and must not proceed if it needs an independent opposite
outer classification.  Mixed `D/T`, finite assembly, unrestricted
associativity, cancellation, and group packaging remain outside Stage 3.

## Hasse and Schoof tracks

### Open

- A selected, precisely cited Manin-style source and the required morphism or
  function-field degree theory.
- Frobenius/cardinality infrastructure beyond the minimal exponent assumption.
- Division polynomials, quotient-coordinate arithmetic, trace testing, bounded
  CRT reconstruction, and point-count correctness.
- Hasse's theorem and Schoof's algorithm.

### Deferred

- Performance optimization is deferred until a correct executable boundary
  exists. Benchmarks and execution regressions will remain distinct from
  logical correctness.
