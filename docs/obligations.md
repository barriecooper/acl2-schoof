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
- Equal-squares alternatives and a minimal positive Frobenius exponent
  satisfying the fixed-representative power equation.  `GFIELD` itself remains
  unrestricted by characteristic.
- PFIELD adaptation and named executable F2, F7, and F11 instances.
- The curve-level `short-weierstrass-characteristic-p` states nonzero two and
  nonzero three using the actual `GFIELD` operations, exposes both facts
  separately, and proves that a self-inverse field element is zero under that
  premise.  F7, F11, and the concrete F7X2 extension satisfy the boundary.

### Qualifications and non-claims

- The Frobenius exponent is not certified as a cardinality, least exponent, or
  prime power. No generic field enumeration is supplied.
- F7/F11 computations validate concrete execution and functional
  instantiation; they do not enlarge the generic theorem statements.

### Open or deferred

- Generic finite-field cardinality/enumeration metadata and a connection from
  that metadata to the Frobenius exponent are open.
- Characteristics two and three are deferred for the initial curve scope;
  their exclusion is a curve predicate, not a generic-field axiom.

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

### Certified continuations

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

This inventory is authoritative for finite semantic assembly.  Here `D`, `O`,
and `T` mean the public affine relations
`affine-distinct-x-secant-relation-p`,
`affine-opposite-y-infinity-relation-p`, and
`affine-doubling-relation-p`; they are not names for arbitrary classifier
values.  For valid affine operands, `curve-point-addition-case-coverage` and
`affine-pair-classify-not-same-x-other-for-curve-points` leave exactly these
three geometric cases.  The executable `:same-x-other` fallback is unreachable
on curve points.  Infinity is a separate tagged-point identity case, not a
fourth affine relation.

For `P=A+B` and `Q=B+C`, the exact inner-pair matrix is:

| inner `AB` | inner `BC` | status after symmetry | certified boundary or missing family |
| --- | --- | --- | --- |
| `O` | `O` | complete | `curve-point-pair-output-point-associative-when-both-inner-opposite-y` |
| `O` | `D` | complete; reverse point order gives `D/O` | `affine-inverse-secant-translation`, whose conclusion is outer `D` or `T` with output `C` and witness `-r` |
| `O` | `T` | complete; reverse point order gives `T/O` | `affine-inverse-tangent-translation`, whose conclusion is outer `D` or `T` with output `B` and witness `-t` |
| `T` | `T` | complete structurally | `curve-point-pair-output-point-associative-when-both-inner-doubling`; both premises force fixed `A=B=C`, and outer commutativity closes the trees |
| `D` | `D` | complete at the affine semantic family level | ordinary outer `D/D` is covered by the X-CERT theorems; outer `O/O` by `affine-dd-opposite-y-propagates-to-other-tree` and its left-tree mirror; an outer `T` and its opposite-tree `D/T` result by `affine-dd-t-translation` and point-order reversal |
| `D` | `T` | complete at the oriented affine semantic family level | `affine-dt-d-translation` combines the two left-outer-secant outcomes; `affine-dt-left-output-opposite-y-propagates-to-right-output` supplies the witness-free O/O outcome |
| `T` | `D` | complete structurally | `affine-td-d-translation` supplies the mirrored affine outcomes and `affine-td-left-output-opposite-y-propagates-to-right-output` supplies O/O; both reverse secants explicitly and reuse the D/T family |

Thus the former phrase “mixed `D/T`” refers **only to the types of the two
inner additions**, not to an outer pair and not to the DD-T naming convention.
`D-D` is complete, `T-T` is complete, and only one oriented `D-T` family is
new mathematics.  `T-D` is its point-order/operand-reversal mirror.  Relation
reversal preserves the secant witness; doubling is intrinsically a one-input
relation; opposite-y reversal is
`affine-opposite-y-infinity-relation-p-symmetric`; and full relation reversal
is `curve-point-addition-relation-p-commutative`.

The completed `D/D` submatrix is more precise than a free outer three-by-three
product.  If both outer additions are secants, the public X-CERT endpoints
`xcert-final-x-coordinates-equal`, `xcert-final-y-coordinates-equal`,
`xcert-untagged-outputs-equal`, and `xcert-tagged-outputs-equal` have orientation
`(A+B)+C = A+(B+C)` and use the four canonical ordered secant witnesses.  If
one outer relation is `O`, DD-O propagates `O` to the other tree (the converse
orientation is the structural theorem
`affine-dd-opposite-y-propagates-to-left-tree`).  If the left outer relation is
`T`, the exact equations are `A+B=C`, `B+C=Q`, `C+C=D`, and the theorem
`affine-dd-t-translation` derives either `A+Q=D` by a secant or `A+A=D` by a
doubling, in both cases with witness `(p+t)-r`.  Reversing `C,B,A` supplies the
right-outer-`T` orientation.  There is therefore no remaining DD family.

Infinity inputs are already complete through
`curve-point-pair-output-point-associative-when-infinity-input`.  An inner `O`
produces canonical infinity on that tree, while the inverse/secant or
inverse/tangent translation supplies the non-infinity tree.  Malformed ACL2
objects matter only to the later total executable lift through the fixers; they
are not extra semantic cases for the finite valid-curve-point theorem.

Finite affine semantic assembly must consume the `D`, `O`, or `T` relation for
both inner additions, closure for affine inner outputs, and the matching outer
relation(s).  Its natural endpoint is
`curve-point-addition-relation-p` for a common output on each tree, rather than
a permanently exposed lower-level disjunction: the latter is only the input to
assembly.  All matrix cells are now certified. The remaining task is finite affine
semantic assembly through the independent relation and case-coverage books.

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
If `ya=-ya`, classifier priority suggests `O`.  The proposed generic
self-inverse exclusion is **false under the current constrained interfaces**:
the `GFIELD` kernel admits characteristic two, while the separately constrained
`ADDITIVE-FIELD` characteristic-exclusion interface is not connected to the
`GFIELD` operations used by curve coordinates.  A concrete model is the
two-element `GFIELD` with `a=0`, `b=1`, `A=B=U=(0,1)`, `C=(1,0)`, and `r=1`.
Both points satisfy `y^2=x^3+1`; `B=-A`; `(B,C,r,U)` satisfies the distinct-x
secant relation; and `xu=xa` and `ya=-ya`.  Thus the requested combined `D/T`
conclusion is also false: the outer pair `(A,U)` is opposite-y/self-inverse,
not a valid doubling pair.

The characteristic interface is now certified as
`short-weierstrass-characteristic-p`: it makes
`field-add(field-one,field-one)` nonzero for the same constrained `GFIELD`
operations and also records nonzero three.  Under that explicit curve premise,
`ya=-ya` gives `ya=0`; A-D4 gives
`3*xa^2+a=0`; the curve equation gives `xa^3+a*xa+b=0`.  The certified
scalar theorem `short-weierstrass-common-root-implies-discriminant-zero` solves
these equations division-free as `a=-(3*xa^2)` and `b=2*xa^3`, then proves the
exact checked-in identity `4*a^3+27*b^2=0`, where `4=(1+1)^2` and
`27=(1+1+1)^3` in the constrained field operations and the coefficients are
fixed.  This contradicts
`short-weierstrass-discriminant-expression-nonzero`.  The public semantic
theorem `affine-inverse-secant-coincident-x-excludes-self-inverse` therefore
certifies that the coincident-x outer ordinate is not self-inverse.  Only the
self-inverse-to-zero step consumes the nonzero-two projection; A-D4, the
scalar resultant algebra, and the contradiction do not consume nonzero three.
The combined characteristic predicate remains the single public premise of
the combined family and of its outer-doubling branch.  It is absent from the
ordinate-coincidence and outer-distinct-x theorems, which are
characteristic-independent.

The earlier `ADDITIVE-FIELD` theorems remain a separate reusable
functional-instantiation template over `additive-field-fix`, zero, one, add,
and repeated addition.  F7 and F11 instantiate it only after separately
proving its nonzero hypotheses.  It cannot instantiate to unrestricted
`GFIELD` without an additional assumption: the kernel's characteristic-two
Boolean witness refutes the required nonzero-two obligation.  The new curve
predicate avoids claiming such a generic instantiation.
The former architectural blocker is therefore resolved at the intended curve
boundary.  The
self-contained additive-normalization prerequisite is now certified separately:
`field-sub-eliminate-common-right-summand` removes a shared right summand from
two equal field sums, and
`short-weierstrass-curve-equations-imply-square-difference` instantiates it to
cancel the common curve constant from the two scalar curve equations.  This
unfactored subtraction bridge now feeds the certified generic
`field-cubic-plus-linear-difference-factorization`, whose public
`field-difference-of-cubes` prerequisite and a local linear-term distribution
factor the remaining right-hand side.  The certified
`short-weierstrass-curve-equations-imply-factored-square-difference` corollary
therefore exposes the single factor `xc-xa` from the curve square difference.
The generic `field-difference-of-squares` now supplies the matching
`(yc-ya)(yc+ya)` factorization.  Combining it with the inverse/secant line
equation exposes the separately proved common-factor equality
`(xc-xa)*(r*(yc-ya))=(xc-xa)*(xc^2+xc*xa+xa^2+a)`.  The inner secant domain,
together with coordinate field-element closure, makes `xc-xa` nonzero via the
kernel subtraction-zero theorem; left cancellation therefore certifies
`r*(yc-ya)=xc^2+xc*xa+xa^2+a`.  The public semantic specialization derives
this relation directly from the inverse relation, the inner secant relation,
and coincident outer x-output, without a characteristic premise, inverse, or
division.  The next bounded certificate consumes exactly the repeated-root
equation `r*(yc-ya)=xc^2+xc*xa+xa^2+a`, the inverse-substituted secant equation
`r*(xc-xa)=yc+ya`, and the coincident-output equation `r^2=xc+xa+xa`.  Its
local ordinate substitution is `yc-ya=r*(xc-xa)-(ya+ya)`, and its separately
staged quadratic simplification is
`(xc+xa+xa)*(xc-xa)=xc^2+xc*xa-(xa^2+xa^2)`.  These division-free identities
certify A-D4, `(-r)*(ya+ya)=3*xa^2+a`, both as an unrestricted generic field
theorem and directly from the three semantic relation premises.  A-D4 is
therefore complete and characteristic-independent; it uses no inverse,
nonzero premise, curve equation, or characteristic assumption.  The subsequent
self-inverse exclusion is also complete: it composes
self-inverse-to-zero, A-D4, the scalar curve equation, the division-free
resultant identity, and the constrained nonzero discriminant.  It uses no
classifier, denominator, division, inverse, or independent characteristic
premise.  The public
`affine-inverse-secant-coincident-x-implies-ordinate-equality` theorem now
reconstructs `yu=ya` directly from the inner output-y equation when `xu=xa`.
For `xu!=xa`,
`affine-inverse-secant-translation-outer-distinct-x` packages the outer secant
with the exact witness `-field-fix(r)` and equations
`(-r)(xu-xa)=yu-ya`, `xc+xa+xu=(-r)^2`, and
`yc+ya=(-r)(xa-xc)`.  This branch needs neither characteristic nor
cancellation.  For `xu=xa`,
`affine-inverse-secant-translation-outer-doubling` combines ordinate
coincidence, the public self-inverse exclusion, A-D4, A-D2, and A-D1/A-D3 to
establish curve membership of `A,C`, the tangent domain, numerator equation,
and both output equations for the same negated witness.  Finally
`affine-inverse-secant-translation` splits only on `xu=xa` and certifies the
outer D/T disjunction.  Outer O is excluded by the self-inverse theorem rather
than assumed away by a classifier premise.  The inverse/secant semantic family
is complete.  The single oriented mixed-inner `D/T` certificate, its structural mirror,
finite semantic assembly, unrestricted associativity, executable lifting, and
group-law packaging remain open.

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

If `(P,C)` is `T`, its semantic content is `P=C` with `yc != -yc`.  The former
proposed DD-T1 equation `p*(yc+yc)=3*xc^2+a` is **false** and is retracted, not
left as an open theorem.  A secant output is the reflection of the third
intersection of its chord with the curve.  Consequently `P=C` says that the
line through `A,B` meets the curve at `-C`; it does not make that line tangent
at `C`.  The first secant witness `p` and the actual tangent witness `t` are
independent.  Negating `p` does not repair the assertion.

The checked-in F11 curve gives a small countermodel: with `a=1`, `b=6`,
`A=(2,4)`, `B=(3,5)`, `C=(7,2)`, and `p=1`, all three points are on the curve
and `(A,B,p,C)` satisfies the secant relation.  The second secant exists with
`r=2` and `Q=(5,2)`; `C` is in the tangent domain, with `t=4` and
`D=2C=(2,7)`.  Nevertheless `p*(yc+yc)=4` while `3*xc^2+a=5` modulo 11;
`(-p)*(yc+yc)=7` also differs from 5.  The outer relation `(A,Q)->D` has
witness `s=3`.

The corrected independent-witness audit starts from exactly these nine
relation equations (all operations and coefficients are fixed as in the
semantic predicates, and the displayed associations abbreviate the checked-in
`field-add` trees):

```text
p*(xb-xa)=yb-ya        xc+xa+xb=p^2       yc+ya=p*(xa-xc)
r*(xc-xb)=yc-yb        xq+xb+xc=r^2       yq+yb=r*(xb-xq)
t*(yc+yc)=3*xc^2+a     xd+xc+xc=t^2       yd+yc=t*(xc-xd).
```

Both inner secant triples and the actual tangent triple must therefore remain
visible.  The audited candidate for the opposite-tree witness is
`s=(p+t)-r`.  It is the specialization suggested by the four-secant S balance
`p+q=r+tt` after the left outer witness `q` is replaced by the independent
tangent witness `t`; the existing X-CERT theorem cannot itself be instantiated,
because it assumes distinct-x outer secants and performs the corresponding
cancellation.  Exhaustive temporary computations on the checked-in F11 curve
and on several nonsingular F7 curves found this candidate correct in every
applicable curve case.  In the countermodel it gives `1+4-2=3`, the actual outer
slope.  The tempting candidates `p`, `-p`, `r`, and `t` respectively give
`1`, `10`, `2`, and `4` there and are all refuted.  Those computations did not
establish that the nine relation equations alone suffice.

The corrected curve-semantic outer-distinct-x endpoint is now certified.  Its
common-curve bridge uses the `A,B` curve equations through the existing input
secant identity and the `A,Q` curve equations through the existing semantic
outer secant slope reconstruction.  Together with the first two complete
secant triples and only the tangent numerator equation at `C`, the
pre-cancellation X-CERT H/S algebra specializes with `xab=C`, `xbc=Q`,
`q=t`, and an internal certified secant slope `u` for `(A,Q)`.  Its exact
factored residual is

```text
(xq-xa) * (p+t-(r+u)) = 0.
```

The outer premise `xq != xa`, coordinate closure, and the field subtraction
zero theorem make `xq-xa` nonzero; the existing X-CERT S cancellation gives
`p+t=r+u`.  Hence the exact fixed witness `s=(p+t)-r` equals `u`, and the
certified `u*(xq-xa)=yq-ya` equation yields
`s*(xq-xa)=yq-ya`.  Equivalently, before this substitution the desired slope
residual has the aligned factorization

```text
(xq-xa) * (s*(xq-xa)-(yq-ya)) = 0.
```

The outer output-x endpoint is also certified.  Its earliest common-curve
bridge is `xcert-h-scalar-reconstruction`, specialized with `xab=C`, its
second input identity replaced by the tangent identity at `C`, and its left
outer output `xl=D`.  The pre-cancellation residual is

```text
(xc-xb) * ((p-r)*(p+t)-(xa-xc)) = 0.
```

The only cancellation factor is `xc-xb`; its nonzero fact comes from the
inner `(B,C,r,Q)` secant relation.  This gives H zero.  The three checked-in
output-x equations give the X-CERT telescope zero, while the already certified
balance gives S zero.  `xcert-composition` therefore identifies the canonical
outer secant output's x-coordinate with `xd`.  Separately, cancellation of the
outer slope equation against the canonical slope reconstruction, using only
`xq-xa != 0`, proves locally that the fixed witness `s=(p+t)-r` equals
`affine-distinct-x-slope(A,Q)`.  Transport through the canonical output-x
rearrangement certifies the exact associated equation
`(xd+xa)+xq=s*s`.

The outer output-y endpoint is now certified as well.  It reuses the certified
witness equality `s=affine-distinct-x-slope(A,Q)` and obtains
`x(affine-distinct-x-output(A,Q))=xd` by cancelling the common two-coordinate
tail from the certified outer output-x equation and the canonical output-x
rearrangement.  The ordinate bridge is the field-only X-CERT final-y theorem,
specialized with `xab=C`, left slope `t`, left output `D`, right slope the
canonical outer slope, and right output the canonical `(A,Q)` output.  Its exact
bounded residual is the six output-y residual reduction

```text
yd-y(E) = (p-r)*(xd-xb) + (r-t)*(xa-xc),
```

with the H coordinate bridge and balance `p+t=r+u` cancelling the right side.
Thus `y(E)=yd`; no equal-x sign alternative or sign-selection premise is used.
The canonical output-y rearrangement then certifies
`yd+ya=s*(xa-xd)` in the relation's exact orientation.

No characteristic premise, classifier premise, division, inverse, or independent
denominator is used.  All three outer distinct-x scalar endpoints are complete,
and `affine-dd-t-outer-distinct-x-translation` now packages them as the public
secant relation `(A,Q,s,D)` with the exact witness
`s=(field-sub (field-add (field-fix p) (field-fix t-slope)) (field-fix r))`.
Thus the DD-T outer distinct-x branch is complete.  This packaging proof is
characteristic-independent and classifier-free.

The coincident-x ordinate boundary is now certified.  The reusable theorem
`short-weierstrass-equal-x-implies-equal-or-neg-y` gives the characteristic-
independent common-curve dichotomy `yq=ya` or `yq=-ya`.  The new structural
mirror `affine-dd-opposite-y-propagates-to-left-tree` reverses both secant
operands and the opposite-y pair, then applies the existing oriented DD-O
theorem to the reversed point order; it replays none of the DD-O field algebra.
Under the temporary `yq=-ya` alternative, the two secant relations supply curve
membership and `xq=xa` constructs the local `(A,Q)` opposite-y relation.  The
mirror derives `(C,C)` opposite-y, hence `yc=-yc`, contradicting exactly the
non-self-inverse tangent-domain conjunct in
`affine-doubling-relation-p(C,t,D)`.  Therefore
`affine-dd-t-coincident-x-implies-ordinate-equality` certifies `yq=ya` from only
the two inner secant relations, doubling at `C`, and `xq=xa`.  No
characteristic predicate, classifier, denominator, division, or inverse is
used.  Coincident-x ordinate reconstruction and outer opposite-y exclusion are
complete.  The tangent domain at `A` is now certified as well.  Under the
temporary assumption `ya=-ya`, the certified equality `yq=ya`, the public
equality `xq=xa`, and curve membership supplied by the two secant relations
construct the local `(A,Q)` opposite-y relation with canonical infinity output.
Mirrored DD-O propagation produces the `(C,C)` opposite-y relation and hence
`yc=-yc`, contradicting the tangent-domain conjunct of doubling at `C`.
Consequently `affine-dd-t-coincident-x-excludes-self-inverse` proves
`ya != -ya` characteristic-independently, without coordinate algebra.
The generic additive prerequisite for that numerator reconstruction is now
certified separately: from exactly `yb-ya=p*delta` and
`ya+yb=r*delta`, `field-two-line-equations-imply-doubled-first-ordinate`
derives `ya+ya=(r-p)*delta`.  Its proof subtracts the two oriented line
equations, using the bounded identities `(ya+yb)-(yb-ya)=ya+ya` and
`r*delta-p*delta=(r-p)*delta`; it needs no element or nonzero hypotheses.
The DD-T coincident-x tangent numerator at `A` is now certified.  With
`delta=xb-xa`, the first secant slope equation and the second secant output-y
equation (after the certified `xq=xa`, `yq=ya` substitution) instantiate
`field-two-line-equations-imply-doubled-first-ordinate` exactly as

```text
ya+ya=(r-p)*delta.
```

The audited H specialization consumes the common-curve input-secant identity
for `(A,B,p)`, the tangent numerator identity at `C`, and the inner `(B,C,r,Q)`
secant equations.  `xcert-h-scalar-reconstruction` yields
`(p-r)*(p+t)=xa-xc`; its only cancellation factor is `xc-xb`, whose
nonzeroness comes from the second secant relation.  The fixed witness
`s=(p+t)-r` separately satisfies the definitional balance `p+t=r+s` by field
normalization alone.

The remaining bounded algebra is staged as

```text
s*(r-p) = -((p-r)*(p+t)) + (p-r)*r,
s*(ya+ya) = ((xc-xa) + (p-r)*r)*delta,
           = p*(r*delta) + (((xc-xa)-r^2)*delta).
```

The second line equation and first input-secant identity replace
`p*(r*delta)` by `xb^2+xb*xa+xa^2+a`; the second secant output-x equation with
`xq=xa` replaces `r^2` by `(xa+xb)+xc`.  The smallest final coordinate
residual is therefore

```text
(xb^2+xb*xa+xa^2+a)
 + (((xc-xa)-((xa+xb)+xc))*(xb-xa))
 = xa^2+(xa^2+(xa^2+a)).
```

A final bounded association converts this to `3*xa^2+a`.  No characteristic
premise, classifier, division, inverse, outer denominator, or additional
cancellation is used.  The tangent numerator at `A` is complete.

The coincident-x output-x equation is now certified as
`affine-dd-t-coincident-x-output-x-equation`.  Its canonical slope is
`u=affine-same-point-non-opposite-slope(A)`.  The tangent-domain theorem gives
`ya != -ya`, hence `ya+ya != 0` by additive-inverse uniqueness; cancelling
exactly that factor between the reconstructed tangent numerator and the
canonical tangent numerator proves `s=u`.  The other cancellation is the
already-audited `xc-xb` in H reconstruction, whose nonzeroness comes from the
second secant relation.

For the canonical output `E=affine-same-point-non-opposite-output(A)`, its
output-x rearrangement gives `(x(E)+xa)+xa=u^2`.  X-CERT composition is
specialized with `xab=C`, `xbc=A`, left outer slope/output `t/D`, and right
outer slope/output `u/E`.  H is zero from `(p-r)*(p+t)=xa-xc`; S is zero from
`p+t=r+s` and `s=u`; and the telescope is zero from the two secant output-x
equations, doubling output-x at C, and canonical output-x at A.  Composition
therefore gives `xd-x(E)=0`, so `x(E)=xd`, and finally
`(xd+xa)+xa=s^2`.  This proof is characteristic-independent and introduces no
classifier, division, inverse, outer denominator, or independent nonzero
premise.

The coincident-x output-y equation is now certified as
`affine-dd-t-coincident-x-output-y-equation`.  The proof reuses the canonical
tangent slope `u=affine-same-point-non-opposite-slope(A)` and canonical output
`E=affine-same-point-non-opposite-output(A)`.  The output-x reconstruction
supplies `x(E)=xd`.  Specializing `xcert-field-only-final-y-equal` with
`xab=C`, left slope/output `t/D`, and right slope/output `u/E` gives the exact
pre-reconstruction residual

```text
yd-y(E)=(p-r)*(xd-xb)+(r-t)*(xa-xc).
```

The H input is `(p-r)*(p+t)=xa-xc`; the S input is
`(p+t)-(r+u)=0`, obtained from the definitional balance `p+t=r+s` and `s=u`.
Together with the two output-x equations these eliminate the residual, while
`x(E)=xd` specializes the canonical output-y rearrangement to the right-hand
line required by the field theorem.  Thus `y(E)=yd`; substituting that equality,
`x(E)=xd`, and `u=s` in the canonical output-y rearrangement proves
`yd+ya=s*(xa-xd)`.

No cancellation is introduced by the final-y reconstruction.  The complete
coincident-x chain uses only the two earlier cancellations: `xc-xb`, nonzero
from the second distinct-x secant relation, in H reconstruction; and `ya+ya`,
nonzero from the certified `ya != -ya` tangent domain and additive-inverse
uniqueness, in the canonical slope identification.  There is no characteristic
premise, classifier premise, division, inverse, outer denominator, or
independent nonzero hypothesis.  All scalar and domain clauses for the
coincident-x doubling branch are now certified.

`affine-dd-t-coincident-x-translation` now packages that branch into the public
doubling relation `(A,s,D)`, with the exact witness
`s=(field-sub (field-add (field-fix p-slope) (field-fix t-slope))
(field-fix r-slope))`.  Its direct semantic proof invokes the five public
endpoints `affine-dd-t-coincident-x-implies-ordinate-equality`,
`affine-dd-t-coincident-x-excludes-self-inverse`,
`affine-dd-t-coincident-x-tangent-equation`,
`affine-dd-t-coincident-x-output-x-equation`, and
`affine-dd-t-coincident-x-output-y-equation`; curve membership of `A` and `D`
comes from the first secant and the doubling relation at `C`.  The packaging is
characteristic-independent and adds no classifier, division, inverse, or
independent denominator premise.  Thus the DD-T coincident-x semantic doubling
branch is complete.

`affine-dd-t-translation` now completes the DD-T family at the affine semantic
relation boundary.  From exactly the two secant relations `(A,B,p,C)` and
`(B,C,r,Q)` and the doubling relation `(C,t,D)`, it splits only on `xq=xa`.
The disequality case invokes
`affine-dd-t-outer-distinct-x-translation` for the secant result, and the
equality case invokes `affine-dd-t-coincident-x-translation` for the doubling
result.  Both disjuncts use the syntactically identical witness
`(field-sub (field-add (field-fix p-slope) (field-fix t-slope))
(field-fix r-slope))`.  The composition is characteristic-independent and has
no classifier, division, inverse, or independent denominator premise; neither
branch proof is replayed.

The oriented mixed-inner `D/T` family is now complete at the affine semantic
boundary: `affine-dt-d-translation` combines its two left-outer-secant
outcomes, and `affine-dt-left-output-opposite-y-propagates-to-right-output`
supplies its witness-free O/O outcome. The structural T/D mirror is also
complete; finite affine semantic assembly, unrestricted associativity,
executable lift, and final group-law packaging remain. Detailed current status is maintained below rather than in
this historical D/D audit.

The field-only audit is stopped by a concrete F11 countermodel to the first
requested endpoint.  Take

```text
a=8,
A=(xa,ya)=(0,1), B=(xb,yb)=(1,1), C=(xc,yc)=(10,10),
Q=(xq,yq)=(1,10), D=(xd,yd)=(2,1),
p=0, r=1, t=0.
```

All nine displayed equations hold modulo 11 (including both nonzero inner
x-differences and the tangent-domain inequality `yc != -yc`).  However the
fixed candidate is `s=(p+t)-r=10`, and the outer slope residual is
`s*(xq-xa)-(yq-ya)=1`, not zero.  Thus no theorem with exactly those nine
hypotheses can certify even the outer slope equation, and the output-x and
output-y endpoints cannot be packaged as the requested combined boundary.
No omission among the nine equations causes this failure.  The countermodel
is not a common-curve model: the three coordinates give incompatible values
of the constant `b` in `y^2=x^3+a*x+b`.  Consequently a curve-equation bridge
(or an equivalent scalar consequence of common curve membership) is
mathematically necessary before this witness can be reconstructed.  Merely
adding the tangent-domain premise, either inner nonzero denominator, a
characteristic premise, or an outer distinct-x premise does not remove this
countermodel.

The completed curve-aware outer-distinct-x scalar certificate derives, without
division, the equation:

```text
yd+ya=s*(xa-xd),                         s=(p+t)-r,
```

The three certified scalar equations are now packaged as the public secant
relation `(A,Q,s,D)` with exact fixed witness `s=(p+t)-r`; this completes only
the DD-T outer distinct-x branch.  A later coincident-x certificate must decide
from the same nine equations whether `xq=xa` forces
`yq=ya`; concrete F7 curve cases support the same `s=(p+t)-r` as the tangent witness
at `A`.  If so, it must separately derive

```text
s*(ya+ya)=3*xa^2+a
xd+xa+xa=s^2
yd+ya=s*(xa-xd)
```

and derive `ya != -ya`, rather than assuming an outer classifier.  The outer
slope and output-x scalar steps now use the certified common-curve
H/S bridge.  The next exceptional scalar step is the outer output-y equation;
after it, the dichotomy at `xq=xa` remains: exclude
`yq=-ya` and establish `yq=ya` from the nine equations and `yc != -yc`.
The concrete order-two pattern suggests that the tangent domain at `C`, not an
arbitrary denominator, is the ultimate source, but no generic division-free
certificate for that implication has yet been audited.  Nonsingularity may be
needed only if the scalar derivation reaches a common curve/tangent root; it
must not be added speculatively.

Thus DD-T must eventually derive, from coordinates rather than an independent
public classifier premise, exactly one of:

```text
xq != xa, and a secant relation for (A,Q) with the same tangent output 2C; or
xq = xa, yq = ya, ya != -ya, and a doubling relation at A with output 2C.
```

An opposite-y conclusion on `(A,Q)` would make that tree infinity and must be
proved impossible from the scalar equations; it may not be excluded by a
public classifier premise.  The coincident-x ordinate/domain bridge and the three outer-doubling identities
are the remaining replacement obligations.  They are open.  They are not currently a
direct specialization of
`xcert-h-scalar-reconstruction`, `xcert-s-scalar-reconstruction`, or the
four-`D` semantic X-CERT theorem.

#### Certificate decision and stopping boundaries

One large common chord certificate is **not currently justified**.  The
inverse families are witness-negation/output-reuse arguments; `DD-O` is
collinearity propagation with one legitimate cancellation; and `DD-T` needs a
new independent-witness scalar reconstruction.  A future shared polynomial
lemma may factor some curve algebra, but the public interfaces should remain
separate oriented
certificates unless ACL2 experiments show transparent specializations with no
hidden nonzero hypotheses.

Stage 3 is complete through inverse/secant, inverse/tangent, DD-O, and DD-T at
the affine semantic relation boundary.  Stage 4 now has exactly one genuinely
new orientation: inner `D/T`; inner `T/D` is its structural mirror.  Finite
assembly, unrestricted associativity, cancellation, and group packaging remain
later stages.

### Associativity status

The at-a-glance family matrix and public boundaries are maintained in
[associativity status](status-associativity.md). The detailed mixed D/T
reconstruction, including residuals, cancellations, finite validation, and the
field-only countermodel, is preserved in the
[mixed D/T certificate audit](audits/mixed-dt-certificate.md).

#### Certified mixed-inner D/T boundaries

All entries use the orientation `A+B=P` by secant `p`, `B+B=Q` by doubling
`t`, and `P+B=R` by secant `q`; the reconstructed opposite-tree witness is
`s=(p+q)-t`.

| Boundary | Public theorem | Exact semantic scope | New cancellation at this boundary | Detail |
|---|---|---|---|---|
| Confluent H field bridge | `xcert-confluent-h-scalar-reconstruction` | Common-curve scalar reconstruction for the two oriented secants and the tangent at B | `xB-xA`, `xB-xP` | [Audit](audits/mixed-dt-certificate.md) |
| Factored S bridge | `xcert-s-factored-reconstruction-from-h` | Field-only factorization of the S balance once confluent H holds | None; factor retained | [Audit](audits/mixed-dt-certificate.md) |
| Outer distinct-x slope | `affine-dt-d-outer-distinct-x-slope-equation` | Four semantic premises plus `xQ != xA`; identifies the canonical A/Q secant slope with s | `xQ-xA` | [Audit](audits/mixed-dt-certificate.md) |
| Outer distinct-x output x | `affine-dt-d-outer-distinct-x-output-x-equation` | Same premises; proves the secant output-x equation for R | No new premise; locally reuses slope identification | [Audit](audits/mixed-dt-certificate.md) |
| Outer distinct-x output y | `affine-dt-d-outer-distinct-x-output-y-equation` | Same premises; proves the secant output-y equation for R | None beyond inherited slope work | [Audit](audits/mixed-dt-certificate.md) |
| Outer distinct-x secant package | `affine-dt-d-outer-distinct-x-translation` | Packages the preceding clauses as `affine-distinct-x-secant-relation-p(A,Q,s,R)` | None | [Audit](audits/mixed-dt-certificate.md) |
| Opposite-y propagation | `affine-dt-opposite-y-propagates-to-left-output` | From A+B=P, B+B=Q, and A opposite Q, derives P opposite B | `xB-xA` internally | [Audit](audits/mixed-dt-certificate.md) |
| Coincident-x ordinate equality | `affine-dt-d-coincident-x-implies-ordinate-equality` | Four semantic premises plus `xQ=xA`; proves `yQ=yA` | None | [Audit](audits/mixed-dt-certificate.md) |
| Tangent domain | `affine-dt-d-coincident-x-excludes-self-inverse` | Same coincident-x scope; proves `yA != -yA` | None beyond inherited propagation | [Audit](audits/mixed-dt-certificate.md) |
| Tangent numerator | `affine-dt-d-coincident-x-tangent-equation` | Same coincident-x scope; proves the tangent numerator equation at A for s | None beyond inherited confluent H | [Audit](audits/mixed-dt-certificate.md) |
| Coincident-x output x | `affine-dt-d-coincident-x-output-x-equation` | Same scope; proves the doubling output-x equation for R | `yA+yA` for canonical slope identification | [Audit](audits/mixed-dt-certificate.md) |
| Coincident-x output y | `affine-dt-d-coincident-x-output-y-equation` | Same scope; proves the doubling output-y equation for R | None beyond inherited slope identification | [Audit](audits/mixed-dt-certificate.md) |
| Coincident-x doubling package | `affine-dt-d-coincident-x-translation` | Packages the domain and scalar clauses as `affine-doubling-relation-p(A,s,R)` | None | [Audit](audits/mixed-dt-certificate.md) |
| Outer O/O propagation | `affine-dt-left-output-opposite-y-propagates-to-right-output` | From A+B=P, B+B=Q, and P opposite B, derives A opposite Q with the same infinity payload | `xB-xA` inside the reused inverse/secant tangent equation; `yB+yB` for slope identification | [Audit](audits/mixed-dt-certificate.md) |
| Left-outer-secant family combination | `affine-dt-d-translation` | Splits on `xQ=xA` and derives right outer secant or doubling with the single witness `(p+q)-t` | None; inherits the branch certificates | [Audit](audits/mixed-dt-certificate.md) |

#### Open

- T/D structural mirror.
- Finite affine semantic assembly.
- Semantic-to-executable dispatcher lift.
- Unrestricted associativity.

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
