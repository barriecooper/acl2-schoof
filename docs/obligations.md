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
- Deriving exact `H=(p-r)(p+q)-(xa-xc)=0` remains open.  Its prospective proof
  combines those three ordered input-secant instances, closure of `AB` from the
  `(A,B)` hypotheses, and the existing output-x/output-y rearrangements.  The
  necessary local field reassociation and cancellation bridge has not yet been
  certified.
- Exact `S=(p+q)-(r+tt)=0` also remains open.  Its prospective ordered-secant
  reconstruction additionally involves `(A,BC)` and closure of `BC`; it is not
  available from output-y rearrangement alone and was not assumed from `H` or
  from associativity.
- The four output-x residuals were already zero before this input-secant step.
  The X-CERT composition has not been simplified with any H/S result.
- Cancellation, exceptional branches, curve associativity, and any later use
  in Schoof machinery.

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

- Full tagged-point associativity.
- Cancellation laws.
- Abstract group or abelian-group packaging.
- Scalar multiplication and its laws.

Associativity is not ready for a direct proof. The prerequisite audit specified
in [the proof plan](proof-plan.md#phase-1-prepare-associativity) must inventory
existing cancellation/substitution/fixing lemmas, identify reusable
branch-independent division-free algebra, and record missing tight lemma groups
before the case proof begins.

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
