# Proof obligation ledger

This is the authoritative ledger of certified, open, and deferred formal
boundaries. It records public endpoints rather than proof history or internal
lemmas. Stable design belongs in [architecture.md](architecture.md), execution
contracts in [execution-boundaries.md](execution-boundaries.md), forward order
in [proof-plan.md](proof-plan.md), and detailed evidence in
[the audits](audits/).

Status labels have the following meanings:

- **Certified** — a registered book certifies the endpoint under repository
  policy.
- **Open** — the maintained route requires the boundary and no public endpoint
  yet closes it.
- **Deferred** — the boundary is intentionally outside the current phase.

## 1. Development policy and trust

| Boundary | Status | Public endpoint | Open dependency / detail |
|---|---|---|---|
| Registered certification tree | Certified | `books/top.lisp` | Certification is the definition of done. |
| Prohibited proof escapes | Certified | `scripts/check-trust.sh`; `scripts/check-execution-policy.sh` | Repository scans reject skipped proofs, project axioms, trust tags, raw Lisp, and equivalent escapes. |
| Documentation and policy checks | Certified | `scripts/check-docs.py`; `Makefile` | Maintained links, ledger structure, trust, and execution policy are checked together. |

Concrete execution and finite enumeration are evidence, not generic proof.
Guard verification establishes execution admissibility, not semantic
correctness. The full evidence model is maintained in
[execution boundaries](execution-boundaries.md#evidence-model).

## 2. Generic field infrastructure

| Boundary | Status | Public endpoint | Open dependency / detail |
|---|---|---|---|
| Total commutative-field kernel | Certified | `field-fix`; `field-add`; `field-neg`; `field-mul`; `field-inv` | `GFIELD` remains unrestricted by characteristic. |
| Natural powers | Certified | `field-pow`; `field-pow-correct`; `field-pow-fast-correct` | Generic fast/spec correspondence is certified. |
| Minimal Frobenius exponent | Certified | `field-frobenius-exponent`; `field-pow-instance-of-field-frobenius-exponent` | This is not a cardinality or least-exponent theorem. |
| Prime-field clients | Certified | PFIELD adapter and named F2, F7, and F11 operations | Concrete clients supply instantiation and execution evidence. |
| Contextual field characteristic | Certified | `field-characteristic-p`; `field-characteristic-unique` | Transparent bounded least-positive additive period; does not imply finiteness. |
| PFIELD characteristic | Certified | `pfield-modulus-is-field-characteristic`; transported characteristic laws | Functional instance of the generic theory, with inherited F7/F11 regressions. |
| Initial curve characteristic scope | Certified | `short-weierstrass-characteristic-p` | States nonzero two and three in the field operations. |
| PFIELD/F7/F11 finite-carrier cardinality | Certified | `pfield-elements`; `member-equal-of-pfield-fix-and-pfield-elements`; `pfield-cardinality-equals-modulus` | Cardinality is grounded by an exhaustive duplicate-free canonical enumeration. |
| Reusable bounded finite-bijection evidence | Certified | `finite-unrank-of-finite-rank`; `member-equal-of-finite-fix-and-finite-elements`; `finite-cardinality-equals-bound` | Field-free constructive carrier/cardinality theory with PFIELD and F7X2 proving instances. |
| Reusable finite-field coding context | Certified | `finite-field-unrank-of-finite-field-rank`; `finite-field-rank-of-finite-field-fix`; `finite-field-bound-greater-than-one` | Separate jointly constrained finite-field model with coherent bounded coding and PFIELD/F7 proving clients; no carrier or cardinality is exposed. |
| Finite-field polynomial core bridge | Certified | `finite-field-poly-normalize`; `finite-field-poly-coefficient-of-poly-normalize`; `finite-field-canonical-polynomial-p-of-poly-mul`; `finite-field-poly-degree-of-nil` | Ordinary renamed definitions and explicit GPOLY functional instances; coding operations are not polynomial premises. |
| Recursive divmod instance equation seam | Certified | `<core>-functional-instance-equation`; `finite-field-poly-divmod-definition-for-reduction-instantiation`; `finite-field-poly-divmod-core-reconstruction-invariant` | Stable recursive equation and public-wrapper equation support; finite-field divmod public semantics are proved by direct accumulator invariants. |
| Finite-field recursive divmod and projections | Certified | `finite-field-poly-divmod`; `finite-field-poly-quotient`; `finite-field-poly-remainder`; `finite-field-poly-divmod-reconstruction`; `finite-field-poly-divmod-final-remainder-degree-bound` | Direct recursive accumulator invariants certify canonicality, reconstruction, and final degree bound without coding operations. |
| Finite-field remainder/reduced representatives | Certified | `finite-field-poly-reduced-p`; `finite-field-poly-remainder-idempotent`; `finite-field-poly-reduced-p-iff-canonical-and-degree-bounded` | Public fixer/recognizer contract over the completed divmod projection, including normalization invariance, zero-modulus totalisation, lower-degree identity, strict length consequence, and reduced representative characterization. |
| Finite-field explicit-modulus reduced-ring staged prefix | Certified | `finite-field-poly-reduced-add`; `finite-field-poly-reduced-neg`; `finite-field-poly-reduced-sub`; `finite-field-poly-reduced-mul`; `finite-field-poly-reduced-one`; `finite-field-poly-reduced-add-commutative` | Transparent operation-then-remainder target interface with verified guards and definition equations. Only reduced-add commutativity is certified among the algebraic laws; finite-field remainder/add compatibility and reduced-add associativity remain the immediate open seam before the full reduced-ring instance. |
| Finite-field fixed-modulus coefficient representation | Certified | `finite-field-fixed-modulus-coefficient-vector`; `finite-field-fixed-modulus-reconstruct`; `finite-field-fixed-modulus-reconstruct-of-coefficient-vector`; `finite-field-fixed-modulus-coefficient-vector-of-reconstruct` | Transparent coefficient vectors over the finite-field remainder fixer. Width is one less than normalized modulus length for nonzero normalized moduli and zero for normalized-zero moduli; coefficient-vector rank/unrank is certified; carrier construction and cardinality are certified by `finite-field-fixed-modulus-elements` and `finite-field-fixed-modulus-cardinality`. |
| Generic finite-field representative-count cardinality | Certified | `finite-field-extension-representative-count-equals-radix-power`; `finite-field-extension-representative-count-equals-degree-power` | Counts exhaustive fixed-modulus representatives from the certified coding/carrier layer. This is not field packaging and requires no irreducibility. |
| F7X2 finite-carrier cardinality | Certified | `f7x2-unrank-of-f7x2-rank`; `member-equal-of-f7x2-fix-and-f7x2-elements`; `f7x2-cardinality-equals-49` | Presentation-specific mixed-radix bijection and exhaustive duplicate-free carrier. |
| Generic extension field cardinality | Open, deferred from immediate Hasse path | — | Requires a field-facing bridge from the existing irreducible quotient-field package to the explicit finite-field-prefixed representative carrier/cardinality layer. It may be needed by generic quotient-field Hasse instances, an ambient-field realization, or Schoof, but is not a premise of the first abstract Hasse statement. |
| Carrier-witness cardinality uniqueness | Open | — | Compare independent exhaustive duplicate-free witnesses only when a client requires it. |
| Prime-power metadata | Open | — | The characteristic/cardinality relationship remains separate. |
| Cardinality Frobenius | Open | — | Must use actual cardinality, not `field-frobenius-exponent`. |
| Characteristics two and three for curves | Deferred | — | Require separate curve models and downstream formula scopes. |

## 3. Dense polynomial arithmetic

| Boundary | Status | Public endpoint | Open dependency / detail |
|---|---|---|---|
| Canonical dense representation | Certified | `normalize`; `canonical-polynomial-p` | Constant-first coefficients; `nil` is canonical zero. |
| Coefficient projection and canonical extensionality | Certified | `poly-coefficient`; `canonical-polynomial-extensionality` | Total coefficientwise interface for canonical dense polynomials. |
| Arithmetic coefficient laws | Certified | `poly-coefficient-of-poly-add`; `poly-coefficient-of-poly-scale` | Exact unconditional addition and scaling coefficient semantics. |
| Multiplication convolution semantics | Certified | `poly-convolution-sum`; `poly-coefficient-of-poly-mul` | Finite convolution through the totalized requested index. |
| Derivative coefficient semantics | Certified | `poly-coefficient-of-poly-derivative` | Shifted natural scaling of the next input coefficient. |
| Ring arithmetic | Certified | `poly-add`; `poly-neg`; `poly-sub`; `poly-mul` | Public results are canonical representatives. |
| Evaluation and powers | Certified | `eval`; `poly-pow` | Evaluation and ring compatibility are certified. |
| Degree and leading coefficient | Certified | `poly-degree`; `poly-leading-coefficient` | Defined over normalized dense polynomials. |
| Formal derivative operation and additive laws | Certified | `poly-derivative`; `canonical-polynomial-p-of-poly-derivative`; `poly-derivative-of-poly-add`; `poly-derivative-of-poly-neg`; `poly-derivative-of-poly-sub` | Uses generic `field-nat-mul`; a characteristic-safe length upper bound is certified. |
| Derivative product rule | Certified | `poly-derivative-of-poly-mul` | Coefficientwise finite convolution and canonical extensionality. |
| Derivative power rule | Open | — | Requires a polynomial natural-scaling interface and induction on the exponent. |
| Derivative-coprime square-free predicate | Certified | `poly-square-free-p` | Total; represented zero is false and nonzero constants are true. |
| Supplied square-divisor obstruction | Certified | `poly-square-free-p-implies-not-poly-has-square-divisor-p` | Characteristic-independent explicit divisor relation. |
| Square-divisor/repeated-factor converse | Open | — | Requires irreducible-divisor existence and factor extraction or Euclid theory. |
| Root-based separability | Deferred | — | Requires extension-field roots and multiplicity. |
| Rational-function algebra | Open | — | Requires equality, cancellation, and degree theory. |
| Further HS/PFIELD bridges | Deferred | — | Add only when a downstream theorem requires them. |

## 4. Euclidean division, GCD, XGCD and modular inversion

| Boundary | Status | Public endpoint | Open dependency / detail |
|---|---|---|---|
| Division with remainder | Certified | `poly-divmod`; `poly-remainder` | Reconstruction and strict remainder-degree bounds hold for normalized nonzero divisors. |
| Congruence and reduced arithmetic | Certified | `poly-congruent-p`; `poly-reduced-p`; `poly-reduced-add`; `poly-reduced-mul` | Canonical modular representatives. |
| Euclidean and monic GCD | Certified | `poly-euclidean-gcd`; `poly-monic-euclidean-gcd` | Divisibility and canonicality endpoints are certified. |
| Extended Euclidean algorithms | Certified | `poly-extended-euclidean-gcd`; `poly-monic-extended-euclidean-gcd` | Bézout identities close the boundary. |
| Irreducibility and modular inverse | Certified | `poly-irreducible-p`; `poly-modular-inverse` | Nonzero modular inverse follows for irreducible modulus. |

## 5. Fixed-modulus quotient fields

| Boundary | Status | Public endpoint | Open dependency / detail |
|---|---|---|---|
| Generic irreducible quotient field | Certified | `fixed-modulus-field-fix`; `fixed-modulus-field-add`; `fixed-modulus-field-neg`; `fixed-modulus-field-mul`; `fixed-modulus-field-inv` | Canonical remainder representation with two-sided nonzero inverse law. |
| Generic fixed-modulus coefficient representation | Certified | `fixed-modulus-reconstruct-of-coefficient-vector`; `fixed-modulus-coefficient-vector-of-reconstruct`; `fixed-modulus-fix-coefficient-vector-extensionality` | Two-way correspondence between canonical quotient representatives and proper, exact-length fixed-entry vectors, including literal recovery of trailing zero slots. |
| Concrete F7X2 instance | Certified | F7X2 operations and fixed-modulus functional instance | Uses the irreducible modulus `x^2+1` over F7. |
| F7X2 public `GFIELD` packaging | Certified | `f7x2-mul-inverse-left`; `f7x2-field-add-left-cancel-regression`; `f7x2-field-div-mul-denominator-regression` | The unchanged concrete operations satisfy every nullary `GFIELD` constraint; downstream cancellation and division functional instances certify the complete substitution. |
| F7X2 seventh-power conjugation | Certified | `f7x2-seventh-power-is-conjugate`; `f7x2-seventh-power-repeated-multiplication` | Unconditional totalized `(a+bX)^7 = a-bX`, proved through public coefficient projections and a 49-case F7 scalar-pair endpoint; fixed-point characterization remains open. |
| Generic executable finite-field constructor | Deferred | — | The fixed-modulus logical constructor is the current reusable boundary. |

## 6. Curve representations and executable addition

| Boundary | Status | Public endpoint | Open dependency / detail |
|---|---|---|---|
| Short-Weierstrass equation and scope | Certified | `short-weierstrass-affine-point-p`; `short-weierstrass-characteristic-p` | Initial model assumes the maintained nonzero discriminant and characteristic scope. |
| Canonical affine coordinates | Certified | `affine-coordinates-fix`; `affine-coordinates-p`; `short-weierstrass-affine-point-p` | Structural representation remains separate from curve membership. |
| Tagged points and infinity | Certified | `curve-point-fix`; `curve-point-representation-p`; `short-weierstrass-curve-point-p`; `curve-point-infinity` | Malformed tagged inputs fix to infinity. |
| Point negation | Certified | `curve-point-neg`; `curve-point-neg-of-neg` | Closure and canonical-input involution are certified. |
| Total affine classification | Certified | `affine-pair-classify` | Valid affine pairs cannot reach the `:same-x-other` fallback. |
| Executable affine addition | Certified | `affine-pair-output-point` | Branch closure is certified. |
| Executable tagged addition | Certified | `curve-point-pair-output-point`; `short-weierstrass-curve-point-p-of-curve-point-pair-output-point` | Total canonical output for tagged points. |
| Alternative small-characteristic curves | Deferred | — | Require models appropriate to characteristics two and three. |

## 7. Independent semantic addition relation

| Boundary | Status | Public endpoint | Open dependency / detail |
|---|---|---|---|
| Division-free affine branch semantics | Certified | `affine-distinct-x-secant-relation-p`; `affine-doubling-relation-p`; `affine-opposite-y-infinity-relation-p` | Independent of executable classifier priority. |
| Full tagged addition semantics | Certified | `curve-point-addition-relation-p` | Covers affine branches and ordered infinity cases. |
| Executable soundness | Certified | `curve-point-pair-output-point-satisfies-addition-relation` | Connects the dispatcher output to the independent relation. |
| Semantic output determinacy | Certified | `curve-point-addition-relation-output-determinate-under-fixed-operands` | Identifies witnesses modulo point fixing. |
| Semantic commutativity | Certified | `curve-point-addition-relation-p-commutative` | Operand reversal preserves the relation. |
| Field-only associativity certificates | Certified | `xcert-composition`; `xcert-untagged-outputs-equal` | Detailed decompositions remain in the [associativity audits](audits/associativity-assembly.md). |

## 8. Associativity

The [associativity status matrix](status-associativity.md) owns family-level
coverage; the ledger records only the three public completion boundaries.

| Boundary | Status | Public endpoint | Open dependency / detail |
|---|---|---|---|
| Affine semantic associativity | Certified | `curve-point-addition-relation-associative-for-affine-inputs` | Complete D/O/T assembly under `short-weierstrass-characteristic-p`. |
| Full tagged semantic associativity | Certified | `curve-point-addition-relation-associative` | Includes original infinity and affine representation reduction. |
| Executable associativity | Certified | `curve-point-pair-output-point-associative`; `curve-point-pair-output-point-associative-fixed` | Semantic-to-executable lift uses soundness, closure, determinacy, and canonical output. |

Detailed family assembly, certificate orientations, historical alternatives,
and finite validation live in the
[assembly audit](audits/associativity-assembly.md) and
[mixed D/T certificate audit](audits/mixed-dt-certificate.md).

## 9. Executable abelian-group laws

| Boundary | Status | Public endpoint | Open dependency / detail |
|---|---|---|---|
| Closure and identity | Certified | `short-weierstrass-curve-point-p-of-curve-point-pair-output-point`; `curve-point-pair-output-point-identity-left`; `curve-point-pair-output-point-identity-right` | Valid tagged points under the curve context. |
| Commutativity and associativity | Certified | `curve-point-pair-output-point-commutative`; `curve-point-pair-output-point-associative` | Literal equality follows from canonical output. |
| Inverse laws | Certified | `curve-point-pair-output-point-with-negate-left`; `curve-point-pair-output-point-with-negate-right` | Uses transparent `curve-point-neg`. |
| Cancellation | Certified | `curve-point-pair-output-point-cancel-left`; `curve-point-pair-output-point-cancel-right` | Algebraic consequences of the public executable laws. |
| Fixing and canonical output | Certified | `curve-point-fix-of-neg`; `curve-point-neg-of-fix`; `curve-point-fix-of-curve-point-pair-output-point`; `curve-point-pair-output-point-of-fixes` | Exact contracts are in [execution boundaries](execution-boundaries.md#curve-addition-correspondence). |

## 10. Contextual abelian-group packaging

| Boundary | Status | Public endpoint | Open dependency / detail |
|---|---|---|---|
| Generic contextual abelian group | Certified | `abelian-group-element-p`; `abelian-group-op`; `abelian-group-identity`; `abelian-group-inverse`; `abelian-group-context-p` | Carrier-based interface with ordinary ACL2 equality. |
| Curve-point abelian-group instance | Certified | `def-curve-point-abelian-group-theorem` | Context is `short-weierstrass-characteristic-p`. |

The stable interface choice and functional-instantiation architecture are
described in [architecture](architecture.md#contextual-abelian-group-and-scalar-architecture).

## 11. Natural scalar multiplication

| Boundary | Status | Public endpoint | Open dependency / detail |
|---|---|---|---|
| Generic natural repeated addition | Certified | `abelian-group-nat-mul` | `nfix`-totalised linear reference specification. |
| Generic closure and laws | Certified | `abelian-group-element-p-of-nat-mul`; `abelian-group-nat-mul-one`; `abelian-group-nat-mul-of-sum`; `abelian-group-nat-mul-distributes-over-op`; `abelian-group-nat-mul-of-nat-mul` | Includes nested scalar composition. |
| Curve natural scalar operation | Certified | `curve-point-nat-mul`; `def-curve-point-natural-scalar-theorem`; `curve-point-nat-mul-of-nat-mul` | Functional instance of the contextual abelian-group theory, including nested scalar composition. |
| Fast natural scalar implementation | Open | — | Separate double-and-add function with correspondence to `curve-point-nat-mul`. |
| Signed scalar multiplication | Deferred | — | Build after the natural theory. |

Totalisation, recursion orientation, guard assurance, and the future optimized
boundary are maintained in
[execution boundaries](execution-boundaries.md#natural-scalar-multiplication).

## 12. Hasse-theorem track

| Boundary | Status | Public endpoint | Open dependency / detail |
|---|---|---|---|
| Primary Hasse route | Selected; not implemented | [Hasse source and dependency audit](audits/hasse-source-and-dependency.md) | Silverman V.1.1 is the selected Frobenius/positive-quadratic-degree route, using III.6 (especially III.6.3) and the required III.4--III.5 isogeny results. |
| Ambient/base-field/Frobenius design | Experimented; no-go for curve slice | [bounded feasibility experiment](audits/hasse-source-and-dependency.md#post-pr-309-bounded-feasibility-experiment-2026-08-08) | F7/F7X2 representations support the intended executable constant embedding and nonidentity conjugation, and a certified seventh-power coefficient bridge; the fixed-point converse and functional instance remain absent. No representation is adopted. |
| Function-field or morphism degree theory | Open; representation undecided | — | A purpose-built layer may suffice. Pointwise equality on `E(F_q)` cannot support degree; broad rational-function or isogeny infrastructure is not yet authorized. |
| Frobenius/dual relationships and degree inequality | Open | — | Requires curve closure from ambient Frobenius homomorphism laws, fixed-point/kernel identification, separability and degree facts, and the positive quadratic degree form. |
| Squared Hasse bound | Open | — | Preferred first endpoint is `(q + 1 - N)^2 <= 4q`; derive the square-root form separately. |

## 13. Schoof-algorithm track

| Boundary | Status | Public endpoint | Open dependency / detail |
|---|---|---|---|
| Division polynomials | Open | — | Requires polynomial derivatives and the selected curve formulas. |
| Quotient-coordinate arithmetic | Open | — | Build on canonical polynomial and modular arithmetic. |
| Frobenius action and trace tests | Open | — | Requires finite-field metadata and quotient-coordinate semantics. |
| Bounded CRT reconstruction | Open | — | Specify and certify the point-count reconstruction bound. |
| Schoof point-count correctness | Open | — | Compose trace congruences with CRT reconstruction. |
| Executable Schoof algorithm | Open | — | Each optimized boundary requires specification, correspondence, guards, and execution evidence. |
| Performance optimization and benchmarking | Deferred | — | Performance evidence remains separate from logical correctness. |

- Finite-field monomial/scalar-division support — Certified (`finite-field-poly-monomial`, `finite-field-poly-degree-of-monomial`, `finite-field-div-nonzero`, `finite-field-div-mul-denominator`).
- Finite-field division-step substrate — Certified (`finite-field-poly-division-step-core-reconstruction`, `finite-field-poly-division-step-core-degree-decreases`, `finite-field-poly-division-step-core-length-decreases`).
- Finite-field recursive divmod and projections — Certified (`finite-field-poly-divmod-reconstruction`, `finite-field-poly-remainder-degree-bound`).

## Finite-field division-step substrate

The finite-field-prefixed one-step polynomial division substrate is certified.
It uses transparent generated definitions for the core step and public term/next
projections, with verified guards, reconstruction, strict degree decrease, and a
strict core length theorem suitable for the future recursive divmod measure.  The
decisive cancellation proof is length/leading-coefficient based, not
coefficient-vector or coding based.  Recursive finite-field divmod and public quotient/remainder APIs are certified; fixed-modulus representations and coding/cardinality operations remain open and are not introduced here.
