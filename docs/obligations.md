# Proof obligation ledger

The cross-cutting inventory and dependency analysis for the final executable
target is maintained in the
[arbitrary-field executable architecture audit](audits/arbitrary-field-executable-schoof-architecture.md).
It records distinct open seams: (1) a reduced-ring descriptor representation
kernel with structural checking, fixing, operations, coding, and `p^m` count;
(2) inverse and field laws under a separate logical validity predicate, plus
fixed-context functional instantiation; (3) a runtime short-curve bridge; (4) a
runtime-`ell` trace program with exhaustive exceptional branches; and (5) the
general cardinality-Frobenius/torsion-to-trace bridge followed by CRT/Hasse
composition.  None is certified at this baseline.  Logical field validity
includes primality, positive extension degree, correct modulus degree, and
irreducibility; no executable validator is currently claimed.  Existing F7,
F11, and F7X2 results are clients or regressions and do not discharge those
general obligations.

An implementation pass after PR #361 exposed an additional prerequisite to
item (1).  It is now split in two.  The modular coefficient, unreduced
polynomial representation/arithmetic, and radix-coding core is **certified** by
`runtime-p-representation.lisp`, including fixed-PFIELD normalization and
multiplication correspondence.  Runtime-`p` monic reduction and fixed-`p`
remainder correspondence remain **open** and precede the descriptor kernel.
Neither boundary assumes primality or irreducibility or checks field validity.
The detailed finding is recorded in the
[architecture audit](audits/arbitrary-field-executable-schoof-architecture.md#post-pr-361-implementation-finding-runtime-coefficient-seam).

| Runtime-`p` modular polynomial representation and radix coding | Certified | `runtime-p-effective-modulus`; coefficient operations; `runtime-p-normalize`; polynomial arithmetic; `runtime-p-{coding-bound,rank,unrank}`; fixed-PFIELD normalization/multiplication correspondence; radix round trips | Malformed or integer `< 2` moduli execute at effective modulus 2. The original input remains available and this is not descriptor validity. Polynomials are unreduced ascending coefficient lists; monic reduction remains open. |

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
| Finite-field explicit-modulus reduced-ring staged prefix | Certified through reduced-add associativity and reduced-mul commutativity | `finite-field-poly-reduced-add`; `finite-field-poly-reduced-neg`; `finite-field-poly-reduced-sub`; `finite-field-poly-reduced-mul`; `finite-field-poly-reduced-one`; `finite-field-poly-reduced-add-commutative`; `finite-field-poly-reduced-mul-commutative`; `finite-field-bounded-remainders-in-same-coset-are-equal`; `finite-field-poly-remainder-of-poly-add-divisor-multiple`; `finite-field-poly-remainder-of-poly-add-remainder-left`; `finite-field-poly-remainder-of-poly-add-remainder-right`; `finite-field-poly-reduced-add-associative` | Transparent operation-then-remainder target interface with verified guards and definition equations. The certified direct algebraic chain covers multiplication by negation, reconstruction differences, and bounded same-coset uniqueness; divisor-multiple invariance and both remainder/add orientations are unconditional, including malformed values and zero-normalizing moduli. Reduced multiplication commutativity is the narrow additional law used to orient modular-inverse correctness; this is not the complete reduced-ring or field package. |
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
| F7X2 base embedding and Frobenius witness | Certified concrete witness | `f7x2-embed-f7`; `f7x2-conjugate-fixed-iff-embedded-image`; `f7x2-conjugate-add`; `f7x2-conjugate-mul` | The natural F7 embedding, coefficient conjugation homomorphism, nonidentity witness, and arbitrary-input fixed-subfield/image characterization are certified.  Seven-case scalar exhaustion proves the universal fixed-point endpoint; exhaustive 49-element agreement and the exact seven-element fixed set are regression evidence.  The experimental context-guarded two-field seam and its F7/F7X2 functional instance are certified; no ambient architecture is adopted. |
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
| Primary Hasse route | Selected; not implemented | [Hasse source and dependency audit](audits/hasse-source-and-dependency.md) | Silverman V.1.1 is the selected Frobenius/positive-quadratic-degree route, using III.6 (especially III.6.3) and the required III.4--III.6 isogeny/dual-isogeny results. |
| Ambient/base-field/Frobenius design | Architecture selected; realization open | [ambient/degree audit](audits/ambient-domain-and-degree-representation.md) | Use a separate point-level seam for Frobenius fixedness and the `ker(1-pi)`/degree bridge; its exact carrier is open.  A directed root-sufficient family is sufficient for a general kernel theorem but is not mandated by this particular kernel.  F7/F49 remains scalar feasibility evidence, not a uniform universe for arbitrary kernels. |
| Rank-two symbolic endomorphism/degree theory | Open; architecture selected | [ambient/degree audit](audits/ambient-domain-and-degree-representation.md) | Use canonical rank-two short-Weierstrass function-field semantics for morphism equality and degree, with an abstract consumer permitted only as an intermediate theorem.  A concrete functional instance is required before public Hasse. |
| Frobenius/kernel/degree realization | Open; major construction | — | Requires `deg(pi)=q`, separability of `1-pi`, the fixed-kernel/base-point correspondence, a certified `#ker(1-pi)=deg_sep(1-pi)` bridge, and quadraticity.  The weakest point carrier for that bridge is open.  General geometric kernels and dual isogenies are needed only if the chosen III.6.3 realization uses them; a direct certified `Z`-span theorem may avoid them. |
| Squared Hasse bound | Open | — | Preferred first endpoint is `(q + 1 - N)^2 <= 4q`; derive the square-root form separately. |

## 13. Schoof-algorithm track

### Joint F11 finite-field instance seam

The joint F11 context is consumable through the named projections in
`f11-finite-field-context-instance-theory` and delayed constraint hints.
`f11-fix` supplies fixer, rank, and unrank, and 11 supplies the bound.  This
single context certifies bounded polynomial and division-polynomial functional
instances; no second constrained family is currently required.

| Boundary | Status | Public endpoint | Open dependency / detail |
|---|---|---|---|
| Generic division-polynomial base | Certified | `finite-field-division-polynomial-base-spec`; `finite-field-division-polynomial-base`; correctness, indices 0--4, unsupported/malformed totalization, closure, and fixing theorems | Dense ascending univariate polynomials; even indices store `psi_n/(2y)`. |
| Generic division-polynomial recurrence | Certified | `finite-field-division-polynomial-c`; `finite-field-division-polynomial-recurrence-step`; exact base, both odd branches, even branch, closure, and fixing theorems | Transparent one-step operation over an ascending table. |
| Generic division-polynomial table | Certified | `finite-field-division-polynomial-table-extend`; `finite-field-division-polynomial-table`; length, lookup, entry, closure, and fixing invariants | Each recurrence result is constructed once; list extension still traverses the prefix. |
| Generic division-polynomial sequence/evaluator | Certified | `finite-field-division-polynomial-sequence-p`; generated-table satisfaction; entrywise uniqueness; `finite-field-division-polynomial`; final-entry, fixing, closure, base, and recurrence theorems | This is the complete generic table/sequence/all-index correspondence, not an F11 transport or classical bivariate semantics theorem. |
| Generic finite-field `psi_3` evaluator bridge | Certified | `finite-field-natural-scalar-is-natural-coefficient-times`; `finite-field-third-division-polynomial-{dense,normalized-dense}-eval-is-expanded-expression`; `finite-field-division-polynomial-index-3-correspondence`; `finite-field-division-polynomial-index-3-eval-is-expanded-expression` | Unconditional total transport for arbitrary ACL2 inputs and arbitrary characteristic. The F11 specialization is certified separately. |
| F11 `psi_3` coefficient and evaluator specialization | Certified | `f11-natural-scalar-is-natural-coefficient-times`; `f11-third-division-polynomial-normalized-dense-eval-is-expanded-expression`; `f11-division-polynomial-index-3-correspondence`; `f11-division-polynomial-index-3-eval-is-expanded-expression`; `f11-golden-division-polynomial-index-3`; `f11-golden-literal-division-polynomial-index-3-eval` | The generic normalized dense-evaluation interface is functionally transported through the jointly constrained F11 instance. The maintained evaluator has exact golden coefficients `(10 6 6 0 3)`, and both its maintained and literal polynomial forms evaluate to the total fixed F11 expanded expression for arbitrary ACL2 `x`. The transparent total F11 ambient Horner evaluator and base-polynomial embedding are certified together with `f11-quotient-coordinate-eval-at-universal-x`, `f11-quotient-coordinate-modulus-eval-at-universal-x`, `f11-golden-psi3-eval-at-universal-x`, and `f11-golden-literal-psi3-eval-at-universal-x`.  These are universal coordinate-ring evaluation and vanishing facts only; interpretation in a field or algebraic closure and classical `E[3]` point semantics remain open. |
| Bounded F11 base and recurrence transport | Certified | `f11-division-polynomial-base-*-from-finite-field-instance`; `f11-division-polynomial-operation-interface`; `f11-division-polynomial-recurrence-step-from-finite-field-instance` | Every retained base theorem (indices 0--4, unsupported indices, index fixing, and coefficient fixing) and the complete recurrence case split is an explicit functional instance through the joint F11 seam. |
| F11 generated table, sequence, and all-index evaluator correspondence | Certified | `f11-division-polynomial-*-definition-correspondence`; structural table interface through stable lookup and newest entry; evaluator lookup/base/recurrence equations; `f11-division-polynomial-table-satisfies-sequence-p`; entrywise and final-entry uniqueness; `f11-division-polynomial-all-index-semantic-correspondence` | The bounded base and recurrence are explicit functional instances. The recursive table and relational sequence results are direct F11 transports of the generic induction architecture. This is stored-sequence semantics, not the classical bivariate bridge. |
| Classical bivariate division-polynomial semantics | Open | — | Connect the separated-`2y` univariate representation to classical bivariate division polynomials in its characteristic scope. |
| Quotient-coordinate commutative ring | Certified, with executable F11 specialization | `quotient-coordinate`; `f11-quotient-coordinate`; their projections, fixers, zero, one, distinguished `x` and `y`, addition, negation, subtraction, multiplication, unconditional left/right zero-annihilation laws, and powers | Both use the literal transparent rank-two `u+yv` pair representation; the F11 operations substitute the production `f11-poly-remainder` and reduced operations. The specialization expansion is unconditional on arbitrary ACL2 inputs and moduli. No irreducibility, inverse, cancellation, domain, or no-zero-divisor premise is introduced. |
| Quotient-coordinate natural power | Certified | `quotient-coordinate-pow-spec`; `quotient-coordinate-pow`; closure, fixing, `nfix`, zero, one, successor, exponent-addition, power-of-power, power-of-product, zero/one-base, embedded-polynomial, and distinguished-`y` even/odd laws | Transparent linear repeated multiplication, totalized by fixing the base and applying `nfix`; `0^0=1`.  The theory uses only the quotient-coordinate commutative ring and introduces no inverse, cancellation, domain, or optimized executable branch. |
| Quotient-coordinate characteristic annihilation | Certified | `quotient-coordinate-nat-mul`; fixing, `nfix`, zero, successor, closure, zero-scaling, natural-scalar sum, composition, and addition-distribution laws; `quotient-coordinate-nat-mul-is-unit-times`; `quotient-coordinate-nat-mul-of-one-is-embedded-field-nat-mul`; `quotient-coordinate-nat-mul-of-characteristic`; `quotient-coordinate-nat-mul-eleven-of-characteristic` | Transparent natural repeated addition transports the generic field characteristic through the canonical constant-polynomial embedding. The fixed eleventh-power binomial expansion and characteristic-11 additive Frobenius are certified by `quotient-coordinate-pow-eleven-of-add-expanded`, `quotient-coordinate-nat-mul-of-eleven-multiple`, and `quotient-coordinate-pow-eleven-of-add`. The complete F11 Frobenius ring-homomorphism interface, trace-predicate semantics, any required classical `E[3]` interpretation, other torsion primes, CRT/Hasse reconstruction, and final Schoof correctness remain open. |
| Cardinality-indexed quotient-coordinate power action | Certified multiplicative/iteration interface and q=11 additive law | `quotient-coordinate-frobenius`; `quotient-coordinate-frobenius-iterate`; zero, one, product, embedding, exact exponent, zero/one/successor iteration, and iteration-composition laws; `quotient-coordinate-frobenius-eleven-of-add` | The supplied `q` is totalized by `nfix`. Multiplication preservation is characteristic-independent; addition preservation is certified only for exponent exactly 11 under `field-characteristic-p(11)`. Generic characteristic-p and prime-power Frobenius portability remain open. |
| Quotient-coordinate semantic evaluation | Certified in the existing single-field interface | `eval-of-poly-remainder-at-root`; `quotient-coordinate-semantic-eval`; fixing, zero, one, distinguished `x`/`y`, addition, negation, subtraction, multiplication, natural-power, q-power, and iterated-q-power preservation theorems | Remainder evaluation needs only that the modulus vanish at the supplied coordinate and retains total malformed-input and normalized-zero-modulus semantics. Multiplication and powers additionally assume the supplied coordinates satisfy the short-Weierstrass equation for the supplied `a,b`. The q-power corollaries retain the existing `nfix` and exponent semantics. These theorems do not assert that the base field contains all of `E[3]`; their conditional base-to-ambient transport is certified separately. |
| Denominator-free quotient-coordinate trace predicate | Certified algebraic predicate; affine/group equivalence open | `quotient-coordinate-cross-add-p`; `quotient-coordinate-cross-opposite-p`; `quotient-coordinate-trace-candidate-p`; Boolean, `nfix`, malformed-trace, and exact-definition contracts | The secant predicate checks `D^2(x1+x2+x3)=N^2` and `D(y1+y3)=N(x1-x3)` with `D=x2-x1`, `N=y2-y1`; residue zero uses fixed equal x and opposite y.  These equations are meaningful with zero divisors but are not equivalent to affine addition without invertibility of `D`, and the opposite predicate is only a narrow infinity spelling rather than a projective point representation. |
| Quotient-coordinate trace semantic soundness | Certified one-way, single-field interpretation and composition boundary | `quotient-coordinate-field-cross-add-p`; `quotient-coordinate-field-cross-opposite-p`; `quotient-coordinate-cross-add-p-semantic-soundness`; `quotient-coordinate-cross-opposite-p-semantic-soundness`; `quotient-coordinate-field-trace-candidate-p`; `quotient-coordinate-trace-candidate-p-semantic-soundness`; `quotient-coordinate-field-cross-add-implies-affine-secant-relation`; `quotient-coordinate-field-cross-add-implies-curve-point-addition`; `quotient-coordinate-field-cross-opposite-implies-affine-opposite-relation`; `quotient-coordinate-field-cross-opposite-implies-curve-point-addition`; `quotient-coordinate-cross-add-implies-curve-point-addition`; `quotient-coordinate-cross-opposite-implies-curve-point-addition` | At a modulus root, and additionally on the supplied semantic curve for multiplication-dependent cross-add evaluation, acceptance implies the identical field-level cross equations under the established total evaluation. Valid evaluated affine points and explicit nonzero `D=x2-x1` compose cross-add acceptance into the existing full curve-point addition relation; valid opposite operands compose directly into that relation with the existing infinity constructor, without a semantic curve premise. These are conditional one-way results: no converse, completeness, derived denominator nonzeroness, irreducibility, canonicality, or domain property is claimed. Trace-branch group wrappers, a concrete F11 ambient-field realization, classical `E[3]` interpretation and completeness, torsion existence, Frobenius trace identification, and actual trace-congruence correctness remain open. Conditional base-to-ambient equation transport is certified separately over an assumed commutative ring and supplies no field/group instance. |
| Base-to-ambient quotient-coordinate trace soundness | Certified conditional transport boundary | `ambient-eval-of-poly-remainder-at-root`; `quotient-coordinate-ambient-eval-of-mul`; `quotient-coordinate-ambient-eval-of-pow`; `quotient-coordinate-ambient-eval-of-frobenius`; `quotient-coordinate-ambient-eval-of-frobenius-iterate`; `quotient-coordinate-cross-add-p-ambient-soundness`; `quotient-coordinate-cross-opposite-p-ambient-soundness`; `quotient-coordinate-trace-candidate-p-ambient-soundness` | If a supplied ambient coordinate is a root of the embedded modulus and the supplied ambient point satisfies the embedded curve equation, base quotient-predicate acceptance implies the identically oriented ambient cross equations. The opposite theorem needs only the root premise. No converse, cancellation, torsion existence, E[3] completeness, algebraic closure, or trace-congruence correctness is claimed. A direct F7/F7X2 functional instance remains deferred because the current concrete instance generators package an entire generic polynomial stack; exposing a narrow operation-preservation bundle without duplicating that stack is the exact missing instantiation seam. |
| Executable F11 polynomial reduction instance | Certified production specialization | `f11-poly-division-step-core`; `f11-poly-divmod`; `f11-poly-quotient`; `f11-poly-remainder`; normalization invariance, idempotence, self-reduction, and addition/multiplication remainder homomorphism laws; `f11-poly-reduced-add`; `f11-poly-reduced-neg`; `f11-poly-reduced-sub`; `f11-poly-reduced-mul`; `f11-poly-reduced-one` | Uses the production generated division-step/divmod templates with the certified F11 coefficient operations. The termination decrease is a functional instance of the finite-field-prefixed theorem. Guards are verified, total malformed/zero-divisor behavior is executable, and the exact modulus `(10 6 6 0 3)` plus focused `psi_3` reductions are certified. The old quotient-coordinate witness now calls this remainder instead of maintaining an independent recursive divider. |
| Finite-field Euclidean divisibility interface | Certified reusable prefix | `finite-field-poly-divides-p`; `finite-field-poly-common-divisor-p`; normalization/fixing, zero, self, and exact-multiple laws; `finite-field-poly-remainder-with-euclidean-remainder-when-divides-second`; `finite-field-poly-divides-p-euclidean-remainder-iff`; `finite-field-poly-divides-p-euclidean-step-iff` | Uses the existing finite-field representation and public divmod/reduction reconstruction and remainder laws. The Euclidean step is unconditional beyond its explicit divisibility premise and retains total malformed, dotted-tail, trailing-zero, and zero-divisor semantics. Raw GCD correctness is certified in the next boundary; monic GCD, XGCD, F11 transport, irreducibility, modular inverse, and the root field remain open. |
| Finite-field raw Euclidean GCD | Certified reusable boundary | `finite-field-poly-euclidean-gcd`; normalized-zero and recursive equations; canonicality and normalization invariance; `finite-field-poly-euclidean-gcd-divides-{both,first,second}`; `finite-field-poly-common-divisor-divides-euclidean-gcd`; `finite-field-poly-common-divisor-p-{of-euclidean-gcd,greatestness}`; `finite-field-poly-euclidean-gcd-raw-correct` | The total guard-verified recursion uses the certified strict canonical-remainder length decrease. Its raw result divides both inputs and is divisible by every common divisor, including for malformed, dotted-tail, trailing-zero, and normalized-zero representations. Monic normalization and monic GCD correctness are certified in the next boundary; finite-field XGCD/Bézout, F11 transport, irreducibility, modular inverse, the fixed-modulus field, and the concrete `psi_3` root field remain open. |
| Finite-field monic Euclidean GCD | Certified reusable boundary | `finite-field-poly-monic-normalize`; `finite-field-poly-divides-p-of-poly-monic-normalize-{dividend,divisor}`; `finite-field-poly-monic-euclidean-gcd`; structural, monicity, divisibility, greatestness, and `finite-field-poly-monic-euclidean-gcd-correct` endpoints | The certified raw GCD is monic-normalized by a transparent total guard-verified scaling operation. Canonicality, normalization and zero/nonzero shape are preserved for malformed, dotted-tail, fixed-coefficient, trailing-zero, and zero representations; nonzero results have leading coefficient finite-field one. Raw XGCD/Bézout is certified in the next boundary; monic XGCD, F11 transport, irreducibility, modular inverse, the fixed-modulus field, and the concrete `psi_3` root field remain open. |
| Finite-field raw extended Euclidean GCD | Certified reusable boundary | `finite-field-poly-extended-euclidean-gcd`; normalized-zero and recursive equations; canonicality and normalizedness of all projections; `finite-field-poly-extended-euclidean-gcd-gcd-is-euclidean-gcd`; `finite-field-poly-extended-euclidean-gcd-bezout`; `finite-field-poly-extended-euclidean-gcd-bezout-with-euclidean-gcd`; `finite-field-poly-extended-euclidean-gcd-raw-specification` | The transparent total guard-verified recursion calls production `finite-field-poly-divmod` once per step and follows the raw-GCD remainder chain. Its unconditional Bézout identity covers malformed, dotted-tail, fixed-coefficient, trailing-zero, exact-divisibility, and normalized-zero representations. Monic scaling of the triple, monic Bézout, coefficient reduction for modular inversion, modular inverse, and concrete F11 transport remain open. |
| Finite-field monic extended Euclidean GCD | Certified reusable boundary | `finite-field-poly-monic-extended-euclidean-gcd`; `finite-field-poly-monic-extended-euclidean-gcd-is-scaled-xgcd`; monic-GCD projection, canonicality, normalizedness, leading-coefficient, unconditional Bézout, when-one, and `finite-field-poly-monic-extended-euclidean-gcd-specification` endpoints | Transparent guard-verified post-processing calls the certified raw XGCD once and scales both coefficients by the single inverse-leading-coefficient scalar. The zero raw GCD totalizes to exactly `(mv nil nil nil)`. Coefficient reduction and concrete production-F11 transport are certified separately; irreducibility, the fixed-modulus field, the concrete `psi_3` root field, and torsion work remain open. |
| Finite-field monic-XGCD coefficient reduction | Certified reusable boundary | `finite-field-poly-monic-extended-euclidean-gcd-first-coefficient-reduction`; `finite-field-poly-remainder-of-polynomial-one-when-positive-degree`; `finite-field-poly-monic-extended-euclidean-gcd-first-coefficient-remainder-one` | Directly composes the certified monic Bézout-when-one identity with the unconditional divisor-multiple remainder law. The total endpoint retains the canonical remainder of one for constant, zero, malformed, dotted-tail, and trailing-zero moduli; only the positive-degree corollary specializes it to literal polynomial one. Finite-field modular inversion and production-F11 transport are certified in distinct boundaries; quartic irreducibility, fixed-modulus field construction, the concrete `psi_3` root field, and later torsion work remain open. |
| Finite-field modular inverse candidate | Certified reusable conditional boundary | `finite-field-poly-modular-inverse`; its definition, canonicality, normalization, multiplication bridge, total correctness, left/right reduced-multiplication inverse, positive-degree literal-one, and aggregate specification theorems | The transparent total guard-verified operation calls monic XGCD once and reduces projection 1 once. Under monic GCD one, its product with the first input reduces to reduced one on either side for every modulus, including zero, malformed, and constant moduli; only the positive-degree corollary returns literal polynomial one. This does not establish irreducibility or inverses for arbitrary nonzero residue classes. The production-F11 instantiation/transport is certified separately. General Schoof quotient-ring computation does not require an irreducible division polynomial; any scalable executable irreducibility client requires a separate audit. |
| Generic and finite-field factor-degree bound | Certified logical boundary | `poly-has-bounded-monic-factor-p`; `poly-reducible-normalized-positive-degree-implies-bounded-monic-factor`; `poly-normalized-positive-degree-without-bounded-monic-factor-is-irreducible`; finite-field-prefixed counterparts | Monic normalization preserves degree for nonzero polynomials. A reducible normalized positive-degree polynomial has a monic divisor of positive degree at most `floor(degree/2)`; absence of such a divisor implies logical irreducibility. These predicates and theorems are not executable factor searches or irreducibility tests. |
| Concrete F11 `psi_3` root field | Open; specialised route only | [trace-congruence route audit](audits/schoof-trace-congruence-routes.md#post-pr-350-concrete-f11-realization-check) | The modulus `(10 6 6 0 3)` and normalization `(7 2 2 0 1)` remain concrete test data, but irreducibility is not certified. Exhaustive F11 factor enumeration is not selected as the general production route, and irreducibility of division polynomials is not required by general Schoof quotient-ring computation. A scalable executable irreducibility criterion would require a separate audit; Rabin-style Frobenius/GCD testing is only a candidate. No quotient field, root, ordinate extension, torsion result, or trace-congruence theorem is established here. |
| Generic curve-level `psi_3` bridge | Certified | `short-weierstrass-psi3`; `short-weierstrass-psi3-on-curve`; `short-weierstrass-psi3-tangent-factorization`; `short-weierstrass-psi3-root-iff-doubled-x`; `short-weierstrass-psi3-root-iff-nat-mul-three-is-infinity`; `third-division-polynomial-expanded-expression`; `third-division-polynomial-expression-is-expanded-expression`; `short-weierstrass-psi3-is-expanded-expression`; `third-division-polynomial-gpoly-eval-is-expanded-expression`; `third-division-polynomial-normalized-gpoly-eval-is-expanded-expression` | For every valid affine point in the generic field context under `short-weierstrass-characteristic-p`, the classical expression `3*x^4 + 6*A*x^2 + 12*B*x - A^2` vanishes exactly when `[3]P` is infinity. The exceptional self-inverse ordinate is excluded from roots using the nonzero discriminant, and infinity is outside the affine constructor. The unconditional total-GFIELD expansion and GPOLY evaluation of the ascending dense coefficient list `(-A^2, 12B, 6A, 0, 3)`, including evaluation after normalization, are certified for arbitrary ACL2 inputs and characteristics. The finite-field transport, maintained index-3 evaluator correspondence, and F11 `(10 6 6 0 3)` specialization are certified separately. Quotient-coordinate evaluation at classical torsion points, trace-congruence correctness, other torsion primes, and CRT remain open. |
| First F11 `psi_3` trace test | Certified algebraic cross-product calculation and program instance | `quotient-coordinate-trace-program-definition`; production and F11 functional instances; `f11-psi3-trace-candidate-p`; residue and exact-value theorems | The operation-parametric trace-program contract is functionally instantiated both by the generic production API and by the executable F11 API; this transfers only the trace client’s program structure, not the complete reduced-ring law suite. For `psi_3=(10 6 6 0 3)`, residues 0 and 1 are false and residue 2 is true, with nonzero `D`, `N`, and cross-products. The coefficient/evaluation specialization and characteristic-11 addition preservation are certified separately. Classical ambient-field and affine interpretation, affine/group equivalence, and the trace-congruence theorem remain open. |
| Bounded CRT reconstruction | Open | — | Specify and certify the point-count reconstruction bound. |
| Schoof point-count correctness and executable composition | Open | — | Compose trace congruences with CRT and certify each logical/executable boundary. |
| Performance optimization and benchmarking | Deferred | — | Performance evidence remains separate from logical correctness. |
