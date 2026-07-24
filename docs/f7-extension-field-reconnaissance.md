# F7 polynomial GCD to extension-field reconnaissance

## Audit snapshot and scope

This is an architecture audit, not an implementation claim.  The authoritative
snapshot was commit `9c8593a43d3335b6d4a11b83d9dd126f655ee412` on branch
`work`, with an initially clean working tree.  The requested predecessor
`52692360ad8d99824f025813465cbbb328cd110f` is not present in the local object
database, so this audit follows the current tree.  The repository pins ACL2
8.6 (`ACL2_VERSION`), and the installed saved image reports SBCL
2.2.9.debian.  The `acl2` command is not on `PATH`; certification uses
`.deps/acl2-8.6/saved_acl2` through the project scripts.

No ACL2 event changes in this PR.  In particular, nothing below certifies F7
XGCD, irreducibility, a quotient ring, or an extension field.

## Current inventory

The generic inventory is materially ahead of the concrete F7 inventory.  This
is important: XGCD is absent only at the *named concrete F7 runtime* boundary,
not from the repository as a whole.

| Concern | Generic certified inventory | Concrete F7 certified inventory | Gap |
| --- | --- | --- | --- |
| Quotient and remainder | `poly-divmod-core`, `poly-divmod`, and `poly-remainder`; canonical quotient/remainder, reconstruction, final degree bound, zero-divisor semantics, exact division, normalization, and idempotence | `f7-poly-divmod-core`, `f7-poly-divmod`, `f7-poly-quotient`, and `f7-poly-remainder`; generated recursion, guards, reconstruction/canonicality/degree instances, and exact executions | None below XGCD |
| Normalization | `normalize`, canonical-polynomial interface, `poly-monic-normalize`, normalized/canonical output, zero/nonzero and leading-coefficient properties | `f7-normalize`, `f7-canonical-polynomial-p`, `f7-poly-monic-normalize`, verified guards, structural laws, and monic divisibility transport | None below XGCD |
| Divisibility/common divisors | Divisor-first `poly-divides-p`, `poly-common-divisor-p`, normalization laws, closure, transitivity, Euclidean-step equivalence, and monic-scaling transport | `f7-poly-divides-p`, `f7-poly-common-divisor-p`, fixing/normalization interfaces, both monic-normalization transports, and common-divisor transport | No monic-gcd uniqueness theorem, but it is not needed next |
| Raw Euclidean GCD | `poly-euclidean-gcd`, equations, canonicality, divides-both, greatestness, and `poly-euclidean-gcd-raw-correct` | `f7-poly-euclidean-gcd`, equations/guards, direct correctness instance and divisibility corollaries, including order- and scalar-sensitive exact results | Complete |
| Monic Euclidean GCD | `poly-monic-euclidean-gcd`, exactly monic normalization of raw GCD; structural and common-divisor correctness package | `f7-poly-monic-euclidean-gcd`, exactly the public wrapper stated in the task; guards, structural interface, correctness, total semantics, and exact regressions | Uniqueness remains open and optional |
| Raw XGCD/Bézout | `poly-extended-euclidean-gcd` returns `(g,s,t)`, follows the raw GCD remainder chain, calls `poly-divmod` once per step, has canonical projections, proves `g = poly-euclidean-gcd`, and proves `s*a+t*b=g` | None | **Selected next unit**: transparent F7 instance/runtime and its direct theorem package |
| Monic XGCD | `poly-monic-extended-euclidean-gcd` calls raw XGCD once, scales both coefficients by the inverse leading coefficient, returns the monic GCD, and proves its Bézout identity | None | Later small wrapper after F7 raw XGCD |
| Modular reduction/congruence | `poly-congruent-p` is equality of canonical remainders; equivalence, bounded-representative equality, modulus-multiple, and add/neg/sub/mul compatibility are certified | Concrete remainder exists, but there is no named F7 congruence or residue-class operation API | Functionally instantiate only the interface actually needed by quotient operations |
| Modular inverse | `poly-modular-inverse` reduces the monic-XGCD first coefficient; canonicality and the conditional product-remainder theorem are certified, including literal one for positive-degree modulus | None | Small concrete wrapper/instance after F7 monic XGCD |
| Coprimality | Expressible today as `poly-monic-euclidean-gcd = polynomial-one`; no separate named predicate is present | Same equality is expressible; no named predicate | Optional convenience definition |
| Irreducibility | No project definition, recognizer, decision procedure, selected-modulus certificate, or theorem connecting irreducibility to GCD one | None | New mathematical theory, but use a fixed certified modulus first |
| Quotient ring / extension field | Generic reduction and congruence prerequisites only; no residue-class carrier or quotient operation suite | None | New construction and bridges |

Repository searches also found no reusable project integer XGCD, matrix inverse,
linear-algebra inversion, quotient-ring constructor, or extension-field
constructor.  The relevant reusable extended-Euclidean machinery is precisely
the generic polynomial stack above.  Imported prime-field inverse and power
support coefficient arithmetic; neither is a polynomial XGCD replacement.

The roadmap/ledger entries relevant to this path are `GPOLY-MOD-REDUCTION`,
`GPOLY-MOD-CONGRUENCE`, `GPOLY-GCD-*`, `GPOLY-MONIC-*`, `GPOLY-XGCD`,
`GPOLY-EUCLIDEAN`, `GPOLY-XGCD-REDUCTION`, `GPOLY-MODULAR-INVERSE`, all F7
division/GCD entries, `EXT-FIELD-QUOTIENT`, and
`EXT-FIELD-IRREDUCIBILITY`.  Existing architecture notes additionally require
a named concrete field boundary before generic polynomial instantiation and
keep coordinate quotient rings distinct from quotient fields.

## What an executable certified `F7[x]/(m)` requires

The first milestone should fix one positive-degree, monic, concretely proved
irreducible `m`.  Values should be canonical F7 polynomials of degree below
`degree(m)`, obtained with `f7-poly-remainder`.  On that carrier ACL2 `equal`
is representative equality; before reduction, equivalence is equality of
remainders.

| # | Dependency | Classification and disposition |
| --- | --- | --- |
| 1 | Representation and residue normalization | Generic reduction is **already certified generically**; concrete divmod/remainder is **already certified for F7**. A small named fixed-modulus reducer and closure/idempotence bridges remain. |
| 2 | Equality/equivalence | Remainder equality and bounded-representative equality are **already certified generically**. A concrete F7 congruence instance is **requiring only functional instantiation**; canonical values may use `equal`. |
| 3 | Add, neg, sub, mul modulo `m` | Polynomial operations and generic reduction exist. Named fixed-modulus wrappers are **required for execution but not abstract correctness**, with small closure theorems. |
| 4 | Reduction respects operations | Add/neg/sub/mul congruence and remainder laws are **already certified generically**; F7 versions are **requiring only functional instantiation** plus small wrapper bridges. |
| 5 | Irreducibility | There is no definition. A generic hypothesis/interface and a certificate for the selected `m` are **requiring new mathematical theory**. A general executable decision procedure is **optional for the first milestone**. |
| 6 | Every nonzero class is invertible | The chain “irreducible + reduced nonzero representative implies monic GCD one” is **requiring new mathematical theory**. Bézout-to-inverse is already generic. |
| 7 | Executable inverse computation | Generic XGCD and modular inverse are certified. Concrete F7 XGCD/monic-XGCD/inverse are **required for execution but not abstract correctness** and should be transparent instances/wrappers. |
| 8 | Executable inverse law | Conditional generic inverse correctness is certified; F7 specialization is **requiring only functional instantiation**. Discharging its GCD-one premise from irreducibility is the new semantic bridge. Guard verification and executions remain separate assurance. |
| 9 | Existing field/polynomial infrastructure | Once the fixed quotient operations satisfy the GFIELD laws, using existing polynomial templates is **requiring only functional instantiation**. Cardinality/enumeration and a general `p^n` parameter object are **optional for the first extension-field milestone**, though later Schoof needs finite enumeration/cardinality. |

Ring operations do not logically depend on XGCD or irreducibility.  Building
their tiny wrappers before the inverse proof is therefore sound and makes the
eventual field carrier explicit.  They should not, however, displace concrete
XGCD as the *next* dependency: the existing generic quotient congruence proofs
already de-risk the ring side, while the missing concrete XGCD runtime is the
first unclosed executable link in the inverse chain.

## XGCD interface and the unit factor

The correct recursive specification returns raw `(g,s,t)`:

```text
g = f7-poly-euclidean-gcd(a,b)
f7-poly-add(f7-poly-mul(s,a), f7-poly-mul(t,b)) = g
```

This is the smallest faithful instance because it follows the same quotient and
remainder chain as the certified raw GCD.  Its immediate theorem interface is:

1. zero/nonzero structural equations and termination on normalized second
   length;
2. canonical/normalized `g`, `s`, and `t`;
3. first projection literally equals `f7-poly-euclidean-gcd`;
4. the unconditional raw Bézout identity;
5. verified guards and exact boundary, multi-step, reversed-order, scalar, and
   Bézout executions.

The raw result must not be advertised as monic.  If its leading coefficient is
`c`, define the later monic wrapper with `u = f7-inv(c)` and return

```text
(f7-poly-monic-normalize(g), f7-poly-scale(u,s), f7-poly-scale(u,t)).
```

Both coefficients must be scaled: `u*(s*a+t*b) = u*g`.  Scaling only `g`, or
claiming that raw coefficients witness the monic GCD, is incorrect whenever
the raw result exposes a nontrivial unit; the existing reversed-order/scalar
regressions make that case observable.

The monic wrapper then needs exact agreement with
`f7-poly-monic-euclidean-gcd`, canonical projections, unconditional monic
Bézout, and the special `monic-gcd = one` corollary.  Reduction of the first
coefficient modulo `m` and the inverse law are needed by modular inversion, but
belong in the following bridge/wrapper PRs.  A separate coprime predicate,
symmetry, coefficient uniqueness, or uniqueness of Bézout witnesses are later
convenience theorems.

## Irreducibility and monic-GCD uniqueness

The minimum useful generic interface is semantic, not an algorithm:

* a named `poly-irreducible-p(m)` over canonical positive-degree nonunits,
  stated through nontrivial divisors/factorizations (with degree conditions to
  exclude units);
* `poly-irreducible-p(m)`, reduced `a`, and `a != 0` imply
  `poly-monic-euclidean-gcd(a,m) = polynomial-one`;
* the existing monic Bézout and reduction theorems then supply an inverse.

The exact syntactic definition should be selected in its own proof PR after
checking which divisor/degree formulation minimizes unit lemmas.  This audit
does not silently choose or claim one.  Separate three deliverables: (1) a
generic quotient construction parameterized by the irreducibility theorem,
(2) a proof that one chosen small monic F7 modulus is irreducible, and only
later (3) a general executable irreducibility test.

Monic-GCD uniqueness is **not** a prerequisite.  Coprimality can be the literal
computed equality to one; modular-inverse correctness assumes exactly that
equality; and the irreducibility bridge can prove it from the certified
greatest-common-divisor and monic output properties.  Quotient operations do
not mention uniqueness.  Functional instances likewise transport literal
function equalities.  Leave uniqueness open unless a later abstraction needs
to equate two independently specified monic GCDs.  At that point the useful
statement is: canonical monic `g` and `h` that divide one another are equal.
The missing core is the associates/unit argument (mutual divisibility plus
equal monic leading coefficients), not Euclidean recursion.

## Alternative inversion strategies

| Strategy | Computability / admission | Reuse and genericity | Verdict |
| --- | --- | --- | --- |
| XGCD | Transparent recursion on the already certified remainder descent; one divmod per step | Reuses the complete generic Bézout, scaling, reduction, and inverse chain; uniform for `F_(p^n)` and suitable for Schoof | **Selected** |
| Exponentiation by `q-2` | Fast and transparent once fast power exists | Needs a proved field cardinality `q`, finite-field multiplicative theory, and Fermat; circular before the quotient is proved a field | Later optimization, not a smaller proof chain |
| Exhaustive search | Easy only after a finite enumeration and decidable canonical carrier exist; poor practical behavior | Needs cardinality/enumeration and a proof search finds a witness; unsuitable for later Schoof workloads | Reject |
| Matrices / linear algebra | Executable Gaussian elimination needs pivots, termination, and correctness | Rebuilds substantial algebra and still needs coefficient inverses; less direct than Euclid | Reject |
| Abstract existence only | Can support abstract correctness | Supplies no executable witness and cannot meet the public runtime boundary or Schoof computation requirements | Insufficient |

None is a materially smaller trusted and executable dependency chain than the
already certified generic XGCD path.

## Recommended sequence of one-idea PRs

Sequence B has effectively completed its generic half already.  Sequence A is
now best read as the remaining concrete tail of B.  Sequence C is algebraically
valid but does not close the first missing executable inverse dependency.
Sequence D is useful only for the irreducibility certificate and final named
field; duplicating XGCD concretely without instantiating the generic theorem
package would sacrifice reuse.

1. **F7 raw XGCD instance (exact next PR).** Add the transparent generated or
   handwritten `f7-poly-extended-euclidean-gcd` recursion with the exact generic
   control flow.  Prove projection equality to raw F7 GCD, canonical projections,
   unconditional raw Bézout, guards, and focused exact executions.  Depends only
   on certified F7 divmod/GCD/operations and generic XGCD.  It cannot be combined
   with monic scaling without mixing recursion/instantiation with a distinct unit
   argument.
2. **F7 monic XGCD wrapper.** Add one nonrecursive wrapper scaling both raw
   coefficients, with monic-GCD projection and monic Bézout theorems plus unit
   regressions.  Depends on PR 1 and existing F7 monic normalization.  Keep it
   separate because the explicit unit factor is its sole mathematical idea.
3. **F7 XGCD reduction bridge.** Instantiate the generic first-coefficient
   reduction and positive-degree literal-one corollary.  No new computation.
   This isolates quotient congruence from XGCD arithmetic.
4. **F7 modular inverse wrapper.** Add the reduced first-coefficient wrapper,
   canonicality, conditional inverse law, guards, and coprime/noncoprime exact
   executions.  It can and should be a separate tiny PR because it assumes GCD
   one and makes no irreducibility claim.
5. **Fixed-modulus residue ring.** Select a small monic positive-degree F7
   modulus; add reducer, carrier, equality policy, and reduced add/neg/sub/mul
   wrappers.  Instantiate congruence, closure, equality, and ring laws; run exact
   operation tables/examples.  This is independent of irreducibility and must
   not be called a field yet.
6. **Irreducibility interface.** Define the generic semantic predicate and prove
   the irreducible/nonzero-representative-to-monic-GCD-one bridge.  This is one
   new mathematical idea and cannot be hidden in a concrete computation PR.
7. **One concrete irreducibility certificate.** Prove the selected modulus
   satisfies that predicate, with exhaustive finite checks only as certified
   supporting lemmas.  Do not build a general decision procedure yet.
8. **Named fixed F7 extension field.** Connect PRs 4--7, prove the inverse law
   and the remaining GFIELD laws, verify guards, add focused concrete inverse and
   operation regressions, then instantiate existing generic polynomial
   infrastructure.  Cardinality/enumeration is a later focused PR before code
   that requires it.

Thus: XGCD is genuinely the next *concrete execution* dependency, but generic
XGCD is already done; instantiate F7 next.  Return the raw result from the
recursive implementation and perform monic rescaling in a separate wrapper.
Monic-GCD uniqueness is unnecessary.  Modular inverse is a separate tiny
wrapper PR.  Quotient-ring operations should precede the final inverse/field-law
integration, though not the XGCD work.  The first field should use one fixed
small irreducible modulus.  The exact next scope is item 1 and nothing beyond it.
