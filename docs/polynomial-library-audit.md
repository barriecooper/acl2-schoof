# ACL2 Community Books polynomial-library audit

> **Historical design record.** Status and “next” sequences in this audit describe
> the revision at which it was written. Current status is maintained only in
> `obligations.md`; current sequencing is in `proof-plan.md`.

## Scope and reproducibility

This is a documentation-only audit.  It adds no polynomial operation, theorem,
package import, or include-book.  The repository base inspected was
`c86ff99a8b2f04e2d7b771b9aa131428fe461f6f`, the merge of the canonical
polynomial-multiplication pull request.

The repository pins ACL2 by the contents of `ACL2_VERSION`; the installer does
a shallow clone of the tag with that name.  The exact installation inspected
was:

| Item | Exact value |
|---|---|
| ACL2 release/tag | `8.6` |
| ACL2/Community Books Git commit | `7585056a0647c1ab8a45b1573c5cfe524acbda3f` |
| Community Books root | `.deps/acl2-8.6/books` (linked as `.deps/acl2/books`) |
| Host Lisp used to build ACL2 | `SBCL 2.2.9.debian` |

The commit was obtained from `git -C .deps/acl2-8.6 rev-parse HEAD`, not
inferred from a release name or from the web.  All paths below are relative to
that exact Community Books root.  Source files and their direct includes were
opened locally.  After installing the missing host Lisp and building
`saved_acl2`, the two include experiments described below were also certified
against this installation.

### Temporary include experiments

Two throwaway books were created under ignored `.deps/experiments`, certified,
and left out of the commit:

```lisp
(include-book "workshops/2022/gamboa-primitive-roots/pfield-polynomial"
              :dir :system)
(include-book
 "workshops/2006/cowles-gamboa-euclid/Euclid/fld-u-poly/fuquot-rem"
 :dir :system)
```

Both succeeded.  The first loaded
`PFIELD::NUM-ROOTS-OF-POLY-UPPER-BOUND`; the second loaded
`FUNPOL::QUOT-REM-REWRITE`.  The complete logs were
`.deps/logs/experiment-pfield-include.log` and
`.deps/logs/experiment-fuquot-include.log`.  This confirms that both endpoint
books and dependency chains can be included by this ACL2/SBCL installation.
It does **not** establish the future prime-field functional instantiation or
HS conversion proofs.

## Method

The search covered the whole local Books tree, not merely filenames.  The main
reproducible commands (run from `.deps/acl2-8.6/books`) were:

```sh
find . -type f \( -iname '*poly*.lisp' -o -iname '*polynomial*.lisp' \
  -o -iname '*horner*.lisp' \) | sort

rg -l -i '^\s*\((defun|define|defund|defun-sk|defchoose|encapsulate).*\
?(poly|coeff|horner|monomial)' --glob '*.lisp' | sort

rg -n -i '(polynomial|poly|coefficient|coeff|evaluate|eval|degree|\
leading.coefficient|normalize|trim|add|multiply|divide|quotient|\
remainder|gcd|derivative|root|irreducible|separable|horner|sparse|dense)' \
  --glob '*.lisp'

rg -l -i '(polynomial|poly-|poly\b|coefficient|horner|irreducible|\
separable|division polynomial)' kestrel/crypto projects/curve25519 \
  projects/elliptic-curves projects/pfcs --glob '*.lisp'

rg -n -i '(skip-proofs|defaxiom|defttag|trust-tag|progn!)' \
  nonstd/polynomials workshops/2000/medina/polynomials \
  workshops/2006/cowles-gamboa-euclid/Euclid/fld-u-poly \
  workshops/2018/gamboa-cowles/complex-polynomials.lisp \
  workshops/2018/greve-gacek/poly.lisp \
  workshops/2020/gamboa-cowles-gamboa/polylist.lisp \
  workshops/2022/gamboa-primitive-roots/pfield-polynomial.lisp \
  projects/shnf nonstd/fft/eval-poly.lisp
```

The broad content search was split into smaller `rg` queries during inspection
so that every match could be reviewed without relying on truncated output.
Candidate files were read around definitions and theorems, and their
`include-book` chains and package setup (`*.acl2`, `certify.lsp`, or
`certification.lsp`) were inspected.  Hits in documentation, generated
`.sys` files, Lisp implementation bundles, and examples that merely use
ordinary arithmetic were discarded.

Terminology in the tables is strict:

* **algebra library** means data, executable operations, and algebraic
  correctness theorems;
* **normal-form rewriter** means a representation of ACL2 expressions for
  proving expression equalities, not a finite-field polynomial API;
* **project-local representation** means a data structure designed for the
  surrounding proof (FFT, constraints, the fundamental theorem of algebra,
  and so on);
* **abstract** means constrained operations and functional-instantiation
  obligations rather than executable operations for a chosen prime field.

## Inventory

### Serious candidates

1. **ACL2(r)/rational dense coefficient lists:**
   `nonstd/polynomials/polynomial-defuns.lisp`,
   `nonstd/polynomials/polynomial-lemmas.lisp`, and
   `nonstd/polynomials/polynomial-calculus.lisp`.
2. **Abstract field univariate polynomials with Euclidean division:** the
   complete chain under
   `workshops/2006/cowles-gamboa-euclid/Euclid/fld-u-poly/`: `coe-fld.lisp`,
   `futermino.lisp`, `fumonomio.lisp`, `fupolinomio.lisp`,
   `fuforma-normal.lisp`, `fusuma.lisp`, `fucongruencias-suma.lisp`,
   `fuopuesto.lisp`, `fuproducto.lisp`, `fucongruencias-producto.lisp`,
   `fupolinomio-normalizado.lisp`, and `fuquot-rem.lisp`.
3. **Prime-field evaluation and root counting:**
   `workshops/2022/gamboa-primitive-roots/pfield-polynomial.lisp`, layered on
   the nonstd dense-list definitions.
4. **Expanded ACL2-number dense-list theory:**
   `workshops/2020/gamboa-cowles-gamboa/polylist.lisp`.
5. **Rational sparse multivariate normal forms:** the chain under
   `workshops/2000/medina/polynomials/`, especially `polynomial.lisp`,
   `normal-form.lisp`, `addition.lisp`, `negation.lisp`, and
   `multiplication.lisp`.
6. **Sparse symbolic polynomial framework:**
   `workshops/2018/greve-gacek/poly.lisp` (with `env-type.lisp` and
   `varid-type.lisp`).
7. **Sparse Horner normal form:** `projects/shnf/top.lisp` (a newer,
   comparatively compact development) and `projects/shnf/support.lisp` (the
   larger supporting proof).

### Relevant but not reusable as the main algebra

* `workshops/2018/gamboa-cowles/complex-polynomials.lisp` is a
  complex-coefficient, dense-list development for the fundamental theorem of
  algebra.  It supplies `polynomial-p`, `eval-polynomial`, `leading-coeff`,
  scaling, addition, shifting, root and zero predicates, but its domain and
  large nonstandard-analysis dependency are wrong for Schoof.
* `nonstd/fft/eval-poly.lisp` uses constant-first **powerlists** and proves FFT
  evaluation/vector identities.  Its `p-*` is pointwise vector
  multiplication, not polynomial convolution.
* The section-2 books under
  `workshops/2002/medina-palomo-alonso/support/` expose an abstract `UPOL`
  interface (`polynomialp`, `nf`, `nfp`, `=`, `+`, `*`, unary `-`, `null`, and
  `identity`) inside `encapsulate`.  They provide commutative-ring laws but no
  representation, evaluation, degree, or algorithms.  The section-3 books
  provide monomial/term normal forms aimed at Noetherian rewriting.  These are
  useful proof-pattern precedents, not an API to execute.
* `nonstd/integrals/integral-of-polynomials.lisp` consumes the nonstd
  polynomial calculus; it is not another algebra implementation.
* `coi/util/eliminate-complex-polys.lisp`,
  `coi/util/linearize-complex-polys.lisp`, `centaur/misc/multiply-out.lisp`,
  and `centaur/misc/collect-like-terms.lisp` are expression transformers or
  proof utilities.
* `projects/curve25519/reduce.lisp` and `top.lisp` normalize/reduce particular
  arithmetic expressions.  The Kestrel elliptic-curve books describe curve
  equations and field-point operations; they do not define a univariate
  polynomial algebra.  The R1CS/PFCS hits concern linear combinations,
  constraints, or variables, not polynomial division or finite-field
  polynomial objects.
* No definition or book for elliptic-curve **division polynomials** was found.
  No serious candidate supplies separability theory or a polynomial gcd.

## Detailed comparison

Legend: “—” means the inspected books do not provide the item, rather than
that it could not be found by name.

| Candidate | Domain and parameterisation | Representation, order, zero, equality, canonicality | Executable operations | Material theorems / missing theory | Dependencies, abstraction, and inclusion |
|---|---|---|---|---|---|
| `nonstd/polynomials/{polynomial-defuns,polynomial-lemmas,polynomial-calculus}.lisp` (package `ACL2`) | Rationals in ordinary ACL2; reals under ACL2(r). No modulus. `integer-polynomial-p` is also provided. | Proper dense list `(c0 ... cn)`, constant first. `nil` evaluates to zero, but `(0)`, `(0 0)`, etc. remain distinct; no normalization or canonical equality. | `eval-polynomial`, `eval-polynomial-expt`, `scale-polynomial`, `polynomial-+`, `polynomial-*`; calculus adds `derivative-polynomial` and integrals. | Closure and evaluation homomorphisms (`real-polynomial-*`, `eval-polynomial-*`, corresponding `+`/scale results), roots, and analytic derivative correctness. No algebraic degree/lc, division, gcd, irreducibility, or separability. | Small footprint for defuns/lemmas; calculus pulls in nonstandard integration. No constrained coefficient interface. The core can be included cleanly, but symbol collisions in `ACL2` and noncanonical integer arithmetic require a bridge. |
| The twelve exact `workshops/2006/cowles-gamboa-euclid/Euclid/fld-u-poly/` paths listed in the inventory, culminating in `fupolinomio-normalizado.lisp` and `fuquot-rem.lisp` (packages `FLD`, `FUTER`, `FUMON`, `FUPOL`, `FUNPOL`) | Arbitrary field specified by constrained `FLD::fdp`, `+`, `*`, unary `-`, reciprocal `/`, `0_f`, `1_f`, equivalence `=`, and representative choice `C_=`. Not a directly selected modulus. | Sparse ordered list of monomials `(coefficient . natural-exponent)`, largest term first. `nil` is normalized zero. `FUPOL::fn` combines/removes terms; `FUNPOL` wraps normalized results. Equality is the library equivalence, with normalized operations yielding representatives. | Normalization, `+`, `-`, `*`, `deg`, `lc`, `quot`, and `rem` are executable over the encapsulate witnesses; a concrete prime-field execution requires a new concrete layer, not merely an include. | Very strong well-formedness, normalization/congruence and ring laws; `deg(product)=deg(p)+deg(q)`, nonzero leading coefficient, terminating long division, remainder degree bound, and quotient/remainder reconstruction (`quot-rem-rewrite`). No evaluation API, powers, gcd, derivative, roots, irreducibility, or separability. | Large old workshop chain and five packages; abstract field encapsulate plus functional-instantiation obligations. Package portcullis must define all packages before inclusion. Clean trust source; its endpoint include experiment certified successfully. This is the only discovered source for general field division and product-degree theory. |
| `workshops/2022/gamboa-primitive-roots/pfield-polynomial.lisp` (package `PFIELD`, dense operations imported from `ACL2`) | Integer coefficients evaluated modulo parameter `p`; key root/product theorems assume `DM::primep p`. Coefficients are not required to be `FEP` representatives. | Same constant-first dense integer lists as nonstd. The last coefficient modulo `p` determines “non-trivial”; no trim/canonicalizer, so many lists denote the same polynomial function. Ordinary list equality is syntactic. | `eval-pfield-polynomial`, root predicate, exhaustive root counter/finder, division specifically by `x+a`, and constructors for `x^k-1`; uses executable nonstd `polynomial-+`, `polynomial-*`, and scale. | `fep-eval-pfield-polynomial`, evaluation of products, root-of-product, linear root results, synthetic-division evaluation/remainder lemmas, root finder correctness, and `num-roots-of-poly-upper-bound`. No general degree/lc, general division, gcd, derivative, irreducibility, or separability. | Includes nonstd defuns and Kestrel prime fields; local proof dependencies include nonstd lemmas, `projects/numbers/euclid`, and arithmetic-5. It is concrete and highly relevant, but is a project book with a large specialized proof. Namespace overlap with HS's existing `PFIELD` dependency is natural. Its endpoint include experiment certified successfully. |
| `workshops/2020/gamboa-cowles-gamboa/polylist.lisp` (package `ACL2`) | ACL2 numbers, with integer/rational/real closure variants; no modulus. | Proper constant-first dense lists. `zero-polynomial-p` accepts every all-zero length; trailing zeroes remain. Equality is syntactic plus some evaluation-extensional predicates, not a canonical quotient. | Evaluation, negation, scale, addition, multiplication, composition, translation, reversal, truncation, and derivative-related functions are executable. | Extensive evaluation, length, last-coefficient, nonzero-product, composition, derivative and fundamental-theorem-of-algebra support. It uses length/nonzero-last as degree information but offers no clean general `degree` API, field division, gcd, irreducibility, or separability. | Large (about 1,900 lines), ACL2/ACL2(r)-conditional, and depends on arithmetic, list, norm, square-root/floor books. Includes explicitly prohibit uncertified books, axioms, and skipped proofs. Too analytic and symbol-heavy to include for its small overlap with HS. |
| `workshops/2000/medina/polynomials/{polynomial,normal-form,addition,negation,multiplication}.lisp` (packages `TER`, `MON`, `POL`) | Rational coefficients, fixed to ACL2 rationals; multivariate terms. | Sparse lists of `(coefficient . term)` monomials, ordered by lexicographic term order. `POL::nf` combines terms and removes zero monomials. Zero is an empty normalized list; `POL::=` is semantic equality through normal forms. | Constructors, normalization, `+`, unary `-`, and `*` execute. | Polynomial/ordered/normal-form closure, equality congruence, additive and multiplicative commutative-ring laws. No evaluation, univariate degree/lc API, field division, gcd, derivative, roots, irreducibility, or separability. | Medium old workshop chain with custom package portcullis. Concrete but fixed to rationals and multivariate sparse machinery; translating FEP lists is costly and loses modular semantics. |
| `workshops/2018/greve-gacek/poly.lisp` (package `ACL2`) | Rational coefficients (`rfix`) with symbolic variable identifiers and environments; no finite-field parameter. | Recursive sparse symbolic form with a constant and coefficient map keyed by variables; equivalences/fixers account for ordering and zero coefficients. It is not a univariate coefficient sequence. | `const-poly`, `coeff-poly`, `plus`, `mul`, `sub`, variable dropping and `poly-eval` are executable. | Coefficient getters, variables/leading variable, closure/fixer/equivalence, and evaluation homomorphisms for plus/mul/sub. No univariate degree, lc, division, gcd, derivative, or finite-field roots. | Large COI quantification/deffix/n-ary stack and project-specific environment types; nested encapsulates support equivalence reasoning. It is a symbolic sparse framework, not a finite-field algebra. |
| `projects/shnf/{top,support}.lisp` (package `DM`) | Integer-coefficient ACL2 expressions over a supplied variable list. | Sparse Horner forms encoded as integers and `(:POW i p q)`-like recursive nodes. Canonicality is `shf-normp`/`shnfp`; equality is established by integer evaluation witnesses. Not a coefficient list. | `norm`, `norm-add`, `norm-neg`, `norm-mul`, `norm-expt`, `evalp`, and `evalh` execute. | Normal-form closure and preservation of integer evaluation; witness theorems establish inequivalence. No field operations, coefficient sequence, degree/lc, division, gcd, derivative, or finite-field root theory. | Depends chiefly on RTL arithmetic (and more proof utilities in `support`). It is exactly a normal-form rewriter for expressions, not reusable polynomial algebra. |

### Trust and portcullis findings

The serious candidate source sets contain no `skip-proofs`, `defaxiom`,
`defttag`, trust-tag event, or raw-Lisp escape.  The strings
`:skip-proofs-okp nil` and `:defaxioms-okp nil` in `polylist.lisp` strengthen,
rather than weaken, its include checks.  Several books use `encapsulate`:
ordinary local proof organization is harmless, while `FLD` deliberately uses
constrained field operations and the 2002 `UPOL` books deliberately define an
abstract interface.  Those constraints are logical assumptions discharged by
functional instantiation, not executable prime-field definitions and not trust
escapes.

The repository's `books/package.lisp` defines only `HS` (and imports the
already-established Kestrel `PFIELD` symbols).  The `ACL2` and `PFIELD`
candidates need no new project package, but the workshop-2006 chain requires
the `FLD`, `FUTER`, `FUMON`, `FUPOL`, and `FUNPOL` package setup recorded in its
`certify.lsp`/book portcullises.  The workshop-2000 and FFT candidates likewise
require their custom packages.  Consequently “the source has no trust escape”
does not imply “drop-in include”: package events and certificates must be
reproduced in the including book's portcullis, and that needs a certification
experiment before adoption.

## Comparison with the HS layer

HS already has the best concrete representation for this project:

* proper dense lists `(c0 c1 ... cn)`, constant coefficient first;
* every coefficient satisfies `PFIELD::FEP` for a parameter `p`;
* trailing zero coefficients are removed by `poly-normalize`;
* `nil` alone is canonical zero;
* `poly-add` and `poly-mul` normalize their executable raw results; and
* evaluation theorems connect both operations to Kestrel field arithmetic.

No candidate matches all six properties.  Translation costs are:

* **Nonstd/2022 dense lists:** structurally identical order, so translation is
  linear and can initially be the identity/list map.  HS-to-integer is trivial
  because every FEP is an integer.  The reverse direction must apply
  `PFIELD::FEP-FIX` coefficientwise and HS normalization.  Proofs must show
  modular evaluation is preserved and account for the candidate's multiple
  trailing-zero representations.  This is the lowest-cost and highest-value
  bridge, especially for the finite-field root bound.
* **Workshop-2006 `FUNPOL`:** converting HS dense lists to sparse descending
  monomials is linear after reversal/zero filtering, but coefficients must be
  related to the abstract `FLD` equivalence.  Going back requires filling all
  exponent gaps, choosing FEP representatives, reversing, and normalizing.
  More importantly, reuse of its theorems needs functional instantiation of
  every field axiom with Kestrel prime-field operations (under primality), plus
  congruence and package work.  This is a significant bridge, but its
  product-degree and Euclidean-division proofs make it worth a bounded
  feasibility study.
* **Workshop-2000, 2018 sparse, and SHNF:** conversion also changes domain
  (rational/integer rather than modular), multivariate/symbolic shape, and
  equality.  These are higher cost while supplying no division/root result
  that HS needs.
* **Powerlists:** conversion must pad to the balanced powerlist sizes expected
  by the FFT representation, while it supplies evaluation rather than
  polynomial algebra.  There is no payoff at this stage.

Changing HS merely to use the nonstd dense representation would lose canonical
zero and FEP closure.  Changing HS to `FUNPOL` now would replace a small,
working executable interface with an abstract sparse interface before its
prime-field instantiation is known to certify.  Neither change is justified by
the audit.

## Recommendation: strategy C

**Keep the HS representation and add proved conversion functions to selected
existing libraries for advanced results.**  This is strategy **C**, staged so
that failure of the workshop-2006 instantiation does not disturb HS.

The first reuse target should be the 2022 `PFIELD` book's root-count theorem,
using the near-identity dense-list bridge.  The second target should be a small
feasibility bridge to the workshop-2006 abstract field development.  Only if
the field functional instantiation and one conversion theorem certify should
later PRs transport `deg`, `lc`, product degree, `quot`, `rem`, and their key
laws.  HS remains the executable façade; the sparse library is a semantic
backend for proved advanced results, not the runtime representation.

This is preferable to:

* **A (direct reuse):** no library has HS's concrete finite-field canonical
  interface plus the required advanced operations;
* **B (façade over one library):** the strongest division library is abstract
  and sparse, while the strongest root library is concrete and dense—there is
  no single suitable backend;
* **D (migration):** it would invalidate certified HS interfaces before
  feasibility is established and would impose sparse/abstract costs on every
  computation; and
* **E (entirely bespoke):** it would unnecessarily re-prove the finite-field
  root bound and, if functional instantiation succeeds, long division and
  product-degree theory.  The total Hasse–Schoof cost favors bridges despite
  their nontrivial engineering cost.

### Consequences for later mathematics

* **Degree and leading coefficient:** define the public HS notions only after
  the `FUNPOL` feasibility PR.  Prefer conversion/transport theorems for
  nonzero canonical polynomials; specify HS zero degree separately because
  `FUNPOL::deg nil` is not its nonzero theorem case.
* **Degree of a product:** transport
  `FUNPOL::|deg (p1 * p2) =e deg p1 ACL2::+ deg p2|` after proving conversion
  commutes with multiplication and that prime fields have no zero divisors.
  Do not duplicate its long proof unless functional instantiation fails for a
  documented technical reason.
* **Division and Euclidean algorithms:** transport `FUNPOL::quot` and
  `FUNPOL::rem` semantically, retaining an HS executable wrapper only after
  quotient/remainder conversion and the remainder-degree bound certify.
  `PFIELD::divide-polynomial-with-remainder-by-x+a` remains useful for the
  special linear case and root arguments, but is not general division.
* **Gcd and coprimality:** no candidate supplies them.  Build Euclid in HS over
  the transported division contract, with monic normalization in FEP
  representatives.  This will be new mathematics in later, separately scoped
  PRs.
* **Formal derivatives:** the nonstd calculus definition is structurally
  reusable, but its correctness is analytic and rational.  A later PR may use
  its executable list pattern; finite-field closure, product rule, and
  conversion results still require prime-field proofs.  Do not include the
  large calculus book just for the definition.
* **Roots over finite fields:** prioritize conversion to
  `PFIELD::pfield-polynomial-root-p` and reuse
  `PFIELD::num-roots-of-poly-upper-bound`, plus its product and linear-factor
  lemmas.  Reconcile whether zero is included in its auxiliary/root counting
  range explicitly in the bridge statement.
* **Separability:** absent.  Develop it later from HS derivative, gcd and root
  theory; the root-count theorem should reduce the amount of new counting
  work.
* **Rational functions:** keep numerator/denominator in canonical HS form.
  Use transported gcd/degree contracts; do not expose sparse `FUNPOL` objects
  in the rational-function API.
* **Elliptic-curve morphisms:** keep coordinates expressed using HS rational
  functions so Kestrel FEP operations remain executable.  Conversion belongs
  at proof boundaries only.
* **Schoof division polynomials:** none exist in the inspected tree.  They will
  be new HS recursive objects, but their degree, leading coefficient,
  coprimality and root facts should consume transported generic algebra rather
  than re-prove it for each recurrence.
* **Manin-style Hasse degree calculations:** the transported product-degree and
  quotient/remainder results are the main prospective saving.  Morphism-level
  cancellation and composition degree remain project-specific; isolating a
  stable HS degree API prevents the abstract backend from leaking into them.

## Proposed sequence of focused pull requests

1. **Include feasibility only:** add a temporary/minimal certified book that
   includes the 2022 PFIELD book under the repository portcullis and proves a
   harmless existing-symbol check; retain it only if it provides lasting CI
   value.  No new polynomial operation.
2. **Dense root bridge:** define HS/nonstd conversion (or prove identity where
   appropriate), evaluation preservation, and equivalence of root predicates;
   transport the finite-field root-count upper bound.
3. **Abstract-field feasibility only:** establish the workshop-2006 packages,
   include its normalized/quotient-remainder endpoint, and functionally
   instantiate a minimal field law with Kestrel prime-field operations.  Stop
   and record the precise obstruction if this cannot certify cleanly.
4. **Sparse conversion:** add mutually inverse-up-to-normalization conversions
   between canonical HS lists and normalized `FUNPOL`, with well-formedness and
   equality/evaluation bridge theorems.
5. **Degree/lc transport:** expose HS degree and leading coefficient and
   transport the product-degree result in one tight lemma group.
6. **Division transport:** expose quotient/remainder through the HS façade and
   transport reconstruction and the remainder-degree bound.
7. **Euclid/gcd:** add monic gcd and coprimality over the now-stable division
   interface.
8. **Derivative and separability:** add the executable derivative, product
   rule, derivative/gcd separability criterion, and connect them to the reused
   root bound.

Each PR must independently run the repository trust scan, focused
certification, smoke test, and full certification.  This audit does not mark
any mathematical obligation as proved and does not change the roadmap: it
records the decision point that must precede the degree milestone.
