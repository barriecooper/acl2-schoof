# Schoof trace-congruence route audit

## Scope, authority, and baseline

This read-only audit selects the smallest defensible correctness boundary after
merged PR #347, project commit `2e33ecd13dbaa0cf8e3e1a448eff09b036a5a9f2`.
It compares dependencies; it does not certify any new mathematics.  Current
status remains authoritative in the [obligation ledger](../obligations.md), and
forward order remains authoritative in the [proof plan](../proof-plan.md).

The inspected production chain includes the books defining the generic
curve-level `psi_3` theorem, the F11 division-polynomial specialization, the
quotient-coordinate ring and trace predicate, the single-field semantic
soundness theorem, and PR #347's base-to-ambient semantics and soundness books.
Both books included by those endpoints and their consumers in `books/top.lisp`
were inspected.  No ACL2 event is added or inferred by this document.

## Certified starting boundary

The repository currently certifies all of the following, but not their desired
classical composition.

1. The executable F11 quotient-coordinate trace predicate rejects residues 0
   and 1 and accepts the algebraic candidate 2 for
   `psi_3 = (10 6 6 0 3)`.  The accepted branch has concrete nonzero quotient
   representatives for its displayed `D`, `N`, and cross-products.
2. Predicate acceptance transports one way to identically oriented cross
   equations in the existing single-field semantic interface at a supplied
   modulus root (and, for multiplication, a supplied curve point).
3. PR #347 separately transports those equations from the base quotient
   calculation to a supplied root and curve point in an **assumed commutative
   ring**.  The seam has no ambient inverse, domain, field, algebraic closure,
   root existence, injectivity, Frobenius, or cardinality assumption.
4. In the repository's generic curve field context, for every valid affine
   point in the stated characteristic range, `psi_3(x)=0` iff `[3]P` is
   infinity.  This is a pointwise theorem, not existence or enumeration of
   `E[3]`.
5. The concrete F11 curve has 12 exhaustively enumerated affine points plus
   infinity as independent certified regression/reference evidence, so its
   actual trace is `11 + 1 - 13 = -1`, hence 2 modulo 3.

There is no theorem yet that the accepted candidate is the Frobenius trace
modulo 3.  In particular, quotient nonzeroness is not semantic nonzeroness at
every root, and cross equations in a commutative ring are not an affine group
equation without the relevant cancellation and denominator facts.

## Washington Chapter 4 as a dependency route

The reference is Lawrence C. Washington, *Elliptic Curves: Number Theory and
Cryptography*, second edition, Chapter 4, especially the finite-field
Frobenius and Schoof sections in the
[specified edition](https://people.cs.nycu.edu.tw/~rjchen/ECC2012S/Elliptic%20Curves%20Number%20Theory%20And%20Cryptography%202n.pdf).
It is used here as a dependency map, not as an instruction to reproduce its
presentation or notation.

The classical route lets the `q`-power Frobenius `pi` act on points over an
algebraic extension.  For `ell != char(F_q)`, it identifies `E[ell]` with a
rank-two module over `F_ell`, represents `pi` linearly, and uses determinant
`q` and trace `t` to obtain

```text
pi^2 - [t] pi + [q] = 0  on E[ell].
```

Cayley--Hamilton supplies the matrix identity once the representation and its
trace and determinant have already been identified.  Schoof then computes the
candidate relation modulo the division polynomial, handles exceptional
addition branches, obtains residues for enough small primes, combines them by
CRT, and selects the unique trace using `|t| <= 2 sqrt(q)`.

### Prerequisites suppressed by the paper presentation

Each textbook transition expands into a formal obligation:

| Textbook step | Formal prerequisites that must be explicit |
|---|---|
| Frobenius on an algebraic extension | A carrier containing the required coordinates; base embedding; field and characteristic/cardinality facts; coordinatewise Frobenius preserving the curve, infinity, equality, negation, addition, and scalar multiplication. |
| `E[ell]` is rank two | `ell` prime and different from the characteristic; an actual torsion carrier including infinity; closure; scalar laws; existence and exact cardinality `ell^2`; basis existence/independence/spanning.  The repository's pointwise `psi_3` iff theorem is not this result. |
| Frobenius has a matrix | Linearity on that module, a chosen basis, coordinate uniqueness, and compatibility between matrix composition and point-map composition. |
| Determinant is `q mod ell` | A Weil-pairing or equivalent theorem, including bilinearity, nondegeneracy, Frobenius action on roots of unity, and the scalar action; alternatively an equally substantial kernel/degree argument. |
| Matrix trace is `q+1-#E(F_q)` | Fixed points of Frobenius are exactly base-field points, the kernel/cardinality or determinant formula for `1-pi`, separability where degree is used, and conversion of integer cardinality to `F_ell`.  This is not the definition of matrix trace. |
| Cayley--Hamilton | A matrix/ring representation and the characteristic identity.  A fixed `2x2` expansion avoids general characteristic-polynomial theory but does not prove the preceding determinant or trace claims. |
| Equality modulo `psi_ell` | A proved divisibility/quotient equivalence and correct bivariate or separated-`2y` semantics, or a universal evaluation theorem at every relevant root.  Equality in the current quotient ring is universal only conditionally at supplied roots; it does not construct or enumerate them. |
| Roots represent all nonzero torsion | `psi_ell` semantics, existence, degree/root count, simple or distinct roots (`ell != char` plus separability/square-freeness), and completeness.  For odd `ell`, each torsion x-coordinate normally has two ordinate choices; both must exist, be covered, and interact correctly with negation and Frobenius. |
| “One point iff all points” | Either a basis plus linear-algebra argument, transitivity with proved hypotheses, or a universal-root/divisibility statement.  One chosen root or one extension witness cannot silently stand for all points. |
| Cross products encode addition | Curve membership; nonzero secant denominator for the ordinary branch; field cancellation/inversion; exact sign/orientation; and separate equal-x, opposite, doubling, and infinity cases.  Cross multiplication admits extra solutions when the denominator is zero or a zero divisor. |
| Exceptional Schoof branches | Certified decisions for `D=0`, opposite/infinity, doubling/equal-x cases, zero candidate, and sign disambiguation; proof that the branches are exhaustive and agree with the group operation. |
| CRT and Hasse selection | Correct residues for pairwise-coprime primes, a certified modulus product bound, centered CRT existence/uniqueness, the Hasse bound itself, and a final connection from trace to point count. |

Thus neither “one point iff all points” nor equality modulo a division
polynomial is accepted here without a completeness, square-freeness, basis, or
universal-root argument appropriate to the exact statement.

## Complete route comparison

### A. Torsion-module and matrix route

This is the most direct transcription of the conceptual proof, but not the
smallest next boundary.  It must construct or characterize `E[3]` as a
two-dimensional `F_3` vector space, prove Frobenius linear, and connect point
endomorphisms to a matrix.  A local four-entry commutative-ring proof can
replace general Cayley--Hamilton.  It cannot replace proofs that the determinant
is `11 mod 3 = 2`, that the matrix trace is
`12 - #E(F_11) mod 3`, or that the resulting point equation has the orientation
tested by the quotient predicate.  Those fixed-point/cardinality and torsion
coverage results dominate the matrix algebra.  The Community Books audit found
useful matrix and determinant infrastructure, but no ready Cayley--Hamilton
endpoint and a substantial representation mismatch.

**Cost/risk:** high foundational cost and a new module/matrix boundary before
the current F11 predicate gains even its affine interpretation.  Defer it.  If
later selected, use the bounded `2x2` identity only after stating how determinant
and trace are obtained; never present the identity itself as trace correctness.

### B. Global endomorphism, isogeny, and degree route

This route derives the characteristic equation from degree, kernels,
separability, and possibly dual isogenies.  It overlaps the selected Hasse route
in the symbolic endomorphism representation, `deg(pi)=q`, separability and
fixed-kernel facts for `1-pi`, degree quadraticity, and kernel/degree bridges.
Dual isogenies, general kernel theorems, Weil-style degree identities, and a
restriction to torsion may remain Schoof-specific depending on the Hasse
realization.

**Cost/risk:** the highest near-term cost.  Reuse becomes attractive after the
Hasse degree seam exists, but waiting for that major development would
unnecessarily block executable Schoof's already concrete `ell=3` client.  Do
not create degree or isogeny theory in the next boundary.

### C. Specialized `ell=3` division-polynomial/root route

This route best exploits current production theorems.  The generic `psi_3`
theorem gives pointwise nonzero 3-torsion semantics, and quotient acceptance
already transports to every *supplied* ambient root/curve point.  What remains
is not merely finding one root: every nonzero 3-torsion point must be covered;
the four x-coordinates must be complete and simple (or completeness must follow
from a universal-root construction); both ordinate choices must be included;
Frobenius must preserve the curve and torsion; and the cross equations must be
identified with the affine/group equation in all ordinary and exceptional
branches.

A temporary brute-force calculation found no F11 root of
`3x^4+6x^2+6x+10` and no factorization into monic quadratics after normalizing
the leading coefficient.  This is **uncertified audit evidence only**,
consistent with irreducibility.  A certified irreducibility result could make
`F_11[x]/(psi_3)` a convenient universal x-root field, but it would not supply
the two y choices, group-law equivalence, torsion completeness, or trace
identification.  A universal-root theorem is preferable to enumerating four
separate roots only if its field and ordinate costs remain bounded.

**Cost/risk:** moderate overall and lowest overlap with undeveloped global
theory.  Select its first affine/group-law sub-boundary now, then reassess the
least expensive completeness construction.

### D. Concrete F11 extension or exhaustive verification

The certified 13-point enumeration independently proves the reference count
for this curve and hence the numerical trace residue.  It validates the
example, not Schoof's method: it does not prove that quotient predicate
acceptance entails trace congruence.  A concrete splitting-field or
degree-eight coordinate witness could check all torsion points and expose
branch behavior, but unless accompanied by certified completeness and semantic
bridges it is only another regression.  With those theorems it could certify
only the present F11/`ell=3` instance, which is acceptable as an intermediate
endpoint but must not become the generic architecture by implication.

**Cost/risk:** exhaustive base-field counting is already cheap but logically
independent; a new extension field risks exchanging matrix theory for an
equally large carrier implementation.  Use a concrete witness only if the
post-group-law audit shows that it closes completeness more cheaply than a
universal-root theorem, and label its exact instance scope.

### E. Direct symbolic quotient/divisibility route

The existing quotient equality is already the computational universal
polynomial statement in the following limited sense: PR #347 proves that
acceptance evaluates to the same cross equations at any supplied ambient root
and supplied curve ordinate under the commutative-ring homomorphism premises.
No separate remainder divisibility proof is needed merely to transport those
equations.  This makes E largely the algebraic half of C rather than an
independent classical proof.

The missing bridge is semantic: show that all classical nonzero 3-torsion
coordinates are such roots/curve points; ensure the target supports field
cancellation; turn the equations into the intended group equation, including
exceptional branches; and identify its scalar with Frobenius trace rather than
just an accepted candidate.  Quotient equality alone supplies none of these.

## Selected next implementation boundary

### Recommendation

Certify a **bounded affine/group interpretation family for the existing trace
cross equations**, followed by one conditional F11/`ell=3` composition theorem.
The exact family should say:

1. for valid affine points over the existing generic curve field, the two
   identically oriented secant cross equations, together with the explicit
   nonzero x-difference/denominator premise, imply the corresponding named
   curve-point addition equation;
2. the equal-x/opposite-y predicate implies the named infinity/opposite group
   equation under the existing affine validity hypotheses;
3. after functional instantiation/composition with quotient-coordinate
   ambient soundness, F11 candidate 2 conditionally gives that same point
   equation for **any supplied** `psi_3` root and ordinate on
   `y^2=x^3+x+6`, whenever the selected ordinary branch's denominator is
   nonzero, with the exceptional branch stated separately.

The exact sign and ordering must be copied from
`quotient-coordinate-field-cross-add-p` and proved against the existing
addition relation; it must not be reconstructed from memory.  Reuse
`books/curve/affine-distinct-x-*`, the curve-point addition/cancellation books,
`books/curve/third-division-polynomial.lisp`,
`books/schoof/quotient-coordinate-trace-predicate.lisp`, and
`books/schoof/quotient-coordinate-{semantic,ambient}-soundness.lisp` and their
included foundations.  A small production book under `books/schoof/` should
hold the generic bridge; a focused `*-regression.lisp` should compose the exact
F11 constants and exercise ordinary and exceptional orientations.

The only genuinely new mathematical context should be the field/cancellation
and nonzero-denominator hypotheses already required by affine secant addition.
If the current ambient commutative-ring seam cannot be functionally instantiated
into the existing curve field without a narrow compatibility lemma, add only
that named preservation lemma.  Do not add a root, extension, closure, module,
matrix, isogeny, or degree context.

### Why this boundary is smallest

It closes a known semantic gap immediately downstream of certified executable
acceptance; is reusable for later primes; and tests the exact signs,
denominators, and exceptional spelling before choosing an ambient carrier.
Unlike fixed `2x2` Cayley--Hamilton, it does not hide determinant and trace
identification.  Unlike an extension field, it does not construct a universe
before knowing which completeness theorem is necessary.  Unlike exhaustive
point counting, it proves a component of the method rather than only the
answer.

### Stop conditions and limits

Stop and return to audit if the family requires any of the following:

* constructing or enumerating `E[3]`, roots, or an algebraic closure;
* proving `psi_3` square-free/irreducible or building an extension field;
* introducing vector spaces, matrices, Cayley--Hamilton, isogenies, or degree;
* proving all Schoof exceptional branches rather than the predicates already
  represented; or
* weakening the theorem by dropping the denominator premise.

The result would prove that the already transported equations have the claimed
affine/group meaning, and would give a conditional per-root F11 theorem.  It
would **not** prove root or torsion existence, completeness of `E[3]`, semantic
nonzeroness of the denominator for every root, Frobenius trace/determinant
identification, a trace congruence, the numerical point count by Schoof, CRT,
or Hasse.  After certification, the next audit point is a bounded choice between
a universal-root/square-free completeness theorem and a concrete certified F11
torsion witness; the matrix and global-degree routes remain deferred unless
that evidence changes their relative cost.
