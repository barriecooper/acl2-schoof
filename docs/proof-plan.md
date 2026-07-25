# Proof plan

## Immediate F7 extension-field dependency

The post-monic-GCD reconnaissance is in
`f7-extension-field-reconnaissance.md`.  The generic raw XGCD, monic scaling,
reduction bridge, and modular-inverse candidate are already certified.  The
next implementation unit is only the concrete F7 raw XGCD instance and its
projection, canonicality, unconditional Bezout, guard, and exact-execution
package.  Quotient operations, irreducibility, and field laws remain open and
must not be folded into that PR.

Each milestone must remain independently certifiable.

The current executable named-field development is over prime fields `F_p`; the
long-term target is arbitrary finite fields `F_q`, where `q = p^n`. Generic
polynomial development is active in the authoritative GFIELD/GPOLY stack, while
concrete recursive named-field instantiation still requires the documented
guard-contract resolution. A milestone is complete only when its stated
ACL2 obligations are genuinely proved and certified.

1. Prime-field polynomial arithmetic, canonical forms, evaluation, and degree
   (current certified implementation), plus the completed abstract field
   kernel and its completed certified fixed-prime PFIELD adapter.  The generic dense-polynomial foundation (representation, normalization, and
   evaluation), its generic additive structure (addition, negation, and
   subtraction), generic canonical scalar multiplication, and the canonical
   polynomial multiplication definition with evaluation semantics are also
   complete.  Generic multiplication is now algebraically complete: its
   commutativity, associativity, and both distributive laws are certified and
   transported through PFIELD to executable F_7.  The explicit canonical
   constant embedding and compact commutative-ring consolidation are complete.
   Reusable natural exponentiation by squaring is complete: a linear proof
   specification, logarithmic executable algorithm, explicit `nfix` behavior,
   generic laws, canonical polynomial instance, and evaluation semantics are
   certified for reuse by fields and later extension fields.  The executable
   F_11 golden field/polynomial fixture for `y^2 = x^3 + x + 6` is complete.
   Generic canonical polynomial degree and leading coefficient, including the
   PFIELD adapter and executable F_7 instances, are complete.  The structural
   leading-term group is also complete for nonempty canonical factors: raw
   multiplication is canonical, normalization preserves the full convolution,
   leading coefficients multiply in operand order, degrees add, and products
   are nonzero.  This uses the field no-zero-divisor law and raw length theorem,
   not evaluation extensionality.  The total, canonical monomial and natural
   degree-shift foundation is also certified, including degree and leading-
   coefficient laws and explicit `nfix` behavior.  The maintained division contract, one-step cancellation, and recursive generic
   division are certified, including reconstruction and the final strict
   remainder-degree bound. Generic modular reduction and congruence are also
   certified, including compatibility with addition, negation, subtraction,
   and multiplication. The existing public remainder is now explicitly
   packaged as the sole total canonical-representative boundary, including
   normalized fixed point and exact zero, constant, polynomial-one, malformed,
   noncanonical, and positive-degree semantics. It is shared by reducible
   Schoof quotients and irreducible quotients later promoted to fields. Four
   transparent reduced representative operations now compose addition,
   negation, subtraction, or multiplication with that remainder. Their guards,
   structural closure, exact total modulus semantics, and representative
   invariance are certified, with concrete F7 executions. They are not quotient
   objects and do not establish quotient-ring laws, reduced-one unit laws,
   irreducibility, or field promotion. Quotient equality is now explicitly
   packaged as equality of canonical remainders, with equivalence,
   normalization/remainder invariance, fixed-representative collapse, exact
   modulus boundaries, and literal equality compatibility for all four reduced
   operations. The complete quotient-ring and unit-law packages remain open.
   The Euclidean remainder step now has a
   certified normalized-divisor-length descent theorem. The raw
   `POLY-EUCLIDEAN-GCD`
   recursion is defined and certified on `(len (normalize second))`: it stops at an
   empty normalized second argument, otherwise transitions from `(a,b)` to
   `(b,poly-remainder(a,b))`, and has certified canonical output. It is not
   monic. Generic
   divisor-first divisibility is now decidable by canonical zero remainder,
   and common divisors are certified invariant across one Euclidean step using
   reconstruction and congruence algebra. Independent Euclidean inductions now
   certify both that the recursive result divides both inputs and that every
   common divisor divides the result. The greatestness induction retains the
   arbitrary divisor, uses normalization invariance at the base, and uses the
   Euclidean-step equivalence as the complete recursive algebraic bridge.
   These directions are now packaged under a transparent public raw-gcd
   correctness interface by direct theorem composition, without new induction,
   recursion, or division reasoning. Transparent generic monic normalization
   is now structurally certified: normalized zero maps explicitly to `nil`,
   nonzero input is inverse-leading-coefficient scaled, zero/nonzero status is
   exact, output is canonical and normalized, and its leading coefficient is
   respectively field zero or field one. Divisibility is now certified
   invariant when only the dividend is scaled by a fixed nonzero field scalar,
   using multiplication closure, constant multiplication, nested scaling, and
   the field inverse law. This theorem is total over malformed and
   noncanonical representations; its nonzero hypothesis is necessary. The
   divisor-scaling invariance is now certified by mutual divisibility and
   transitivity, with inverse reasoning inherited from dividend scaling. The
   unconditional dividend- and divisor-position monic-normalization
   equivalences are now certified by explicit normalized-zero branches and the
   two scaling laws, without induction or division expansion. The transparent
   `POLY-MONIC-EUCLIDEAN-GCD` wrapper is now certified both structurally and
   mathematically: it divides both inputs, and every common divisor divides it.
   Correctness is transported compositionally through divisor-position and
   dividend-position monic-normalization invariance, without recursion,
   induction, inverse reasoning, or division expansion. Raw representatives
   and total malformed-input semantics are preserved. This does not prove
   uniqueness and introduces neither associate theory nor a monic predicate.
   Raw generic XGCD and its monic post-processing are now certified.  The
   nonrecursive `POLY-MONIC-EXTENDED-EUCLIDEAN-GCD` scales both raw Bézout
   coefficients by the inverse leading coefficient, agrees exactly with
   `POLY-MONIC-EUCLIDEAN-GCD`, and unconditionally reconstructs that monic gcd.
   The first monic Bézout coefficient is now connected to public reduction:
   under gcd one, its product with the first input has the same remainder as
   `POLYNOMIAL-ONE` modulo the second input, and this specializes to literal
   one for a nonempty normalized second input of positive degree. Constant
   moduli deliberately retain their zero-remainder semantics.
   Normalized-monic-gcd uniqueness remains optional unless a downstream
   algorithm requires equality rather than the certified divisibility interface.
   The total nonrecursive `POLY-MODULAR-INVERSE` wrapper is now certified.  It
   returns the reduced first monic-XGCD coefficient, is canonical and
   normalized for every ACL2 input, and is conditionally inverse-correct when
   the monic gcd is one; normalized positive-degree moduli specialize the
   product remainder to literal one.  Zero-normalized moduli retain the
   normalized coefficient and nonzero constants return zero.
   Both generic reduced-product orientations are now literally reduced one
   under that exact condition; one is the existing Bézout/remainder theorem in
   reduced notation and the other follows by commutativity.  The converse unit
   characterization, uniqueness, irreducibility implying monic gcd one,
   quotient fields, concrete
   polynomial-field instances, and extension fields remain open. Later power uses include
   extension-field arithmetic,
   Frobenius, derived finite-field inversion, irreducibility tests,
   elliptic-curve scalar/endomorphism calculations, and Schoof computations.
   The executable-instantiation policy is
   recorded in `executable-instantiation.md`: abstract algorithms, ordinary
   executable concrete definitions, and certified correctness bridges are all
   required for future computational layers.  Concrete generated division, extension fields, and arbitrary finite-field
   execution are not complete.
2. Documentation and CI maintenance, then concrete named-field instantiation
   through modular inversion and resolution of its inverse/division guards.
3. Use the certified irreducibility-to-monic-GCD-one bridge and provide further
   executable irreducibility certificates for selected defining polynomials.
4. Build quotient fields modulo those certified irreducible polynomials for
   coefficient-field extensions. Separately, build general polynomial quotient
   rings for Schoof division-polynomial calculations; those moduli need not be
   irreducible.
5. Certified extension fields and generic polynomial instances, then rational
   functions over `F_q(t)` and well-defined operations.
6. Valuation at infinity, including product and cancellation laws.
7. Generic twisted elliptic curve over an abstract finite field and its
   rational-function group operations.
8. Frobenius/scalar-multiplication maps and their quadratic degree sequence.
9. Point-count connection, torsion kernels, and necessary separability results.
10. Integer quadratic conclusion yielding Hasse's bound.
11. Division polynomials and quotient-coordinate algebra over the general
    quotient rings.
12. Schoof trace residues and certified bounded CRT reconstruction.


## Generic recursive division (certified)

`books/polynomial/generic/division.lisp` certifies `POLY-DIVMOD-CORE` and the total `(mv q r)` public `POLY-DIVMOD`.  Canonical remainder length is the measure, the one-step decrease theorem supplies termination, and an accumulator invariant supplies normalized reconstruction without evaluation extensionality.  The final remainder is zero or strictly below the normalized nonzero divisor.  Guards are verified separately. No executable boundary or concrete PFIELD/F7 recursive
instance is added; concrete generated division through modular inversion and
uniqueness remain open. Generic divisibility, GCD, XGCD, and modular inversion
are defined and certified in their later books.

## Architecture and top-down interfaces

GPOLY is authoritative for new polynomial algebra. The older HS/PFIELD
polynomial stack remains a legacy/root-count bridge unless a specific bridge
requires it; gcd, derivative, quotient-ring, and
extension-field work should not be independently duplicated in both stacks.
The raw generic Euclidean computation now uses the certified normalized-divisor-
length descent and returns a canonical, potentially non-monic result. The
generic divisibility interface and both directions of common-divisor invariance
across a remainder step are now certified, unconditionally including
zero-normalized inputs. Raw algebraic gcd correctness is now exposed by the
public `POLY-COMMON-DIVISOR-P` interface: the computed result is a common
divisor, and every common divisor divides it. The raw result remains canonical
but potentially non-monic. Monic normalization's representation,
leading-coefficient, and divisibility interfaces are certified, as is the
transparent monic-gcd wrapper. Its common-divisor and greatestness correctness
is now certified compositionally. Raw XGCD and unconditional Bezout, monic XGCD
and monic Bezout, the XGCD remainder bridge, and the total conditional
`POLY-MODULAR-INVERSE` candidate are certified. The downstream composition
book proves both reduced unit laws for every nonzero remainder-fixed
representative modulo an irreducible polynomial, using only the certified
GCD-one bridge and existing conditional inverse laws. Selected constants,
`x`, and `1+x` modulo the certified irreducible F7 polynomial `x^2+1` are
regressions, not a quotient-field API. Literal-one inverse correctness requires
a normalized positive-degree modulus; constant moduli retain their
zero-remainder semantics. The presentation-specific `F7X2` carrier boundary
is now certified: arbitrary ACL2 objects reduce to normalized F7 polynomials
of degree below two, and every recognized carrier value is uniquely
reconstructible from its constant and linear F7 coefficients. Recognized-value
equality is ordinary ACL2 equality and is coefficient-extensional; noncanonical
inputs are compared only after `F7X2-FIX`. The two addition projection formulas
are now certified unconditionally for arbitrary ACL2 operands by fixing and
reconstructing both operands and applying the bounded normalized
two-coefficient addition bridge. Recursive polynomial division remains
encapsulated. The six negation, subtraction, and multiplication projection
formulas, general ring laws, inversion, and field promotion remain open. Extension operations, field laws, and
a GFIELD instance remain open, as do elliptic-curve arithmetic, division polynomials, Hasse
theory, and Schoof. No concrete
PFIELD/F7 gcd API was introduced. The complete concrete F7 one-step semantic
theorem layer, including the strict length-decrease prerequisite, is certified;
recursive concrete F7 divmod and all projections remain postponed. The first executable
Schoof path may target a named prime field; arbitrary finite-field execution is
a later architectural phase.

The maintained next dependency chain is documentation and CI maintenance;
concrete named-field instantiation and guard resolution; executable irreducibility certificates for
selected defining polynomials; irreducible-modulus quotient fields for
coefficient extensions; general quotient rings, separately, for Schoof
division-polynomial calculations; and then elliptic-curve, Frobenius, torsion,
and bounded CRT layers. The detailed status remains authoritative in
`obligations.md`. In particular, further executable irreducibility
certification, quotient-field laws, unfinished
general quotient-ring operations, extension fields, curves, Hasse, Frobenius,
division polynomials, Schoof residues, and CRT reconstruction remain open.

Top-down planning requires interfaces for base-to-extension-field embedding,
q-power Frobenius, Frobenius preservation of the curve, Frobenius fixed points
corresponding to rational points, finite splitting certificates, fibre-to-kernel
completeness, and endomorphism degree and separability. These are requirements,
not imported code or claims of proof.

## Concrete F7 monic-divisibility prerequisite

The F7 divisor-first divisibility and common-divisor predicates accompany certified transport through `F7-POLY-MONIC-NORMALIZE` in either argument.  The field interface consists of focused addition, multiplication, and total-inverse fixing congruences.  Concrete raw F7 GCD is retained as an ordinary guard-verified recursion with a direct certified instance of the generic raw common-divisor specification and exact total executions; its representative is intentionally not rescaled and can depend on input order.  Concrete monic F7 GCD is complete as one guard-verified, nonrecursive post-processing call around that raw runtime.  Concrete monic F7 XGCD is also complete: its single transparent wrapper calls raw XGCD once and uniformly scales the gcd and both Bézout coefficients by the inverse raw leading coefficient.  The representative raw gcds `(6 6)` and `(1 1)` both project to monic `(1 1)`, while the scaled coefficients retain their order-sensitive witnesses.  Concrete F7 polynomial modular inverse is also complete as one monic-XGCD call followed by the existing remainder operation, with conditional correctness under monic GCD one. Monic-GCD uniqueness, irreducible-implies-coprime, quotient/extension fields, curves, Hasse theory, and Schoof remain future work.


The generic logical root boundary now proves that a degree-two polynomial with
no coefficient-field root is irreducible. This theorem remains logical and
field-generic. The concrete F7 specialization certifies `x^2+1` by exhausting
exactly the seven coefficient-field elements, not polynomial factors or
quotient elements. Irreducible-implies-coprime, construction of
`F7[x]/(x^2+1)`, and its promotion to a field remain open.
