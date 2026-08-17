# Proof plan

This document owns forward mathematical dependency order. Current theorem-level
status is in the [obligation ledger](obligations.md); stable design is in
[architecture](architecture.md).

## Destinations and shared seam

The long-term destinations are a Manin-style proof of Hasse's theorem and an
executable, certified Schoof point-counting algorithm. They share the generic
field, polynomial, curve, finite-cardinality, and Frobenius foundations, but
neither downstream track is a prerequisite for the other.

The Hasse track uses the adopted hybrid representation: canonical symbolic
maps over a narrow rank-two short-Weierstrass function field for equality,
composition, separability, and degree, and a separate geometric point seam for
Frobenius fixedness and the `ker(1-pi)`/degree bridge. The weakest sufficient
point carrier remains to be selected when that bridge is realized.

The Schoof track uses dense ascending univariate division-polynomial data with
the conventional `2y` factor removed from even indices. Its immediate forward
order is governed by the
[arbitrary-field executable architecture audit](audits/arbitrary-field-executable-schoof-architecture.md).
That audit selects a staged hybrid: an explicit run-time polynomial-basis
finite-field descriptor family supplies the public executable input, while a
fixed-descriptor wrapper functionally instantiates the existing constrained
field, polynomial, curve, and group mathematics.  “Arbitrary finite field” no
longer means only a separately certified nullary operation instance.

The runtime prerequisite now also has certified total runtime-`p` coefficient
inversion, reusing PFIELD inversion, with two-sided laws under primality of the
effective modulus and nonzero fixed input. Malformed moduli retain effective
modulus 2, while composites execute without a field claim. The earlier stages are: runtime-`p` representation
and radix coding in `runtime-p-representation.lisp`; coefficient commutative-
ring laws in `runtime-p-algebra.lisp`; normalized polynomial commutative-ring
laws in `runtime-p-polynomial-algebra.lisp`; the canonical zero-collapsing
monomial plus total degree/leading-coefficient seam in
`runtime-p-polynomial-monomial-degree.lisp`; the inverse-free monic product-
leading-term calculation in
`runtime-p-monic-product-leading-term.lisp`; its arbitrary canonical-multiplier
generalization in `runtime-p-monic-product-arbitrary-multiplier.lisp`; exact active-step reconstruction
with strict normalized-length and degree decrease in
`runtime-p-active-monic-subtraction.lisp`; and the transparent, total,
guard-verified one-step monic reduction interface in
`runtime-p-monic-division-step.lisp`; and structural recursive monic divmod,
canonical results, reconstruction, and strict monic final bound in
`runtime-p-monic-divmod.lisp`. Its length measure supersedes the rejected fuel
design, so no fuel-adequacy obligation applies. Exact fixed-PFIELD monic
divmod, quotient, and remainder correspondence is also certified. The
descriptor representation slice is described below; reduced-operation laws
and field semantics remain subsequent open boundaries. The certified divmod is unconditional modular-ring execution and
makes no claim of descriptor or field validity.

The descriptor representation, execution, and coding slice is certified:
polynomial-basis descriptor shape/fixing, element representation/fixing/equality,
add/neg/mul execution and closure, fixed-width vector round trips, rank/unrank
bijection, exhaustive duplicate-free carrier, and exact `p^m` representation
cardinality.  Runtime monic-remainder compatibility with polynomial addition, negation, and
multiplication and descriptor add/neg/sub/mul fixer congruence are certified.
The complete unconditional commutative quotient-ring laws are now certified;
this boundary was not needed by the earlier representation-only coding results.  Focused prime,
composite, reducible-modulus, and malformed-input regressions are certified.
This reduced-ring/representation boundary still does not add polynomial-basis
inverse, claim descriptor field laws, instantiate `GFIELD`, or decide logical
field validity. The coefficient inverse does not change those facts.

Descriptor assurance separates an executable structural predicate from a
logical field-validity predicate requiring primality, positive extension
degree, correct modulus degree, and irreducibility.  A certified executable
validator is optional future work.  The subsequent order is:

1. polynomial-basis inversion and the prime-plus-irreducible logical field-validity bridge, followed by the descriptor field-law
   bridge and fixed-context field correspondence, including characteristic/order and fixed-descriptor functional instances;
2. the runtime short-curve bridge for descriptor-threaded `A,B`, discriminant,
   point fixing, and fixed-symbol correspondence;
3. descriptor/curve-threaded runtime-`ell` division-polynomial and quotient
   trace execution, including bounded candidate search and exhaustive
   ordinary/exceptional branch dispatch;
4. generic cardinality-`q` Frobenius and torsion semantics proving that the
   accepted residue is the cardinality-defined trace modulo `ell`; and
5. auxiliary-prime accumulation, centered CRT, Hasse uniqueness, and final
   composition with the independently specified rational-point cardinality.

The older specialized sequence is retained below as historical/detail context,
not as the controlling forward route:

1. Continue the reusable finite-field instantiation seam identified by the
   post-PR #350 route audit.  Finite-field-prefixed divisibility, the Euclidean
   remainder step, raw Euclidean GCD computation, monic normalization, and the
   complete monic common-divisor/greatestness package, raw XGCD with its
   unconditional Bézout identity, and monic XGCD with its unconditional
   scaled Bézout identity, and reduction of the first monic-XGCD coefficient
   modulo the second input are certified.  The total finite-field modular
   inverse candidate and its conditional two-sided reduced-ring correctness
   under monic GCD one are also certified.  This complete boundary is now
   transported into the production F11 representation, reusing its sole
   divmod/remainder implementation.  Monic normalization now preserves degree
   generically for nonzero polynomials, and the generic and finite-field-
   prefixed logical interfaces certify that reducibility yields a monic factor
   of positive degree at most half the input degree; absence of such a factor
   implies irreducibility.  This is logical theory, not an executable test.
   Continue the general Schoof quotient-ring route, which does not require
   division polynomials to be irreducible.  If an executable irreducibility
   client is later required, first audit a scalable method; Rabin-style
   Frobenius/GCD testing is a candidate, not a certified or selected result.
   The concrete F11 quartic root field remains an optional specialised
   regression or bounded classical witness, not the arbitrary-field execution
   architecture.  Any later root-field experiment must keep root and ordinate
   existence, cancellation, and base embedding explicit.
2. Supply the remaining classical `E[3]` coverage needed to turn the
   conditional point equation into a statement about every nonzero 3-torsion
   point, then identify the equation's scalar as the actual Frobenius trace
   modulo 3.  Completeness, square-freeness or a universal-root substitute,
   Frobenius preservation, and trace/determinant identification must be
   explicit.  A general algebraic closure and Cayley--Hamilton development are
   not independently on executable Schoof's critical path.
3. Generalize to enough torsion primes and certify the next required executable
   client.  No `ell=5` client is currently certified.
4. Certify enough correct residues that their modulus product exceeds the Hasse
   uniqueness bound.  Modulus 3 alone is insufficient for F11; numerically
   `3*5=15 > 4*sqrt(11)`, but this does not certify either residue's classical
   correctness or an `ell=5` implementation.
5. Reconstruct the unique trace in the Hasse interval by bounded CRT.
6. Compose the result into final point-count correctness and the executable
   Schoof boundary.

The generic and F11 generated-table, relational-sequence, uniqueness, and
all-index evaluator correspondence is certified. Cardinality-based Frobenius must use
certified actual cardinality and compatible characteristic/prime-power
metadata, never merely `field-frobenius-exponent`.

## Hasse dependency order

1. Stage the pure discriminant argument behind explicit abstract
   endomorphism/positive-degree premises, without claiming Hasse or treating a
   false context guard as a realization.
2. Build the narrow rank-two symbolic map fragment, beginning with canonical
   map equality and `deg(pi)=q`.
3. Realize the fixed-kernel/base-point and separable-degree bridge over the
   weakest adequate geometric carrier.
4. Instantiate the arithmetic consumer to derive the public Hasse inequality.

## Completion criteria

A phase is complete only when its registered books certify under repository
trust policy and the obligation ledger records its remaining dependencies.
Guard verification and concrete evaluation are execution evidence, not
semantic correspondence. Chronological completion narratives and proof-debug
history belong in commits, pull requests, and explicitly historical audits.
