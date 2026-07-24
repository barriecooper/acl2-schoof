# ACL2 Hasse--Schoof

This repository is a certified foundation for a future Manin-style proof of
Hasse's theorem and for Schoof point counting on short Weierstrass curves.
Neither Hasse's theorem nor Schoof's algorithm is complete here, and the
repository does not yet implement arbitrary extension fields.

The development has grown beyond a small polynomial pilot.  Its certified
foundation includes an abstract field kernel, a constrained-modulus PFIELD
adapter, named concrete F2 and F7 fields, canonical generic polynomial
normalization and evaluation, addition, subtraction, scaling, multiplication,
constant embedding and powers, degree and leading coefficients, product
leading-term and no-zero-divisor consequences, monomials and shifts, one-step
leading-term cancellation, and recursive quotient/remainder division with
reconstruction and a final remainder-degree bound. It also includes generic
polynomial congruence, Euclidean division and remainder, divisor-first
divisibility, raw Euclidean GCD and monic GCD post-processing, raw XGCD with an
unconditional Bezout identity, monic XGCD with an unconditional monic Bezout
identity, and the XGCD-to-remainder bridge. The repository also contains the
concrete F11 golden-curve fixture.

GPOLY algorithms are generic certified definitions over constrained field
operations.  PFIELD is a constrained-modulus adapter, not ordinary arithmetic
for one named runtime modulus.  F2, F7, and F11 are named executable concrete
instances where the corresponding generated operations have been supplied.
At present the recursive division algorithm itself is certified generically;
a concrete F7 one-step boundary was not retained after its semantic theorem
group certified experimentally because the existing F7 inverse/division guard
contract blocked explicit guard verification. Recursive F7 divmod is postponed.

The total generic `POLY-MODULAR-INVERSE` candidate is defined and certified. It
reduces the first monic-XGCD coefficient and is conditionally correct when the
monic GCD is polynomial one: the product reduces to the remainder of polynomial
one. That remainder is literally polynomial one only for a nonempty normalized
positive-degree modulus; nonzero constant moduli instead have zero-remainder
semantics.

The next dependency chain is documentation and CI maintenance; concrete
named-field instantiation and guard resolution; a proof that irreducibility
implies monic GCD one; executable irreducibility certificates for selected
defining polynomials; irreducible-modulus quotient fields for coefficient-field
extensions; and, separately, general polynomial quotient rings for Schoof
division-polynomial calculations. Elliptic-curve, Frobenius, torsion, and
bounded CRT layers follow. The quotient-field moduli must be irreducible,
whereas the moduli used by the general Schoof quotient rings need not be.

Genuinely unfinished work includes the irreducibility bridge and certificates,
concrete recursive named-field instances through modular inversion,
quotient-field laws, general quotient-ring operations not already certified,
extension fields, elliptic curves, Hasse, Frobenius, division polynomials,
Schoof residues, and bounded CRT reconstruction. See
`docs/obligations.md` for the authoritative detailed status rather than treating
this overview as an obligation ledger.

## Reproduce

On Debian/Ubuntu install `git make perl sbcl`, then run:

```sh
make setup
make check-trust
make certify-one BOOK=books/polynomial/generic/division.lisp
make certify-one BOOK=books/polynomial/generic/pfield-instance.lisp
make certify
make test
```

Setup installs ACL2 8.6 under ignored `.deps/`, builds it with SBCL, and uses
that checkout's Community Books and `books/build/cert.pl`. Certification logs
live in `.deps/logs/`; initial setup requires network access and substantial
disk space.

With Docker:

```sh
docker build -t acl2-schoof .
docker run --rm acl2-schoof
```

`books/` contains project books, `tests/` executable certification tests,
`scripts/` the reproducible driver, and `docs/` the design and proof ledger.
To add a book, include only direct prerequisites, add it to `books/top.lisp`,
certify it with `make certify-one BOOK=books/path/name.lisp`, and then run the
full suite.

The zero polynomial is `nil`; coefficients are stored in ascending degree and
canonical inputs have no trailing zero.  The trust policy forbids proof
bypasses, axioms, trust tags, and raw Lisp. `make check-trust` conservatively
scans comments and strings as well as executable forms. Generated certificates,
logs, and `.deps/` contents are build artifacts and are not tracked.


## Polynomial architecture

GPOLY is authoritative for new polynomial algebra. HS/PFIELD polynomials remain
a legacy/root-count bridge unless an explicit bridge requires them; new gcd,
derivative, modular-reduction, quotient-ring, and extension-field developments
should not be duplicated across both stacks. The first executable Schoof path
may use a named prime field, while arbitrary finite-field execution is a later
architectural phase.
