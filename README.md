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
reconstruction and a final remainder-degree bound.  The repository also
contains the concrete F11 golden-curve fixture.

GPOLY algorithms are generic certified definitions over constrained field
operations.  PFIELD is a constrained-modulus adapter, not ordinary arithmetic
for one named runtime modulus.  F2, F7, and F11 are named executable concrete
instances where the corresponding generated operations have been supplied.
At present the recursive division algorithm itself is certified generically;
a concrete F7 one-step boundary was not retained after its semantic theorem
group certified experimentally because the existing F7 inverse/division guard
contract blocked explicit guard verification. Recursive F7 divmod is postponed.

Generic modular reduction is certified. The next mathematical milestone is
generic polynomial congruence and its addition/multiplication compatibility.
Still open are polynomial gcd and extended gcd, quotient/remainder uniqueness,
irreducibility, arbitrary extension fields, rational functions, generic curve
operations, Hasse, division polynomials, CRT trace reconstruction, and Schoof
trace computation.  These are tracked in `docs/obligations.md`; the full
Euclidean-polynomial milestone is not complete.

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
