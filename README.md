# ACL2 Hasse--Schoof

This is a working ACL2 formalisation repository for a Manin-style proof of
Hasse's theorem and, later, Schoof point counting for short Weierstrass curves
over prime fields. The currently certified mathematical scope is the small
prime-field polynomial pilot; Hasse's theorem is **not** yet claimed. The
`main` branch must always pass certification.

## Clean-checkout verification

On Debian/Ubuntu install `git make perl sbcl`, then run:

```sh
make setup
make check-trust
make certify
make test
```

Setup clones the official ACL2 `8.6` tag into ignored `.deps/`, builds it with
SBCL, and uses that checkout's Community Books and `books/build/cert.pl`.
Certification logs live in `.deps/logs/`. The first setup requires network
access and substantial disk space.

With Docker:

```sh
docker build -t acl2-schoof .
docker run --rm acl2-schoof
```

## Packages and books

Project definitions and theorems live in package `HS`. The companion
`books/package.acl2` creates it as a certification portcullis command, while
`books/package.lisp` is the single Community Books prime-field dependency
boundary. `HS` has an explicit import list and does not import field operations;
project sources use qualified names such as `PFIELD::add` and `PFIELD::mul`.

`books/` contains project books, `tests/` executable certification tests,
`scripts/` the reproducible driver, and `docs/` the design and proof ledger. To
add a book, include only its direct prerequisites, add it to `books/top.lisp`,
and first certify it alone:

```sh
make certify-one BOOK=books/path/name.lisp
```

Then run `make check-trust`, `make certify`, and `make test`. Every pull request
must preserve all three checks and the `main` branch certification invariant.

The zero polynomial is `nil`; coefficients are ascending and canonical inputs
have no trailing zero. The trust policy categorically forbids proof bypasses,
axioms, trust tags, and raw Lisp. `make check-trust` conservatively scans even
comments and strings. Current deeper proof obligations are tracked rather than
admitted; see `docs/obligations.md`.

Generated ACL2 certificates, portcullises, compiled files, and temporary build
files are ignored. `make clean` removes project-generated artifacts; downloaded
ACL2 and Community Books files remain under ignored `.deps/`.
