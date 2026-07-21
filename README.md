# ACL2 Hasse--Schoof

This repository is a certifying foundation for a formal Manin-style proof of
Hasse's theorem, followed by Schoof point counting, for short Weierstrass curves
over prime fields.  The present milestone is intentionally only a small
polynomial pilot; Hasse's theorem is **not** claimed.

## Reproduce

On Debian/Ubuntu install `git make perl sbcl`, then run:

```sh
make setup
make check-trust
make certify
make test
make certify-one BOOK=books/polynomial/eval.lisp
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

`books/` contains the project books, `tests/` executable certification tests,
`scripts/` the reproducible driver, and `docs/` the design and proof ledger.
To add a book, include only its direct prerequisites, add it to `books/top.lisp`,
first run `make certify-one BOOK=books/path/name.lisp`, then run the full suite.

The zero polynomial is `nil`; coefficients are ascending and canonical inputs
have no trailing zero. The trust policy categorically forbids proof bypasses,
axioms, trust tags, and raw Lisp. `make check-trust` conservatively scans even
comments and strings. Current deeper proof obligations are tracked rather than
admitted; see `docs/obligations.md`.

## Last bootstrap verification

On 2026-07-21, after building ACL2 8.6 with SBCL, all acceptance commands
completed successfully with the shown process statuses:

```text
make setup        # exit 0
make check-trust  # exit 0
make certify      # exit 0
make test         # exit 0
```

The successful `make certify` run certified `books/top.lisp` and its project
dependencies; the successful `make test` run certified `tests/smoke.lisp`.
The complete driver logs contained no ACL2 failure markers. Generated
certificates are build artifacts and are not tracked.
