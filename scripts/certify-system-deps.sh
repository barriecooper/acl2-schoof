#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
acl2="$root/.deps/acl2"
books="$acl2/books"
book="workshops/2022/gamboa-primitive-roots/pfield-polynomial"

test -x "$acl2/saved_acl2" || {
  echo "ACL2 executable is missing: $acl2/saved_acl2" >&2
  exit 1
}

# cert.pl's generated makefile depends on feature/version dependency files.
# A fresh ACL2 source checkout does not contain these generated files.
if [[ ! -f "$books/build/acl2-version.certdep" ]]; then
  echo "Preparing Community Books certification metadata"
  mkdir -p "$root/.deps/logs"
  (
    cd "$books/build"
    ../../saved_acl2 < cert_features.lsp \
      > "$root/.deps/logs/community-books-features.log" 2>&1
  )
fi

echo "Ensuring certified external Community Book: $book.lisp"
# cert.pl recursively follows this book's ordinary and local include-books,
# builds only that required chain, and does no certification work when all
# certificates are already current.
(
  cd "$books"
  perl build/cert.pl --acl2 ../saved_acl2 "$book.lisp"
)
