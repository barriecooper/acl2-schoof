#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd); cd "$root"
book=${1:?book required}; book=${book%.lisp}
test -f "$book.lisp" || { echo "no such book: $book.lisp" >&2; exit 2; }
mkdir -p .deps/logs
log=".deps/logs/$(echo "$book" | tr / _).log"
export ACL2_SYSTEM_BOOKS="$root/.deps/acl2/books"
set +e
perl .deps/acl2/books/build/cert.pl --acl2 .deps/acl2/saved_acl2 "$book.lisp" >"$log" 2>&1
rc=$?; set -e
if ((rc)); then
  echo "certification failed; markers:" >&2
  {
    grep -E -i 'ACL2 Error|FAILED|HARD ACL2 ERROR' "$log" || true
    grep -F '********' "$log" || true
  } | tail -20 >&2
  echo "---- tail of $log ----" >&2; tail -80 "$log" >&2; exit "$rc"
fi
tail -8 "$log"
