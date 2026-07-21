#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Deliberately conservative: comments and strings are scanned too.
pat='[(][[:space:]]*(skip-proofs|defaxiom|defttag|set-raw-mode(-on)?|progn!)([[:space:])]|$)'
set +e
grep -E -r -n -i --include='*.lisp' "$pat" books tests
rc=$?
set -e
case "$rc" in
  0)
    echo 'forbidden ACL2 trust-expanding form found' >&2
    exit 1
    ;;
  1)
    echo 'trust scan passed (conservative: comments and strings are included)'
    ;;
  *)
    echo "trust scanner failed (grep exit status $rc)" >&2
    exit "$rc"
    ;;
esac
