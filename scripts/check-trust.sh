#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Deliberately conservative: comments and strings are scanned too.
pat='[(][[:space:]]*(skip-proofs|defaxiom|defttag|set-raw-mode(-on)?|progn!)([[:space:])]|$)'
if rg -n -i --glob '*.lisp' "$pat" books tests; then
  echo 'forbidden ACL2 trust-expanding form found' >&2; exit 1
fi
echo 'trust scan passed (conservative: comments and strings are included)'
