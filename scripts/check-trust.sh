#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Deliberately conservative: comments and strings are scanned too.
pat='[(][[:space:]]*(skip-proofs|set-ld-skip-proofsp|defaxiom|defttag|set-raw-mode(-(on|off))?!?|progn!|defattach(!|-system)?|include-raw)([[:space:])]|$)'
if (($# == 0)); then
  paths=(books tests)
else
  paths=("$@")
fi
set +e
grep -E -r -n -i --include='*.lisp' --include='*.acl2' "$pat" "${paths[@]}"
rc=$?
set -e
case "$rc" in
  0)
    echo 'forbidden ACL2 trust-expanding form found' >&2
    exit 1
    ;;
  1)
    echo 'trust scan passed (*.lisp and *.acl2; comments and strings included)'
    ;;
  *)
    echo "trust scanner failed (grep exit status $rc)" >&2
    exit "$rc"
    ;;
esac
