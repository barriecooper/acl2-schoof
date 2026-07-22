#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

printf '(in-package "ACL2")\n' >"$tmp/clean.lisp"
printf '(value-triple :clean)\n' >"$tmp/clean.acl2"
"$root/scripts/check-trust.sh" "$tmp" >/dev/null

# Construct the spelling so this regression remains outside any future scan
# of shell source itself.
printf '(%s foo bar)\n' 'defattach' >"$tmp/forbidden.acl2"
if "$root/scripts/check-trust.sh" "$tmp" >/dev/null 2>&1; then
  echo 'trust scanner missed a forbidden form in an .acl2 file' >&2
  exit 1
fi
echo 'trust scanner regression passed'
