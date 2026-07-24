#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d)
generated="$root/.deps/check-execution-policy-regression-$$"
trap 'rm -rf "$tmp" "$generated"' EXIT

printf '(value-triple :clean)\n' >"$tmp/clean.lisp"
"$root/scripts/check-execution-policy.sh" "$tmp" >/dev/null

check_rejected() {
  local spelling=$1 file="$tmp/fixture-$2.lisp" output
  printf '(%s :logic nil :exec nil)\n' "$spelling" >"$file"
  if output=$("$root/scripts/check-execution-policy.sh" "$file" 2>&1); then
    echo "execution-policy scanner accepted forbidden form: $spelling" >&2
    exit 1
  fi
  [[ $output == *"$file:1:"* && ${output,,} == *"${spelling,,}"* ]] || {
    echo "execution-policy diagnostic omitted file or construct: $output" >&2
    exit 1
  }
}

check_rejected mbe mbe
check_rejected defexec defexec
check_rejected MbE mixed-case
check_rejected ACL2::MBE qualified-mbe
check_rejected acl2::defexec qualified-defexec

mkdir -p "$generated"
printf '(%s :logic nil :exec nil)\n' mbe >"$generated/output.lisp"
"$root/scripts/check-execution-policy.sh" >/dev/null
echo 'execution-policy scanner regression passed (forms, case, packages, diagnostics, and scope)'
