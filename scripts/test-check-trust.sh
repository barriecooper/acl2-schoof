#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d)
generated="$root/.deps/check-trust-regression-$$"
trap 'rm -rf "$tmp" "$generated"' EXIT

printf '(in-package "ACL2")\n' >"$tmp/clean.lisp"
printf '(value-triple :clean)\n' >"$tmp/clean.acl2"
"$root/scripts/check-trust.sh" "$tmp" >/dev/null

check_rejected() {
  local spelling=$1
  local file="$tmp/fixture-$2.acl2"
  local output
  printf '(%s sample)\n' "$spelling" >"$file"
  if output=$("$root/scripts/check-trust.sh" "$file" 2>&1); then
    echo "trust scanner accepted forbidden form: $spelling" >&2
    exit 1
  fi
  [[ $output == *"$file:1:"* ]] || {
    echo "trust scanner did not identify the offending file: $output" >&2
    exit 1
  }
  [[ ${output,,} == *"${spelling,,}"* ]] || {
    echo "trust scanner did not identify the offending construct: $output" >&2
    exit 1
  }
  rm "$file"
}

# Every trust-expanding family is rejected in its ordinary spelling.  Extra
# cases exercise case folding and the ACL2 package-prefix path explicitly.
forms=(skip-proofs set-ld-skip-proofsp defaxiom defttag set-raw-mode
       set-raw-mode-on set-raw-mode-off 'progn!' defattach 'defattach!'
       defattach-system include-raw)
for index in "${!forms[@]}"; do
  check_rejected "${forms[$index]}" "$index"
done
check_rejected 'SkIp-PrOoFs' mixed-case
check_rejected 'acl2::skip-proofs' qualified-skip
check_rejected 'ACL2::DEFAXIOM' qualified-axiom
check_rejected 'my-package::include-raw' qualified-raw

# Default scope is only project books and tests.  Generated dependencies and
# certification output under .deps must never become scanner inputs.
mkdir -p "$generated"
printf '(%s sample)\n' 'skip-proofs' >"$generated/output.lisp"
"$root/scripts/check-trust.sh" >/dev/null

echo "trust scanner regression passed (${#forms[@]} unqualified forms, case, package, diagnostics, and scope)"
