#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"

# Public logical/executable boundaries require deliberate review and the
# evidence described in AGENTS.md.  Existing MBE templates are confined to the
# field kernel; imported Community Books under .deps are outside project policy.
package='([[:alnum:]_$*+<>=!?./-]+::)?'
construct='(mbe|defexec)'
pat="[(][[:space:]]*${package}${construct}([[:space:])]|$)"
if (($# == 0)); then
  paths=(books tests)
else
  paths=("$@")
fi

set +e
matches=$(grep -E -r -n -H -i --include='*.lisp' --include='*.acl2' "$pat" "${paths[@]}" 2>&1)
rc=$?
set -e
if ((rc > 1)); then
  printf '%s\n' "$matches" >&2
  echo "execution-policy scanner failed (grep exit status $rc)" >&2
  exit "$rc"
fi
if ((rc == 1)); then
  echo 'execution-boundary scan passed'
  exit 0
fi

violations=$matches
if (($# == 0)); then
  # This is the sole reviewed source template currently recorded in
  # docs/execution-boundaries.md.  Do not broaden this allowlist for fixtures.
  violations=$(printf '%s\n' "$matches" | grep -F -v 'books/field/kernel.lisp:' || true)
fi
if [[ -n $violations ]]; then
  printf '%s\n' "$violations"
  echo 'unreviewed ACL2 MBE or DEFEXEC boundary found' >&2
  exit 1
fi
echo 'execution-boundary scan passed (reviewed field-kernel MBE template only)'
