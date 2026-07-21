#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
version=$(cat "$root/ACL2_VERSION")
dest="$root/.deps/acl2-$version"
mkdir -p "$root/.deps"
if [[ ! -d "$dest/.git" ]]; then
  git clone --depth 1 --branch "$version" https://github.com/acl2/acl2.git "$dest"
fi
if [[ ! -x "$dest/saved_acl2" ]]; then
  command -v sbcl >/dev/null || { echo 'SBCL is required (apt-get install sbcl)' >&2; exit 1; }
  make -C "$dest" LISP=sbcl
fi
ln -sfn "acl2-$version" "$root/.deps/acl2"
test -x "$root/.deps/acl2/saved_acl2"
