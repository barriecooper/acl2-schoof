#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
"$root/scripts/certify-one.sh" tests/smoke.lisp
