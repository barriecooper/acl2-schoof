#!/usr/bin/env bash
set -euo pipefail
exec "$(dirname "$0")/certify-one.sh" books/top.lisp
