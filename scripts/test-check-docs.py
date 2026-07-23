#!/usr/bin/env python3
"""Focused regressions for check-docs.py."""

from __future__ import annotations

import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts/check-docs.py"


def run(path: Path, succeeds: bool) -> None:
    result = subprocess.run([str(CHECKER), str(path)], text=True, capture_output=True)
    if (result.returncode == 0) != succeeds:
        raise SystemExit(
            f"unexpected result for {path}: {result.returncode}\n{result.stdout}{result.stderr}"
        )


def main() -> None:
    run(ROOT / "docs/obligations.md", True)
    with tempfile.TemporaryDirectory() as directory:
        docs = Path(directory) / "docs"
        docs.mkdir()
        path = docs / "sample.md"
        path.write_text("| A | B |\n|---|---|\n| x | y | z |\n", encoding="utf-8")
        run(path, False)
        path.write_text("| A | B |\n|---|---|\n| x | y |\n\n| q | r |\n", encoding="utf-8")
        run(path, False)
        obligations = docs / "obligations.md"
        obligations.write_text(
            "| Identifier | Status |\n|---|---|\n| DUP | Open |\n| DUP | Proved |\n",
            encoding="utf-8",
        )
        run(obligations, False)
        obligations.write_text(
            "| Identifier | Status |\n|---|---|\n| BAD | Finished |\n", encoding="utf-8"
        )
        run(obligations, False)
    print("documentation checker regression passed")


if __name__ == "__main__":
    main()
