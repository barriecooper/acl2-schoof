#!/usr/bin/env python3
"""Validate maintained Markdown without third-party dependencies."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_STATUSES = {"Open", "Postponed", "Proved"}
LINK = re.compile(r"(?<!!)\[[^]]*\]\(([^)]+)\)")


def table_cells(line: str) -> list[str] | None:
    stripped = line.strip()
    if not (stripped.startswith("|") and stripped.endswith("|")):
        return None
    return [cell.strip() for cell in stripped[1:-1].split("|")]


def check_file(path: Path) -> list[str]:
    errors: list[str] = []
    lines = path.read_text(encoding="utf-8").splitlines()
    expected: int | None = None
    previous_was_table = False
    identifiers: set[str] = set()
    obligation_header: list[str] | None = None

    for number, line in enumerate(lines, 1):
        cells = table_cells(line)
        if cells is not None:
            if number >= 2 and not lines[number - 2].strip() and previous_was_table:
                errors.append(f"{path}:{number}: blank line splits a Markdown table")
            if expected is None:
                expected = len(cells)
            elif len(cells) != expected:
                errors.append(
                    f"{path}:{number}: table has {len(cells)} columns; expected {expected}"
                )
            previous_was_table = True
            if path.name == "obligations.md":
                if cells and cells[0] == "Identifier":
                    obligation_header = cells
                elif obligation_header and not all(
                    re.fullmatch(r":?-+:?", cell) for cell in cells
                ):
                    identifier = cells[0]
                    if identifier in identifiers:
                        errors.append(f"{path}:{number}: duplicate obligation {identifier}")
                    identifiers.add(identifier)
                    status_index = obligation_header.index("Status")
                    status = cells[status_index] if status_index < len(cells) else ""
                    if status not in ALLOWED_STATUSES:
                        errors.append(
                            f"{path}:{number}: invalid obligation status {status!r}; "
                            f"allowed: {', '.join(sorted(ALLOWED_STATUSES))}"
                        )
        else:
            if line.strip():
                expected = None
                previous_was_table = False

        for match in LINK.finditer(line):
            target = match.group(1).strip().split()[0].strip("<>")
            if not target or target.startswith(("#", "http://", "https://", "mailto:")):
                continue
            target = target.split("#", 1)[0]
            resolved = (ROOT / target.lstrip("/")) if target.startswith("/") else path.parent / target
            if not resolved.exists():
                errors.append(f"{path}:{number}: broken repository-relative link {target!r}")
    return errors


def main() -> int:
    paths = [Path(arg).resolve() for arg in sys.argv[1:]]
    if not paths:
        paths = sorted((ROOT / "docs").glob("*.md")) + [ROOT / "README.md"]
    errors = [error for path in paths for error in check_file(path)]
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"documentation check passed ({len(paths)} files)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
