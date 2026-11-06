#!/usr/bin/env python3
"""Prepare isolated W10 interval declarations with inferred, checked types.

This is a candidate producer, not an installer or acceptance check. It never
writes the accepted source directory. Each macro expands to an ordinary opaque
theorem; type_of% elaborates the same proof used by the theorem body. Numerical
endpoints and proof terms are copied from the input, without rounding.
"""

import argparse
import hashlib
import json
import re
from pathlib import Path


COMMAND = '''import W10Interval

/-- Expand an interval proof to an ordinary theorem with its inferred type. -/
macro "box_bound " n:ident " := " proof:term : command =>
  `(theorem $n : type_of% $proof := $proof)
'''

BOUND = re.compile(
    r"theorem (W10Log\d+_b\d+) :\n(.*?) := by\n"
    r"  exact (box_(?:add|sub|neg|mul|inv|pow)) ([^\n]+)\n\n",
    re.S,
)


def compress(source: str) -> tuple[str, list[str]]:
    blocks = re.split(r"(?=^theorem )", source, flags=re.M)
    changed = []
    for index, block in enumerate(blocks):
        match = BOUND.fullmatch(block)
        if match is None:
            continue
        name, statement, operation, arguments = match.groups()
        lower = statement.strip().split(" ≤ ", 1)[0]
        upper = statement.strip().rsplit(" ≤ ", 1)[1]
        # These files use explicit rational endpoints. Reject unfamiliar input
        # instead of allowing an expression parser to silently change a bound.
        endpoint = r"\(\(-?\d+ : ℝ\) / \d+\)"
        if not all(re.fullmatch(endpoint, bound) for bound in (lower, upper)):
            raise ValueError(f"unsupported endpoint in {name}")
        blocks[index] = (
            f"box_bound {name} :=\n"
            f"  {operation} (l := {lower}) (u := {upper}) {arguments}\n\n"
        )
        changed.append(name)
    result = "".join(blocks)
    if changed:
        if not result.startswith("import W10Interval\n"):
            raise ValueError("unexpected imports")
        result = result.replace("import W10Interval\n", "import W10BoundCommand\n", 1)
    return result, changed


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path, default=Path(__file__).resolve().parents[1] / "src")
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    source_dir, output_dir = args.source_dir.resolve(), args.output_dir.resolve()
    accepted = Path(__file__).resolve().parents[1] / "src"
    if output_dir == accepted or accepted in output_dir.parents or output_dir == source_dir:
        parser.error("use a separate candidate directory; this tool does not install sources")
    output_dir.mkdir(parents=True, exist_ok=True)
    report = {"status": "UNVERIFIED_CANDIDATE_NOT_INSTALLED", "modules": []}
    for source in sorted(source_dir.glob("W10Log*.lean")):
        before = source.read_bytes()
        result, names = compress(before.decode())
        if not names:
            continue
        after = result.encode()
        (output_dir / source.name).write_bytes(after)
        report["modules"].append({
            "module": source.stem,
            "before_sha256": digest(before), "after_sha256": digest(after),
            "before_bytes": len(before), "after_bytes": len(after),
            "before_physical_lines": len(before.splitlines()),
            "after_physical_lines": len(after.splitlines()),
            "declarations": names,
        })
    (output_dir / "W10BoundCommand.lean").write_text(COMMAND)
    report["command_sha256"] = digest(COMMAND.encode())
    (output_dir / "candidate.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Prepared {len(report['modules'])} candidate modules; not installed or verified")


if __name__ == "__main__":
    main()
