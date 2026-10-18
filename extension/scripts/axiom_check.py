#!/usr/bin/env python3
"""Validate the output of `lake env lean AxiomCheck.lean`.

The checker is deliberately strict: an empty or truncated log is a failure, not a
vacuous pass. It derives the expected inventory from `AxiomCheck.lean` itself, so the
count is never hard-coded.

Checks performed
----------------
1. The log contains no Lean error line.
2. Every `#print axioms NAME` in the audit file is reported exactly once.
3. No name outside the audit file is reported.
4. Every reported axiom set is contained in {propext, Classical.choice, Quot.sound}.
5. `sorryAx` never appears, not even inside another name.

Exit status: 0 only when all checks pass; 1 otherwise.
"""
import argparse
import re
import sys
from pathlib import Path

PERMITTED = {"propext", "Classical.choice", "Quot.sound"}

AUDIT_LINE = re.compile(r"^\s*#print axioms\s+(\S+)\s*$", re.M)
DEPENDS = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]\s*$")
NO_AXIOMS = re.compile(r"^'([^']+)' does not depend on any axioms\s*$")
LEAN_ERROR = re.compile(r"\berror\b|\bunknown constant\b|\bunknown identifier\b")


def fail(message):
    print(f"FAIL: {message}")
    return 1


def expected_names(audit_file):
    if not audit_file.is_file():
        return None, fail(f"audit file not found: {audit_file}")
    names = AUDIT_LINE.findall(audit_file.read_text())
    if not names:
        return None, fail(f"no '#print axioms' lines in {audit_file}")
    duplicates = sorted({n for n in names if names.count(n) > 1})
    if duplicates:
        return None, fail(f"duplicate '#print axioms' lines: {', '.join(duplicates)}")
    return names, 0


def parse_log(lines):
    entries = {}
    duplicate = []
    errors = []
    for raw in lines:
        line = raw.strip()
        if not line:
            continue
        if LEAN_ERROR.search(line):
            errors.append(line)
            continue
        match = DEPENDS.match(line)
        if match:
            name, body = match.group(1), match.group(2)
            axioms = {part.strip() for part in body.split(",") if part.strip()}
        else:
            match = NO_AXIOMS.match(line)
            if not match:
                continue
            name, axioms = match.group(1), set()
        if name in entries:
            duplicate.append(name)
        entries[name] = axioms
    return entries, duplicate, errors


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("log", type=Path, help="captured stdout of `lake env lean AxiomCheck.lean`")
    parser.add_argument(
        "--audit",
        type=Path,
        default=Path(__file__).resolve().parents[1] / "AxiomCheck.lean",
        help="audit source; names are derived from its '#print axioms' lines",
    )
    args = parser.parse_args()

    if not args.log.is_file():
        return fail(f"log not found: {args.log}")

    names, status = expected_names(args.audit)
    if status:
        return status

    entries, duplicate, errors = parse_log(args.log.read_text().splitlines())

    if errors:
        return fail(f"{len(errors)} Lean error line(s); first: {errors[0]}")
    if duplicate:
        return fail(f"name(s) reported more than once: {', '.join(sorted(set(duplicate)))}")
    if not entries:
        return fail("empty audit output: no '#print axioms' result was reported")
    if "sorryAx" in args.log.read_text():
        return fail("'sorryAx' appears in the audit output")

    missing = [n for n in names if n not in entries]
    if missing:
        return fail(
            f"incomplete audit: {len(missing)} of {len(names)} expected name(s) missing, "
            f"first: {missing[0]}"
        )
    unexpected = sorted(set(entries) - set(names))
    if unexpected:
        return fail(f"name(s) not requested by {args.audit.name}: {', '.join(unexpected[:5])}")

    bad = {name: sorted(axioms - PERMITTED) for name, axioms in entries.items()}
    bad = {name: extra for name, extra in bad.items() if extra}
    if bad:
        first = sorted(bad)[0]
        return fail(f"non-permitted axiom(s) {bad[first]} in {first}")

    sets = {}
    for axioms in entries.values():
        sets.setdefault(tuple(sorted(axioms)), 0)
        sets[tuple(sorted(axioms))] += 1
    detail = "; ".join(
        f"{count} x [{', '.join(axioms) if axioms else 'none'}]"
        for axioms, count in sorted(sets.items())
    )
    print(f"PASS: {len(entries)} audited names; axioms used: {detail}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
