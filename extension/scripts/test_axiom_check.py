#!/usr/bin/env python3
"""Self-test for scripts/axiom_check.py.

The gate must accept a valid log and reject an empty, a truncated and a
non-permitted-axiom log. Run: python3 scripts/test_axiom_check.py
"""
import subprocess
import sys
import tempfile
from pathlib import Path

CHECKER = Path(__file__).resolve().parent / "axiom_check.py"

AUDIT = """#print axioms Alpha.ok
#print axioms Beta.ok
"""

VALID = """'Alpha.ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'Beta.ok' does not depend on any axioms
"""

CASES = [
    ("valid output accepted", VALID, 0),
    ("empty output rejected", "", 1),
    ("truncated output rejected", "'Alpha.ok' depends on axioms: [propext]\n", 1),
    (
        "non-permitted axiom rejected",
        "'Alpha.ok' depends on axioms: [propext, sorryAx]\n"
        "'Beta.ok' does not depend on any axioms\n",
        1,
    ),
    (
        "unrequested name rejected",
        VALID + "'Gamma.extra' depends on axioms: [propext]\n",
        1,
    ),
]


def main():
    failures = 0
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        audit = tmp / "AxiomCheck.lean"
        audit.write_text(AUDIT)
        for label, log_text, expected in CASES:
            log = tmp / "log.txt"
            log.write_text(log_text)
            completed = subprocess.run(
                [sys.executable, str(CHECKER), str(log), "--audit", str(audit)],
                capture_output=True,
                text=True,
            )
            ok = completed.returncode == expected
            failures += not ok
            print(f"{'ok  ' if ok else 'FAIL'} {label} (exit {completed.returncode}, expected {expected})")
            if not ok:
                print(completed.stdout.rstrip())
                print(completed.stderr.rstrip())
    print("PASS: checker self-test" if not failures else f"FAIL: {failures} case(s)")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
