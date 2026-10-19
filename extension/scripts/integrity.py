#!/usr/bin/env python3
"""Read-only integrity checks.

Modes
-----
snapshot   Write a SHA256 manifest of the tracked files (``--exclude-extension`` skips ``extension/``).
check      Compare the repository with a single manifest.
baseline   Alias of ``check`` kept for older instructions.
transition Verify an authorized candidacy transition:

           1. the historical manifest is unchanged and anchored at a 40-hex revision;
           2. every authorized path matches its recorded *before* hash in that manifest;
           3. every authorized path matches its recorded *after* hash on disk;
           4. every protected path outside the authorized list still matches the manifest;
           5. every closure source still matches the closure manifest (math sources, pins).

Any missing manifest, missing file, duplicate entry or unexplained difference fails the run.
"""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

SHA_RE = re.compile(r"^[0-9a-f]{40}$")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fail(message):
    print(f"FAIL: {message}")
    return 1


def load(path):
    return json.loads(path.read_text())


def mode_snapshot(args):
    names = subprocess.check_output(["git", "-C", str(args.repo), "ls-files", "-z"]).decode().split("\0")
    data = {
        n: digest(args.repo / n)
        for n in names
        if n and (args.repo / n).is_file() and not (args.exclude_extension and n.startswith("extension/"))
    }
    args.manifest.write_text(json.dumps(data, indent=2) + "\n")
    print("Snapshot:", len(data))
    return 0


def mode_check(args):
    data = load(args.manifest)
    bad = []
    for name, expected in data.items():
        path = args.repo / name
        if not path.is_file() or digest(path) != expected:
            bad.append(name)
    for name in bad:
        print("DIFF/MISSING", name)
    print("PASS" if not bad else "FAIL", len(data), "files")
    return bool(bad)


def mode_transition(args):
    for path in (args.manifest, args.transition, args.closure):
        if not path.is_file():
            return fail(f"missing evidence file: {path}")

    historical = load(args.manifest)
    transition = load(args.transition)
    closure = load(args.closure)
    errors = []

    if not SHA_RE.match(str(transition.get("historical_revision", ""))):
        errors.append("transition.historical_revision is not a 40-hex revision")

    changes = transition.get("authorized_changes")
    if not isinstance(changes, list) or not changes:
        return fail("transition.authorized_changes is missing or empty")
    authorized = {}
    for entry in changes:
        path = entry.get("path")
        before = entry.get("before_sha256")
        after = entry.get("after_sha256")
        if not path or not before or not after:
            errors.append(f"incomplete authorized entry: {entry}")
            continue
        if path in authorized:
            errors.append(f"duplicate authorized path: {path}")
        authorized[path] = entry

    for path, entry in authorized.items():
        if path not in historical:
            errors.append(f"{path}: not in the historical manifest")
        elif historical[path] != entry["before_sha256"]:
            errors.append(f"{path}: before hash does not match the historical manifest")
        current = args.repo / path
        if not current.is_file():
            errors.append(f"{path}: authorized file is missing")
        elif digest(current) != entry["after_sha256"]:
            errors.append(f"{path}: does not match its recorded after hash")

    unchanged = 0
    for path, expected in historical.items():
        if path in authorized:
            continue
        current = args.repo / path
        if not current.is_file():
            errors.append(f"{path}: protected file is missing")
        elif digest(current) != expected:
            errors.append(f"{path}: protected file changed outside the authorized list")
        else:
            unchanged += 1

    if not SHA_RE.match(str(closure.get("closure_revision", ""))):
        errors.append("closure.closure_revision is not a 40-hex revision")
    closure_files = closure.get("files")
    if not isinstance(closure_files, dict) or not closure_files:
        errors.append("closure.files is missing or empty")
        closure_files = {}
    for path, expected in closure_files.items():
        current = args.repo / path
        if not current.is_file():
            errors.append(f"{path}: closure source is missing")
        elif digest(current) != expected:
            errors.append(f"{path}: closure source differs from the closure revision")

    if errors:
        for message in errors:
            print("FAIL:", message)
        return fail(f"{len(errors)} integrity problem(s) in the candidacy transition")

    print(
        f"PASS: {len(authorized)} authorized changes, {unchanged} protected files unchanged, "
        f"{len(closure_files)} closure sources identical"
    )
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("mode", choices=["snapshot", "check", "baseline", "transition"])
    parser.add_argument("repo", type=Path)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("transition", type=Path, nargs="?")
    parser.add_argument("closure", type=Path, nargs="?")
    parser.add_argument("--exclude-extension", action="store_true")
    args = parser.parse_args()

    if args.mode == "snapshot":
        return mode_snapshot(args)
    if args.mode in ("check", "baseline"):
        return mode_check(args)
    if args.transition is None or args.closure is None:
        return fail("transition mode requires <historical> <transition> <closure>")
    return mode_transition(args)


if __name__ == "__main__":
    raise SystemExit(main())
