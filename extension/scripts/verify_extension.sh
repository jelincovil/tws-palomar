#!/usr/bin/env bash
# Verify the db2 threshold extension end to end.
#
# Used identically by a human reproducing the close-out and by
# .github/workflows/extension-ci.yml. Every step fails the script (set -e + pipefail),
# and every log is kept even on failure.
#
# Steps: build Solution from source, build the five extension modules, run the axiom
# audit and its checker, run the rational checks, and verify that the protected base
# files still match their historical manifest.
#
# Environment: OUT_DIR overrides the log directory (default: <repo>/verification-logs/extension).
set -euo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
extension_dir=$(cd -- "$script_dir/.." && pwd)
repo_root=$(cd -- "$extension_dir/.." && pwd)
out_dir=${OUT_DIR:-"$repo_root/verification-logs/extension"}

if [ ! -f "$extension_dir/lakefile.toml" ]; then
  printf 'FAIL: %s does not contain extension/lakefile.toml\n' "$repo_root" >&2
  exit 1
fi

mkdir -p "$out_dir"

{
  printf '# extension verification — %s\n' "$(date -Iseconds)"
  printf 'repository_root=%s\n' "$repo_root"
  printf 'extension_dir=%s\n' "$extension_dir"
  printf 'out_dir=%s\n' "$out_dir"
  printf 'lean=%s\n' "$(lean --version 2>&1 | head -1)"
  printf 'lake=%s\n' "$(lake --version 2>&1 | head -1)"
  printf 'toolchain=%s\n' "$(cat "$repo_root/lean-toolchain" 2>/dev/null || echo missing)"
  if git -C "$repo_root" rev-parse --git-dir >/dev/null 2>&1; then
    printf 'git_head=%s\n' "$(git -C "$repo_root" rev-parse HEAD)"
    printf 'git_branch=%s\n' "$(git -C "$repo_root" rev-parse --abbrev-ref HEAD)"
    printf 'git_dirty_files=%s\n' "$(git -C "$repo_root" status --porcelain | wc -l | tr -d ' ')"
  else
    printf 'git_head=not-a-git-checkout\n'
  fi
  printf 'mathlib_pin=%s\n' "$(
    python3 -c 'import json,sys; d=json.load(open(sys.argv[1])); print(next(p["inputRev"] for p in d["packages"] if p["name"] == "mathlib"))' \
      "$repo_root/lake-manifest.json" 2>/dev/null || echo unknown
  )"
} > "$out_dir/00-environment.txt"

printf '== extension verification\n'
printf '   repository: %s\n' "$repo_root"
printf '   logs:       %s\n' "$out_dir"

printf '== [1/6] lake build Solution (from source)\n'
( cd "$repo_root" && lake build Solution ) 2>&1 | tee "$out_dir/01-solution-build.log"

printf '== [2/6] lake build (extension, five modules)\n'
( cd "$extension_dir" && lake build ) 2>&1 | tee "$out_dir/02-extension-build.log"

printf '== [3/6] lake env lean AxiomCheck.lean\n'
( cd "$extension_dir" && lake env lean AxiomCheck.lean ) 2>&1 | tee "$out_dir/03-axioms.log"

printf '== [4/6] axiom audit checker\n'
python3 "$extension_dir/scripts/axiom_check.py" "$out_dir/03-axioms.log" \
  --audit "$extension_dir/AxiomCheck.lean" 2>&1 | tee "$out_dir/04-axioms-check.log"

printf '== [5/6] rational direct/padded checks\n'
( cd "$extension_dir" && python3 scripts/exact_checks.py ) 2>&1 | tee "$out_dir/05-exact-checks.log"

printf '== [6/6] protected-base integrity and candidacy transition\n'
python3 "$extension_dir/scripts/integrity.py" transition "$repo_root" \
  "$extension_dir/verification/integrity-before.json" \
  "$extension_dir/verification/candidacy-transition.json" \
  "$extension_dir/verification/closure-sources.json" 2>&1 | tee "$out_dir/06-integrity.log"

printf 'ALL CHECKS PASSED\n'
