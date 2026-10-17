#!/usr/bin/env bash
set -euo pipefail
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"
mkdir -p verification-logs
python3 scripts/preflight.py | tee verification-logs/01-static.txt
python3 scripts/check_exact_cases.py | tee verification-logs/02-exact-cases.txt
lean --version | tee verification-logs/03-toolchain.txt
lake exe cache get 2>&1 | tee verification-logs/04-cache.txt
lake build 2>&1 | tee verification-logs/05-build.txt
lake env lean AxiomAudit.lean 2>&1 | tee verification-logs/06-axioms.txt
bash scripts/verify-comparator.sh 2>&1 | tee verification-logs/07-comparator.txt
printf '%s\n' 'Completed all commands. Review the logs and record the audited source revision.'
