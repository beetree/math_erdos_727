#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

python3 scripts/check_axioms.py
python3 scripts/check_fc_source.py

lake build
mkdir -p .lake
lake env lean -DwarningAsError=true Audit.lean | tee .lake/axiom-audit.log
python3 scripts/check_axioms.py .lake/axiom-audit.log
