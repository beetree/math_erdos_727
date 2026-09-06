#!/usr/bin/env python3
"""Check project source tokens and the axiom reports requested by Audit.lean.

Lean checks the proofs. This script checks the audit output, including transitive
dependencies, against the permitted foundations. Adapted from the verification
script in the sibling math_erdos_740 repository.
"""

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def code_only(source):
    out, i, depth = [], 0, 0
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if source[i] == "\n":
                    out.append("\n")
                i += 1
        elif source.startswith("/-", i):
            out.append(" ")
            depth = 1
            i += 2
        elif source.startswith("--", i):
            j = source.find("\n", i)
            i = len(source) if j < 0 else j
        elif source[i] == '"':
            out.append(" ")
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    if source[i] == "\n":
                        out.append("\n")
                    i += 1
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError("Unclosed block comment")
    return "".join(out)


def main():
    files = [ROOT / "Erdos727.lean", ROOT / "Audit.lean"]
    files += sorted((ROOT / "Erdos727").rglob("*.lean"))
    for file in files:
        code = code_only(file.read_text())
        bad = re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code)
        if bad:
            raise SystemExit(f"Disallowed source token in {file.relative_to(ROOT)}: {bad[0]}")

    if len(sys.argv) == 1:
        print("Project source check passed.")
        return
    if len(sys.argv) != 2:
        raise SystemExit("Usage: check_axioms.py [audit-log]")

    expected = re.findall(r"(?m)^#print\s+axioms\s+(\S+)",
                          code_only((ROOT / "Audit.lean").read_text()))
    if not expected or len(expected) != len(set(expected)):
        raise SystemExit("Audit must request a nonempty list of distinct declarations.")
    log = Path(sys.argv[1]).read_text()
    reports = dict(re.findall(r"'([^\n]+?)' depends on axioms:\s*\[([^\]]*)\]", log))
    reports.update({name: "" for name in re.findall(
        r"'([^\n]+?)' does not depend on any axioms", log)})
    for name in expected:
        if name not in reports:
            raise SystemExit(f"Missing axiom report: {name}")
        dependencies = {x.strip() for x in reports[name].split(",") if x.strip()}
        if dependencies - ALLOWED:
            raise SystemExit(f"Unexpected axioms for {name}: {sorted(dependencies - ALLOWED)}")
    print(f"Verified {len(expected)} axiom reports: standard foundations only.")


if __name__ == "__main__":
    main()
