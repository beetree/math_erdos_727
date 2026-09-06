#!/usr/bin/env python3
"""Compare local propositions with the hash-pinned Formal Conjectures source for Problem 727.

Offline by default; --refetch also verifies a fresh download against the same hash.
The snapshot is reference text, never a Lean import.
"""

import argparse
import hashlib
from pathlib import Path
import re
import sys
from urllib.request import urlopen

ROOT = Path(__file__).resolve().parents[1]
REVISION = (ROOT / "third_party/formal_conjectures/REVISION").read_text().strip()
SNAPSHOT = ROOT / "third_party/formal_conjectures/source/727.lean.txt"
UPSTREAM_PATH = "FormalConjectures/ErdosProblems/727.lean"
DIGEST = "c1a9edb2477930bf617c3838b59a808a3f5449f4cc387a2c3b850b39ca9293d2"


def verify_hash(data, expected, label):
    if hashlib.sha256(data).hexdigest() != expected:
        raise ValueError(f"SHA-256 mismatch: {label}")


def without_comments(source):
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
            out.append(" ")
            newline = source.find("\n", i)
            i = len(source) if newline < 0 else newline
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError("Unclosed Lean comment")
    return "".join(out)


def region(source, start, end):
    source = without_comments(source)
    starts = list(re.finditer(r"(?m)^" + re.escape(start), source))
    ends = list(re.finditer(r"(?m)^" + re.escape(end), source))
    if len(starts) != 1 or len(ends) != 1 or starts[0].start() >= ends[0].start():
        raise ValueError(f"Missing, duplicate, or reordered boundaries: {start!r}, {end!r}")
    return source[starts[0].start():ends[0].start()].strip()


def replace_once(source, old, new):
    if source.count(old) != 1:
        raise ValueError(f"Expected exactly one occurrence of {old!r}")
    return source.replace(old, new, 1)


def same(local, upstream, label):
    if " ".join(local.split()) != " ".join(upstream.split()):
        raise ValueError(f"Local/upstream source mismatch: {label}\n--- local\n{local}\n--- upstream\n{upstream}")


def compare(problem, local):
    upstream = region(problem, "theorem erdos_727 :", "theorem erdos_727.variants.k_2 :")
    upstream = replace_once(upstream, "theorem erdos_727 : answer(sorry) ↔", "")
    upstream = replace_once(upstream, ":= by\n  sorry", "")
    upstream = replace_once(upstream, "@[category research open, AMS 11]", "")
    loc = region(local, "def formalConjecturesStatement :", "def formalConjecturesStatement_k2")
    loc = replace_once(loc, "def formalConjecturesStatement : Prop :=", "")
    same(loc, upstream, "erdos_727 proposition")

    upstream = region(problem, "theorem erdos_727.variants.k_2 :", "theorem erdos_727.variants.k_1 :")
    upstream = replace_once(upstream, "theorem erdos_727.variants.k_2 :", "")
    upstream = replace_once(upstream, "answer(sorry) ↔", "")
    upstream = replace_once(upstream, ":= by\n  sorry", "")
    upstream = replace_once(upstream, "@[category research solved, AMS 11]", "")
    loc = region(local, "def formalConjecturesStatement_k2 :", "def formalConjecturesStatement_k3")
    loc = replace_once(loc, "def formalConjecturesStatement_k2 : Prop :=", "")
    same(loc, upstream, "erdos_727.variants.k_2 proposition")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refetch", action="store_true")
    args = parser.parse_args()
    data = SNAPSHOT.read_bytes()
    verify_hash(data, DIGEST, str(SNAPSHOT.relative_to(ROOT)))
    if args.refetch:
        url = f"https://raw.githubusercontent.com/google-deepmind/formal-conjectures/{REVISION}/{UPSTREAM_PATH}"
        with urlopen(url, timeout=30) as response:
            verify_hash(response.read(), DIGEST, url)
    compare(data.decode("utf-8"), (ROOT / "Erdos727/FormalConjectures.lean").read_text())
    print(f"Formal Conjectures source check passed at {REVISION}: erdos_727 and variants.k_2 propositions."
          + (" Fresh upstream download verified." if args.refetch else ""))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        sys.exit(f"Formal Conjectures source check failed: {error}")
