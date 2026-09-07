# Erdős Problem 727, case k = 3: Lean 4 formalization

**Paper:** [*A carry-counting approach to the k = 3 case of Erdős Problem 727*](erdos_727_partial_proof.pdf) (Johan Land, 6 September 2026; [LaTeX source](erdos_727_partial_proof.tex)), condensing the original manuscript [`expert_advice/erdos_727_k2_k3_proof.md`](expert_advice/erdos_727_k2_k3_proof.md).

Erdős Problem 727 (Erdős, Graham, Ruzsa, Straus 1975, p. 90) asks whether, for every `k`, there
are infinitely many `n` with `((n+k)!)² ∣ (2n)!`; the 1975 paper says this cannot be proved even
for `k = 2`.  This repository formalizes the manuscript's proof for `k = 3`, and deduces `k = 2`.

## Statement

The propositions in [`Erdos727/FormalConjectures.lean`](Erdos727/FormalConjectures.lean)
reproduce the right-hand sides of `erdos_727` and `erdos_727.variants.k_2` of
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/8323e878b83fcd7f4a448256069352a265460d75/FormalConjectures/ErdosProblems/727.lean)
(revision pinned in `third_party/formal_conjectures/REVISION`, source comparison by
`scripts/check_fc_source.py`):

```lean
def formalConjecturesStatement_k2 : Prop :=
    letI k := 2
    Set.Infinite {n : ℕ | (Nat.factorial (n + k)) ^ 2 ∣ Nat.factorial (2 * n)}
```

The endpoints are `Erdos727.erdos727_k3 : formalConjecturesStatement_k3` and
`Erdos727.erdos727_k2 : formalConjecturesStatement_k2` in [`Erdos727/Final.lean`](Erdos727/Final.lean).

## What this verification establishes

The terminal theorems `Erdos727.erdos727_k3` and `Erdos727.erdos727_k2` are proved with no
`sorry`, no project axioms, and no `native_decide`; `lake build` asserts (via
[`Erdos727/BuildAudit.lean`](Erdos727/BuildAudit.lean)) that their transitive axiom dependencies
are exactly `propext`, `Classical.choice`, `Quot.sound`, and prints the report for `erdos727_k2`.  Accepting the
pinned Formal Conjectures formulation of the `k = 2` question, this settles it affirmatively (and
the `k = 3` case), subject to the usual trust in Lean's kernel, standard foundations, Mathlib at
the pinned revision, and the checking environment.  It does not address the general case of
Erdős Problem 727.

The only external mathematical inputs are Mathlib (including `L(1, χ) ≠ 0` for nontrivial
Dirichlet characters and Chebyshev's bound on `ψ`) and the vendored Mertens theorems in
`Erdos727/Analytic/MertensSource.lean`, which are themselves proved Lean code (see
`third_party/mertens/NOTICE.md`).

## Verification

See [FORMALIZATION.md](FORMALIZATION.md) for the module-by-module map and design decisions, and
[docs/VERIFICATION.md](docs/VERIFICATION.md) for the recorded transcript.  `bash scripts/check.sh`
scans the sources for prohibited tokens, compares the statement with the pinned upstream source,
builds the project, and checks the axiom reports requested in `Audit.lean` against
`propext`, `Classical.choice`, `Quot.sound`.

```sh
lake build
bash scripts/check.sh
```

The build uses the prebuilt Mathlib in `.lake/packages` (copied from a sibling project, or
`lake exe cache get`).

## Layout

* `Erdos727/` — the formalization (see FORMALIZATION.md for the dependency map).
* `Erdos727/Analytic/MertensSource.lean` — vendored Mertens theorems (`third_party/mertens`).
* `third_party/formal_conjectures/` — pinned upstream statement and license.
* `scripts/` — verification scripts.  `Audit.lean` — axiom report requests.
