# Formalization of the k = 3 case of Erdős Problem 727

The source is [`expert_advice/erdos_727_k2_k3_proof.md`](expert_advice/erdos_727_k2_k3_proof.md)
(6 September 2026), a candidate proof that infinitely many `n` satisfy `((n+3)!)² ∣ (2n)!`, hence
also `((n+2)!)² ∣ (2n)!`.  The target is the Formal Conjectures statement
`erdos_727.variants.k_2` (see [`Erdos727/FormalConjectures.lean`](Erdos727/FormalConjectures.lean)
and [`third_party/formal_conjectures`](third_party/formal_conjectures)).

## Status

**Work in progress.**  The verified boundary is recorded by `bash scripts/check.sh`
(`sorry`/`axiom` scan, Formal Conjectures source comparison, `lake build`, axiom audit of
`Audit.lean`).  Until every module is `sorry`-free the endpoints `erdos727_k3`, `erdos727_k2`
in [`Erdos727/Final.lean`](Erdos727/Final.lean) depend on `sorryAx`; the conditional theorems
`k3_of_mertensAP`, `k2_of_mertensAP` in [`Erdos727/Main.lean`](Erdos727/Main.lean) isolate the
single analytic input `MertensAP 210` (Mertens' second theorem in arithmetic progressions
modulo 210, with `O(1/log x)` error), which is proved in the `Erdos727/Analytic/Character*`
chain.

Module status (✓ = compiles with no `sorry`; ◐ = partially proved; ○ = statements only):

| Module | Content | Status |
| --- | --- | --- |
| `Defs` | `f`, `A`, the six forms `L i`, `carry`, `Good`, `S`, `Y` | ✓ |
| `Carries` | Kummer's theorem, `Good n ↔ ∀ p, 2 v_p(A n) ≤ carry p n` (§2) | ✓ |
| `Polynomial` | factorizations (3.1), resultants, derivative values, §11 identities | ✓ |
| `Count` | residue-class counting in intervals | ✓ |
| `SmallPrimes` | the progression `t₀ + Q v` handling all `p ≤ 1000` (§4) | ✓ |
| `Progression` | `F v`, `Lv i v`, root classes, injectivity, first carry, reduction (§5) | ✓ |
| `Failure` | `failSet`, `sqSet`, `badSet`, union bound, infinitude from `#failSet < X` | ✓ |
| `Ranges` | `smallR`, `mediumR`, `largeR`, sum splitting | ✓ |
| `Range/Square` | square events `≤ 0.01 X` (§5) | ✓ |
| `DigitSets` | carry digit sets, `#(badSet) ≤ ((p+1)/2)^(ℓ-1)(X/p^ℓ + 1)` (§7) | ✓ |
| `Range/Small` | very small primes `≤ 0.02 X` (§7) | ✓ |
| `Analytic/WeylSum` | `e`, `dist₁`, geometric sums, Weyl differencing (§8) | ✓ |
| `Analytic/DigitFourier` | finite Fourier expansion of digit sets, `ℓ¹` bound (§9) | ✓ |
| `Range/Medium` | medium primes and strips `≤ 0.35 X` (§9–10) | ○ |
| `Range/Large` | large primes `≤ 0.60 X` given `MertensAP 210` (§11) | ✓ |
| `Main` | `#failSet ≤ 0.98 X`, conditional endpoints, `k = 2` from `k = 3` (§12) | ✓ |
| `Analytic/MertensSource` | vendored Mertens theorems (see `third_party/mertens`) | ✓ |
| `Analytic/Mertens` | `mertens_second`, block sums (6.3), definition of `MertensAP` | ✓ |
| `Analytic/CharacterPartialSums`, `LFunctionLink`, `CharacterMertens` | character partial sums, `lim ∑χ(n)/n = L(1,χ)`, twisted Mertens (§6) | ✓ |
| `Analytic/MertensAPProof` | orthogonality and the `Weight` framework: `MertensAP q` (§6) | ○ |
| `Analytic/MertensAP`, `Final` | `mertensAP_210`, unconditional endpoints | ✓ (modulo the chain) |

## Design decisions (deviations from the manuscript)

* All arithmetic is in `ℕ`; carries are `(Nat.centralBinom n).factorization p`, and the level-`h`
  carry condition is `p^h ≤ 2 (n % p^h)`.
* Section 4: `Q` and `t₀` are obtained from `Nat.chineseRemainderOfFinset` with the explicit
  Hensel witnesses `t_p = 248, 1107, 300, 196, 17238, 491349478` for `p = 2, 3, 5, 7, 13, 181`.
* Section 9 is reorganised: instead of equidistribution on the torus and a limiting argument, the
  indicator of the carry digit set is expanded in additive characters of `ℤ/p^J`
  (`Analytic/DigitFourier`), with the `ℓ¹` bound `(2p(2 + log p))^J` and Weyl's inequality proved
  by differencing (`Analytic/WeylSum`).  Every error term is explicit.
* Section 7 counts residues via the digit sets and groups primes by `ℓ(p) = ⌊log X / 2 log p⌋`.
* The range constants are slackened to `0.01 + 0.02 + 0.35 + 0.60 = 0.98 < 1`.
* Mertens' theorem in progressions is stated for a general modulus `q` and used only for `q = 210`.

## Toolchain

* Lean `leanprover/lean4:v4.34.0-rc2`; Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`
  (pinned in `lake-manifest.json`).
* Prohibited in project sources: `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`
  (enforced by `scripts/check_axioms.py`).
