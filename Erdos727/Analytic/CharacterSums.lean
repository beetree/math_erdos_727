import Erdos727.Analytic.MertensAPProof

/-!
# Character sums and Mertens' theorems in arithmetic progressions

The route to `MertensAP q` (Section 6 of the manuscript, where it is quoted from the prime
number theorem in progressions; here we only need the Mertens-strength statement):

1. For a nontrivial Dirichlet character `χ` mod `q`, the partial sums `∑_{n<N} χ(n)` are bounded
   by `q` (periodicity and `∑_{n mod q} χ(n) = 0`).
2. Abel summation: `T(y) = ∑_{n ≤ y} χ(n)/n` converges to some `ℓ` with `|T(y) - ℓ| ≤ 2q/y`, and
   `∑_{n ≤ x} χ(n) log n / n` is bounded.
3. `ℓ = L(1, χ)` (Abel's theorem for the Dirichlet series, using `LFunction_eq_LSeries` for
   `s > 1` and continuity of `LFunction` at `1`), hence `ℓ ≠ 0` by
   `DirichletCharacter.LFunction_apply_one_ne_zero`.
4. `log n = ∑_{d ∣ n} Λ(d)` gives `∑_{n≤x} χ(n) log n/n = ∑_{d≤x} χ(d)Λ(d)/d · T(x/d)
   = ℓ ∑_{d≤x} χ(d)Λ(d)/d + O(ψ(x)/x)`, so with Chebyshev's `ψ(x) ≪ x`
   (`Chebyshev.psi_le_const_mul_self`) and `ℓ ≠ 0`: `∑_{d≤x} χ(d)Λ(d)/d = O(1)`.
5. Removing prime powers (`∑_p ∑_{k≥2} log p / p^k < ∞`): `∑_{p≤x} χ(p) log p/p = O(1)`.
6. Orthogonality of characters and Mertens' first theorem (`MertensSource`) give
   `∑_{p≤x, p≡a} log p/p = φ(q)⁻¹ log x + O(1)` for every unit `a`.
7. The `Mertens.Weight` framework of `MertensSource` (partial summation with an explicit
   `O(1/log x)` error) turns this into `MertensAP q`.
-/

