import Erdos727.Ranges
import Erdos727.Analytic.DigitFourier
import Erdos727.Analytic.WeylSum

/-!
# Medium primes and boundary strips (Sections 9 and 10, reorganised)

**Levels.**  For a prime `X^{1/20} < p ≤ X^{1/2 - η}` let `J = Jlev X p` be the largest
`J ∈ [4, 39]` with `p ≤ X^{2/J - η}` (`Nat.findGreatest`).  Then `4 ≤ J ≤ 39`,
`p^J ≤ X^{2 - ηJ}`, and if `J < 39` also `p > X^{2/(J+1) - η}`; for `J = 39`, `p > X^{1/20}`.

**Per-prime bound.**  The parameters `v ∈ [X, 2X)` with `p ∣ Lv i v` form the set
`{v₀ + p z : z < L}` with `L ≤ X/p + 1` (`exists_root`, `card_filter_mod_eq_le`).  For
`v = v₀ + pz ∈ badSet X i p`, `F v mod p^J ∈ T := digitSet p (carryDigits p (shift i) J)`
(`F_mod_eq`, `mem_carryDigitSet_of_noCarry`).  With `n z := F (v₀ + p z)`,
`card_filter_le_main_add_error` gives

  `#(badSet X i p) ≤ L #T / p^(J-1) + p^{-J} ∑_{h<p^J, p^(J-1) ∤ h} ‖\hat T(h)‖ ‖W(h)‖`,
  `W(h) = ∑_{z<L} e(h n z / p^J)`.

Main term: `#T ≤ ((p+1)/2)^(J-1)` (`card_carryDigitSet_le`), so it is `≤ (X/p + 1) ρ^(J-1)`
with `ρ = 1001/2000 ≥ (p+1)/(2p)`.

Error term.  Write `h = p^(J-s) h'` with `p ∤ h'` and `2 ≤ s ≤ J`.  By `F_eq`,
`n z = D p² z² + (2 D v₀ + E) p z + F v₀`, so `h n z / p^J = (h' D / p^(s-2)) z² +
(h'(2 D v₀ + E) / p^(s-1)) z + h' F v₀ / p^s`.
* `s ≥ 3`: `gcd(h' D, p) = 1` (`D = 210 Q²` has all prime factors `≤ 1000 < p`, use
  `prime_dvd_Q_le`), and `weyl_quadratic` with `q = p^(s-2)` (odd), `N = L`, `z₀ = 0` gives
  `‖W‖² ≤ (2L/p^(s-2) + 1)(2L + 2p^(s-2)(1 + (s-2) log p))
        ≤ 4L²/p + 4L(2 + J log p) + 2p^(J-2)(1 + J log p)`.
* `s = 2`: the quadratic coefficient `h' D` is an integer (`e_add_int`), the linear coefficient
  `h'(2 D v₀ + E)/p` has `p ∤ h'(2 D v₀ + E)` (`not_dvd_D_add_E` with `v = v' = v₀`), so
  `norm_sum_e_le_inv_dist₁` and `inv_le_dist₁_div` give `‖W‖ ≤ p/2 ≤ √(2 p^(J-2))`.
So `‖W(h)‖ ≤ Wb := √(4L²/p + 4L(2 + J log p) + 2p^(J-2)(1 + J log p))` for every such `h`, and
with `sum_norm_fourier_digitSet_le` (`carryDigits_interval`, `carryDigits_subset_range`):

  `error ≤ p^{-J} (2p(2 + log p))^J Wb = (2(2 + log p))^J Wb`.

Uniformly for `X^{1/20} < p ≤ X^{1/2-η}` and `J = Jlev X p` (so `L ≤ 2X/p`):
`Wb² / (X/p)² ≤ 16/p + 8(2 + 39 log p) p/X + 2 p^J (1 + 39 log p)/X²
             ≤ 16 X^{-1/20} + 8(2 + 39 log X) X^{-1/2} + 2(1 + 39 log X) X^{-4η}`,
and `(2(2 + log p))^J ≤ (2(2 + log X))^39`, so `error ≤ ε X/p` for all large `X`
(`(log X)^A X^{-c} → 0`; e.g. `isLittleO_log_rpow_rpow_atTop`/`tendsto_pow_log_div_mul_add_atTop`).

**Summation.**  `∑_{p ∈ mediumR X} #(badSet X i p)` splits into the strip
`X^{1/2-η} < p ≤ X^{1/2+η}`, where `#(badSet) ≤ X/p + 1` and `∑ 1/p ≤ log((1/2+η)/(1/2-η)) + o(1)`
(`sum_inv_prime_block`), and the proper range, where
`∑_p (X/p + 1) ρ^(Jlev X p - 1) + ε X/p`.  Grouping by `J`: `{p : Jlev X p = J} ⊆ primeBlock X a b`
with `1/a = 2/J - η`, `1/b = 2/(J+1) - η`, so `∑ 1/p ≤ log(b/a) + C b/log X` and
`log(b/a) = log((J+1)/J) + log((2 - ηJ)/(2 - η(J+1))) ≤ 1/J + 10⁻⁶`.  Hence the main term is
`≤ X ∑_{J=4}^{39} ρ^(J-1)(1/J + 10⁻⁶) + o(X) ≤ 0.0535 X + o(X)`; the `+1` terms are `O(π(X^{1/2}))`;
`∑_{p ≤ X^{1/2}} 1/p ≤ log 10 + O(1)` bounds the `ε` terms.  Six forms give `≤ 0.35 X`.
-/

namespace Erdos727

open Finset Real Filter

/-- **Sections 9 and 10**: medium primes and boundary strips. -/
theorem medium_bound : ∀ᶠ X : ℕ in atTop,
    (∑ i, ∑ p ∈ mediumR X, #(badSet X i p) : ℝ) ≤ (35 / 100) * X := by
  sorry

end Erdos727
