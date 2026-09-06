import Erdos727.Analytic.CharacterPartialSums

/-!
# The limit of `∑ χ(n)/n` is `L(1, χ)` (step 3 of `CharacterSums`)
-/

namespace Erdos727

open Finset Real

variable {q : ℕ} [NeZero q]

/-- The limit of `∑_{n ≤ N} χ(n)/n` is `L(1, χ)`. -/
theorem tendsto_sum_char_div_LFunction (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, χ n / n) Filter.atTop
      (nhds (DirichletCharacter.LFunction χ 1)) := by
  sorry

end Erdos727
