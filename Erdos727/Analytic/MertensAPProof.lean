import Erdos727.Analytic.CharacterMertens

/-!
# Mertens' theorems in arithmetic progressions (steps 6–7 of `CharacterSums`)
-/

namespace Erdos727

open Finset Real

variable {q : ℕ} [NeZero q]

/-- **Mertens' first theorem in arithmetic progressions.** -/
theorem mertens_first_AP (a : ZMod q) (ha : IsUnit a) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => (p : ZMod q) = a), log p / p
        - (Nat.totient q : ℝ)⁻¹ * log N| ≤ C := by
  sorry

/-- **Mertens' second theorem in arithmetic progressions**, with `O(1/log x)` error. -/
theorem mertensAP_of_neZero (q : ℕ) [NeZero q] : MertensAP q := by
  sorry

end Erdos727
