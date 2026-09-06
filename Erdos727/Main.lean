import Erdos727.Range.Square
import Erdos727.Range.Small
import Erdos727.Range.Medium
import Erdos727.Range.Large
import Erdos727.FormalConjectures

/-!
# Completion of the proof (Section 12)

Adding the four range bounds gives `#(failSet X) ≤ 0.98 X < X` for all large `X`, so every
large dyadic interval `[X, 2X)` contains a good parameter, and there are infinitely many good
`n`.  The `k = 2` statement follows from `k = 3` since `(n+3)! = (n+3) (n+2)!`.
-/

namespace Erdos727

open Finset Real Filter

theorem card_failSet_lt (hM : MertensAP 210) : ∀ᶠ X : ℕ in atTop, #(failSet X) < X := by
  filter_upwards [sq_bound, small_bound, medium_bound, large_bound hM, eventually_ge_atTop 1]
    with X h1 h2 h3 h4 hX
  have hcast : (#(failSet X) : ℝ) ≤
      ∑ i, ∑ p ∈ primeRange X, ((#(sqSet X i p) : ℝ) + #(badSet X i p)) := by
    exact_mod_cast card_failSet_le X
  have hsplit : ∀ i : Fin 6, ∑ p ∈ primeRange X, ((#(sqSet X i p) : ℝ) + #(badSet X i p)) =
      ∑ p ∈ primeRange X, (#(sqSet X i p) : ℝ) + (∑ p ∈ smallR X, (#(badSet X i p) : ℝ)
        + ∑ p ∈ mediumR X, (#(badSet X i p) : ℝ) + ∑ p ∈ largeR X, (#(badSet X i p) : ℝ)) := by
    intro i
    rw [Finset.sum_add_distrib]
    congr 1
    exact_mod_cast sum_badSet_split X i
  rw [Finset.sum_congr rfl (fun i _ => hsplit i)] at hcast
  simp only [Finset.sum_add_distrib] at hcast
  have hX' : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have : (#(failSet X) : ℝ) < X := by linarith
  exact_mod_cast this

/-- **Main theorem, conditional form**: infinitely many `n` satisfy `((n+3)!)² ∣ (2n)!`. -/
theorem infinite_good (hM : MertensAP 210) : Set.Infinite {n : ℕ | Good n} :=
  infinite_good_of_eventually (card_failSet_lt hM)

theorem k3_of_mertensAP (hM : MertensAP 210) : formalConjecturesStatement_k3 :=
  infinite_good hM

/-- `k = 2` follows from `k = 3`. -/
theorem k2_of_k3 : formalConjecturesStatement_k3 → formalConjecturesStatement_k2 := by
  intro h
  unfold formalConjecturesStatement_k2 formalConjecturesStatement_k3 at *
  refine Set.Infinite.mono ?_ h
  intro n hn
  have hn' : (n + 3).factorial ^ 2 ∣ (2 * n).factorial := hn
  show (n + 2).factorial ^ 2 ∣ (2 * n).factorial
  have h1 : (n + 2).factorial ^ 2 ∣ (n + 3).factorial ^ 2 :=
    pow_dvd_pow_of_dvd (Nat.factorial_dvd_factorial (by omega)) 2
  exact h1.trans hn'

theorem k2_of_mertensAP (hM : MertensAP 210) : formalConjecturesStatement_k2 :=
  k2_of_k3 (k3_of_mertensAP hM)

end Erdos727
