import Erdos727.Defs

/-!
# Elementary counting lemmas

Counting integers in an interval lying in prescribed residue classes.
-/

namespace Erdos727

open Finset

/-- At most `N / m + 1` integers of `Ico X (X + N)` lie in a given residue class modulo `m`. -/
theorem card_filter_mod_eq_le {X N m r : ℕ} (hm : 0 < m) :
    #{v ∈ Ico X (X + N) | v % m = r} ≤ N / m + 1 := by
  -- The map `v ↦ (v - X) / m` sends the filtered set into `range (N / m + 1)` injectively.
  have key : ∀ v ∈ {v ∈ Ico X (X + N) | v % m = r}, (v - X) / m ∈ range (N / m + 1) := by
    intro v hv
    simp only [mem_filter, mem_Ico] at hv
    rw [mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_right (by omega)
  refine (card_le_card_of_injOn (fun v => (v - X) / m) key ?_).trans (by simp)
  have aux : ∀ v v', X ≤ v → X ≤ v' → v ≤ v' → v % m = v' % m →
      (v - X) / m = (v' - X) / m → v = v' := by
    intro v v' hv hv' hle hmod hdiv
    have h1 : m ∣ v' - v := (Nat.modEq_iff_dvd' hle).1 hmod
    have h2 : v' - v < m := by
      have e1 := Nat.div_add_mod (v - X) m
      have e2 := Nat.div_add_mod (v' - X) m
      have e3 := Nat.mod_lt (v' - X) hm
      rw [hdiv] at e1
      omega
    have := Nat.eq_zero_of_dvd_of_lt h1 h2
    omega
  intro v hv v' hv' h
  simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq] at hv hv'
  simp only at h
  rcases le_total v v' with hle | hle
  · exact aux v v' hv.1.1 hv'.1.1 hle (by rw [hv.2, hv'.2]) h
  · exact (aux v' v hv'.1.1 hv.1.1 hle (by rw [hv.2, hv'.2]) h.symm).symm

/-- At most `#T * (N / m + 1)` integers of `Ico X (X + N)` have residue in `T` modulo `m`. -/
theorem card_filter_mod_mem_le {X N m : ℕ} (hm : 0 < m) (T : Finset ℕ) :
    #{v ∈ Ico X (X + N) | v % m ∈ T} ≤ #T * (N / m + 1) := by
  have hsub : {v ∈ Ico X (X + N) | v % m ∈ T} ⊆
      T.biUnion (fun r => {v ∈ Ico X (X + N) | v % m = r}) := by
    intro v hv
    simp only [mem_filter] at hv
    simp only [mem_biUnion, mem_filter]
    exact ⟨v % m, hv.2, hv.1, rfl⟩
  exact (card_le_card hsub).trans
    (card_biUnion_le_card_mul _ _ _ fun r _ => card_filter_mod_eq_le hm)

/-- Real-valued form: `#{v ∈ Ico X (X+N) | v % m = r} ≤ N / m + 1`. -/
theorem card_filter_mod_eq_le_real {X N m r : ℕ} (hm : 0 < m) :
    (#{v ∈ Ico X (X + N) | v % m = r} : ℝ) ≤ N / m + 1 := by
  calc (#{v ∈ Ico X (X + N) | v % m = r} : ℝ) ≤ ((N / m + 1 : ℕ) : ℝ) := by
        exact_mod_cast card_filter_mod_eq_le (r := r) hm
    _ ≤ N / m + 1 := by
        push_cast
        gcongr
        exact Nat.cast_div_le

/-- If `g` is injective on the residue classes modulo `m` that matter, counting preimages
reduces to counting residues: for a function `g : ℕ → ℕ` with
`g v ≡ g v' [MOD M] → v ≡ v' [MOD M]` on a residue class `v % m = r`, the number of
`v ∈ Ico X (X + N)` with `v % m = r` and `g v % M ∈ T` is at most `#T * (N / M + 1)`. -/
theorem card_filter_image_mod_le {X N m M r : ℕ} (hM : 0 < M) (g : ℕ → ℕ) (T : Finset ℕ)
    (hinj : ∀ v v', v % m = r → v' % m = r → g v % M = g v' % M → v % M = v' % M) :
    #{v ∈ Ico X (X + N) | v % m = r ∧ g v % M ∈ T} ≤ #T * (N / M + 1) := by
  have hsub : {v ∈ Ico X (X + N) | v % m = r ∧ g v % M ∈ T} ⊆
      T.biUnion (fun s => {v ∈ Ico X (X + N) | v % m = r ∧ g v % M = s}) := by
    intro v hv
    simp only [mem_filter] at hv
    simp only [mem_biUnion, mem_filter]
    exact ⟨g v % M, hv.2.2, hv.1, hv.2.1, rfl⟩
  refine (card_le_card hsub).trans (card_biUnion_le_card_mul _ _ _ fun s _ => ?_)
  rcases ({v ∈ Ico X (X + N) | v % m = r ∧ g v % M = s}).eq_empty_or_nonempty with
    h | ⟨v₀, hv₀⟩
  · rw [h, card_empty]; exact Nat.zero_le _
  · simp only [mem_filter] at hv₀
    refine (card_le_card ?_).trans
      (card_filter_mod_eq_le (X := X) (N := N) (r := v₀ % M) hM)
    intro v hv
    simp only [mem_filter] at hv ⊢
    exact ⟨hv.1, hinj v v₀ hv.2.1 hv₀.2.1 (hv.2.2.trans hv₀.2.2.symm)⟩

end Erdos727
