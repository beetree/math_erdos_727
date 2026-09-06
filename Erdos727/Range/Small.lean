import Erdos727.Ranges
import Erdos727.DigitSets

/-!
# Very small primes (Section 7)

For a prime `1000 < p ≤ X^{1/20}` put `ℓ = ℓ(p) = ⌊log X / (2 log p)⌋`, realised as
`Nat.log p (Nat.sqrt X)`, so that `p^ℓ ≤ √X` and `ℓ ≥ 10`.  By `card_badSet_le`,

  `#(badSet X i p) ≤ ((p+1)/2)^(ℓ-1) (X / p^ℓ + 1) ≤ (X / p) ρ_p^(ℓ-1) + p^(ℓ-1)`,

with `ρ_p = (p+1)/(2p) ≤ ρ = 1001/2000`.  The second terms sum to `O(√X · X^{1/20}) = o(X)`.
For the first, group the primes by `m = ℓ(p) ≥ 10`: those with `ℓ(p) = m` satisfy
`X^{1/(2m+2)} < p ≤ X^{1/(2m)}`, and `sum_inv_prime_block` bounds `∑ 1/p` over that block by
`log ((2m+2)/(2m)) + C (2m+2) / log X ≤ 1/m + C (2m+2) / log X`.  Hence

  `∑_p (1/p) ρ^(ℓ(p)-1) ≤ ∑_{m ≥ 10} ρ^(m-1) (1/m + C(2m+2)/log X) ≤ ρ^9 / (10 (1-ρ)) + O(1/log X)`,

and `6 · ρ^9 / (10(1-ρ)) < 6 · 0.0004 < 0.02`.
-/

namespace Erdos727

open Finset Real Filter

/-- `ρ = 1001/2000`. -/
noncomputable def ρ : ℝ := 1001 / 2000

/-- The number of levels used at a small prime: `p^(ℓ X p) ≤ √X`. -/
def ℓ (X p : ℕ) : ℕ := Nat.log p (Nat.sqrt X)

theorem sqrt_ne_zero_of_one_le {X : ℕ} (hX : 1 ≤ X) : Nat.sqrt X ≠ 0 := by
  rw [Ne, Nat.sqrt_eq_zero]
  omega

theorem pow_ℓ_le {X p : ℕ} (_hp : 2 ≤ p) (hX : 1 ≤ X) : p ^ ℓ X p ≤ Nat.sqrt X :=
  Nat.pow_log_le_self p (sqrt_ne_zero_of_one_le hX)

theorem sqrt_lt_pow_ℓ_succ {X p : ℕ} (hp : 2 ≤ p) : Nat.sqrt X < p ^ (ℓ X p + 1) :=
  Nat.lt_pow_succ_log_self hp _

theorem ten_le_ℓ {X p : ℕ} (hp : 2 ≤ p) (h : (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 20)) : 10 ≤ ℓ X p := by
  have h20 : ((p : ℝ)) ^ (20 : ℕ) ≤ (X : ℝ) := by
    calc ((p : ℝ)) ^ (20 : ℕ) ≤ ((X : ℝ) ^ ((1 : ℝ) / 20)) ^ (20 : ℕ) :=
          pow_le_pow_left₀ (by positivity) h 20
      _ = (X : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg X)]
          norm_num
  have h20' : p ^ 20 ≤ X := by exact_mod_cast h20
  have hsq : p ^ 10 ≤ Nat.sqrt X := by
    rw [Nat.le_sqrt]
    calc p ^ 10 * p ^ 10 = p ^ 20 := by ring
      _ ≤ X := h20'
  exact Nat.le_log_of_pow_le (by omega) hsq

/-- The block containing the primes with `ℓ X p = m`, for `m ≥ 1`:
`X^{1/(2m+2)} < p ≤ X^{1/(2m)}`. -/
theorem ℓ_eq_imp' {X p m : ℕ} (hp : 2 ≤ p) (hX : 1 ≤ X) (hm : 1 ≤ m) (h : ℓ X p = m) :
    (X : ℝ) ^ (1 / (2 * (m : ℝ) + 2)) < p ∧ (p : ℝ) ≤ (X : ℝ) ^ (1 / (2 * (m : ℝ))) := by
  have h1 : p ^ m ≤ Nat.sqrt X := h ▸ pow_ℓ_le hp hX
  have h2 : Nat.sqrt X < p ^ (m + 1) := h ▸ sqrt_lt_pow_ℓ_succ hp
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  constructor
  · have hlt : X < p ^ (2 * m + 2) := by
      calc X < (Nat.sqrt X + 1) ^ 2 := Nat.lt_succ_sqrt' X
        _ ≤ (p ^ (m + 1)) ^ 2 := Nat.pow_le_pow_left h2 2
        _ = p ^ (2 * m + 2) := by rw [← pow_mul]; ring_nf
    have hltR : (X : ℝ) < (p : ℝ) ^ (2 * m + 2) := by exact_mod_cast hlt
    have hn : (2 * m + 2 : ℕ) ≠ 0 := by omega
    have key : (1 / (2 * (m : ℝ) + 2)) = ((2 * m + 2 : ℕ) : ℝ)⁻¹ := by push_cast; ring
    rw [key]
    calc (X : ℝ) ^ (((2 * m + 2 : ℕ) : ℝ)⁻¹)
        < ((p : ℝ) ^ (2 * m + 2)) ^ (((2 * m + 2 : ℕ) : ℝ)⁻¹) :=
          Real.rpow_lt_rpow hX0 hltR (by positivity)
      _ = p := Real.pow_rpow_inv_natCast hp0 hn
  · have hle : p ^ (2 * m) ≤ X := by
      calc p ^ (2 * m) = (p ^ m) ^ 2 := by rw [← pow_mul]; ring_nf
        _ ≤ (Nat.sqrt X) ^ 2 := Nat.pow_le_pow_left h1 2
        _ ≤ X := Nat.sqrt_le' X
    have hleR : (p : ℝ) ^ (2 * m) ≤ (X : ℝ) := by exact_mod_cast hle
    have hn : (2 * m : ℕ) ≠ 0 := by omega
    have hpos : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * m)
    have key : (1 / (2 * (m : ℝ))) = ((2 * m : ℕ) : ℝ)⁻¹ := by push_cast; ring
    rw [key]
    calc (p : ℝ) = ((p : ℝ) ^ (2 * m)) ^ (((2 * m : ℕ) : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast hp0 hn).symm
      _ ≤ (X : ℝ) ^ (((2 * m : ℕ) : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hleR (inv_pos.mpr hpos).le

/-- The per-prime bound in real form. -/
theorem card_badSet_le_real {p : ℕ} (hp : p.Prime) (hpY : Y < p) (i : Fin 6) (X : ℕ)
    {m : ℕ} (hm : 1 ≤ m) (hℓ : ℓ X p = m) :
    (#(badSet X i p) : ℝ) ≤ (X / p) * ρ ^ (m - 1) + (p : ℝ) ^ (m - 1) := by
  have hN := card_badSet_le hp hpY i X hm
  have hpR : (1000 : ℝ) < p := by unfold Y at hpY; exact_mod_cast hpY
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hcast : (#(badSet X i p) : ℝ) ≤
      (((p + 1) / 2 : ℕ) : ℝ) ^ k * (((X / p ^ (k + 1) : ℕ) : ℝ) + 1) := by
    exact_mod_cast hN
  have h1 : (((p + 1) / 2 : ℕ) : ℝ) ≤ ((p : ℝ) + 1) / 2 := by
    have := Nat.cast_div_le (α := ℝ) (m := p + 1) (n := 2)
    push_cast at this
    exact this
  have h2 : (((X / p ^ (k + 1) : ℕ) : ℝ)) ≤ (X : ℝ) / (p : ℝ) ^ (k + 1) := by
    have := Nat.cast_div_le (α := ℝ) (m := X) (n := p ^ (k + 1))
    push_cast at this
    exact this
  have hpos : (0 : ℝ) < p := by linarith
  have hp0 : (p : ℝ) ≠ 0 := hpos.ne'
  calc (#(badSet X i p) : ℝ)
      ≤ (((p + 1) / 2 : ℕ) : ℝ) ^ k * (((X / p ^ (k + 1) : ℕ) : ℝ) + 1) := hcast
    _ ≤ (((p : ℝ) + 1) / 2) ^ k * ((X : ℝ) / (p : ℝ) ^ (k + 1) + 1) := by
        gcongr
    _ = (X / p) * (((p : ℝ) + 1) / (2 * p)) ^ k + (((p : ℝ) + 1) / 2) ^ k := by
        have e : (((p : ℝ) + 1) / (2 * p)) ^ k = (((p : ℝ) + 1) / 2) ^ k / (p : ℝ) ^ k := by
          rw [← div_pow, div_div]
        rw [e, pow_succ]
        generalize ((p : ℝ) + 1) / 2 = A
        field_simp
    _ ≤ (X / p) * ρ ^ k + (p : ℝ) ^ k := by
        gcongr
        · unfold ρ
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
        · linarith

/-! ### Auxiliary facts about `smallR` -/

theorem mem_smallR {X p : ℕ} :
    p ∈ smallR X ↔ p.Prime ∧ Y < p ∧ p ≤ 2 * Cb * X ∧ (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 20) := by
  unfold smallR
  rw [Finset.mem_filter, mem_primeRange]
  tauto

theorem smallR_subset_range (X : ℕ) :
    smallR X ⊆ Finset.range (⌊(X : ℝ) ^ ((1 : ℝ) / 20)⌋₊ + 1) := by
  intro p hp
  rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (by positivity)]
  exact (mem_smallR.mp hp).2.2.2

theorem card_smallR_le (X : ℕ) : (#(smallR X) : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 20) + 1 := by
  have h := Finset.card_le_card (smallR_subset_range X)
  rw [Finset.card_range] at h
  calc (#(smallR X) : ℝ) ≤ ((⌊(X : ℝ) ^ ((1 : ℝ) / 20)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h
    _ = (⌊(X : ℝ) ^ ((1 : ℝ) / 20)⌋₊ : ℝ) + 1 := by push_cast; ring
    _ ≤ (X : ℝ) ^ ((1 : ℝ) / 20) + 1 := by
        gcongr
        exact Nat.floor_le (by positivity)

/-- **(7.2)**: the error terms `p^(ℓ-1)` sum to at most `X / 1000` once `X ≥ 3^20`. -/
theorem sum_pow_ℓ_le {X : ℕ} (hX : 3 ^ 20 ≤ X) :
    ∑ p ∈ smallR X, (p : ℝ) ^ (ℓ X p - 1) ≤ (X : ℝ) / 1000 := by
  set y : ℝ := (X : ℝ) ^ ((1 : ℝ) / 20) with hy
  have hy0 : 0 ≤ y := by positivity
  have hy20 : y ^ 20 = X := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg X)]
    norm_num
  have hX3 : (3 : ℝ) ^ 20 ≤ X := by exact_mod_cast hX
  have hy3 : 3 ≤ y := by
    by_contra hcon
    push Not at hcon
    have := pow_lt_pow_left₀ hcon hy0 (by norm_num : (20 : ℕ) ≠ 0)
    linarith
  have hX1 : 1 ≤ X := le_trans (by norm_num) hX
  have hsqrt : (Nat.sqrt X : ℝ) ≤ y ^ 10 := by
    rw [← pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) (two_ne_zero)]
    calc (Nat.sqrt X : ℝ) ^ 2 = ((Nat.sqrt X ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ X := by exact_mod_cast Nat.sqrt_le' X
      _ = (y ^ 10) ^ 2 := by rw [← pow_mul, hy20]
  have hterm : ∀ p ∈ smallR X, (p : ℝ) ^ (ℓ X p - 1) ≤ y ^ 10 := by
    intro p hp
    have hp2 : 2 ≤ p := (mem_smallR.mp hp).1.two_le
    have : p ^ (ℓ X p - 1) ≤ Nat.sqrt X :=
      (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)).trans (pow_ℓ_le hp2 hX1)
    calc (p : ℝ) ^ (ℓ X p - 1) ≤ (Nat.sqrt X : ℝ) := by exact_mod_cast this
      _ ≤ y ^ 10 := hsqrt
  have hy10 : 0 ≤ y ^ 10 := by positivity
  have h9 : (3 : ℝ) ^ 9 ≤ y ^ 9 := pow_le_pow_left₀ (by norm_num) hy3 9
  have hkey : 1000 * (y + 1) ≤ y ^ 9 * y := by
    nlinarith [mul_le_mul_of_nonneg_right h9 hy0]
  calc ∑ p ∈ smallR X, (p : ℝ) ^ (ℓ X p - 1) ≤ ∑ p ∈ smallR X, y ^ 10 := Finset.sum_le_sum hterm
    _ = #(smallR X) * y ^ 10 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (y + 1) * y ^ 10 := by gcongr; exact card_smallR_le X
    _ ≤ y ^ 20 / 1000 := by
        rw [le_div_iff₀ (by norm_num)]
        have : y ^ 20 = y ^ 9 * y * y ^ 10 := by ring
        rw [this]
        nlinarith [mul_le_mul_of_nonneg_right hkey hy10]
    _ = X / 1000 := by rw [hy20]

/-! ### The main terms -/

theorem ℓ_add_one_le_log {X p : ℕ} (hp : 4 ≤ p) (hX : 1 ≤ X) (hℓ : 1 ≤ ℓ X p) :
    ℓ X p + 1 ≤ Nat.log 2 (Nat.sqrt X) := by
  apply Nat.le_log_of_pow_le (by norm_num)
  have h2 : 2 ≤ 2 ^ ℓ X p := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ X p := Nat.pow_le_pow_right (by norm_num) hℓ
  calc 2 ^ (ℓ X p + 1) = 2 * 2 ^ ℓ X p := by ring
    _ ≤ 2 ^ ℓ X p * 2 ^ ℓ X p := Nat.mul_le_mul_right _ h2
    _ = 4 ^ ℓ X p := by rw [← mul_pow]; norm_num
    _ ≤ p ^ ℓ X p := Nat.pow_le_pow_left hp _
    _ ≤ Nat.sqrt X := pow_ℓ_le (by omega) hX

theorem fibre_subset_primeBlock {X m : ℕ} (hX : 1 ≤ X) (hm : 1 ≤ m) :
    (smallR X).filter (fun p => ℓ X p = m) ⊆ primeBlock (X : ℝ) (2 * m) (2 * m + 2) := by
  intro p hp
  rw [Finset.mem_filter] at hp
  obtain ⟨hp, hℓ⟩ := hp
  have hprime := (mem_smallR.mp hp).1
  obtain ⟨h1, h2⟩ := ℓ_eq_imp' hprime.two_le hX hm hℓ
  unfold primeBlock
  rw [Finset.mem_filter, Nat.mem_primesLE]
  refine ⟨⟨?_, hprime⟩, h1⟩
  rw [Nat.le_floor_iff (by positivity)]
  exact h2

theorem two_le_rpow_of_le_log {X m : ℕ} (hm : m + 1 ≤ Nat.log 2 (Nat.sqrt X)) :
    (2 : ℝ) ≤ (X : ℝ) ^ (1 / (2 * (m : ℝ) + 2)) := by
  have hne : Nat.sqrt X ≠ 0 := by
    intro h0
    rw [h0, Nat.log_zero_right] at hm
    omega
  have h1 : 2 ^ (m + 1) ≤ Nat.sqrt X := Nat.pow_le_of_le_log hne hm
  have h2 : 2 ^ (2 * m + 2) ≤ X := by
    calc 2 ^ (2 * m + 2) = (2 ^ (m + 1)) ^ 2 := by rw [← pow_mul]; ring_nf
      _ ≤ (Nat.sqrt X) ^ 2 := Nat.pow_le_pow_left h1 2
      _ ≤ X := Nat.sqrt_le' X
  have h2R : (2 : ℝ) ^ (2 * m + 2) ≤ (X : ℝ) := by exact_mod_cast h2
  have hn : (2 * m + 2 : ℕ) ≠ 0 := by omega
  have key : (1 / (2 * (m : ℝ) + 2)) = ((2 * m + 2 : ℕ) : ℝ)⁻¹ := by push_cast; ring
  rw [key]
  calc (2 : ℝ) = ((2 : ℝ) ^ (2 * m + 2)) ^ (((2 * m + 2 : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (by norm_num) hn).symm
    _ ≤ (X : ℝ) ^ (((2 * m + 2 : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h2R (by positivity)

/-- The harmonic sum over the primes with `ℓ X p = m`. -/
theorem sum_fibre_le {C : ℝ}
    (hC : ∀ x : ℝ, 2 ≤ x → ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      2 ≤ x ^ (1 / b) → ∑ p ∈ primeBlock x a b, (1 : ℝ) / p ≤ log (b / a) + C * b / log x)
    {X m : ℕ} (hX : 2 ≤ X) (hm : 1 ≤ m) (hmM : m + 1 ≤ Nat.log 2 (Nat.sqrt X)) :
    ∑ p ∈ (smallR X).filter (fun p => ℓ X p = m), (1 : ℝ) / p
      ≤ 1 / m + C * (2 * m + 2) / log X := by
  have hX1 : 1 ≤ X := by omega
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  calc ∑ p ∈ (smallR X).filter (fun p => ℓ X p = m), (1 : ℝ) / p
      ≤ ∑ p ∈ primeBlock (X : ℝ) (2 * m) (2 * m + 2), (1 : ℝ) / p :=
        Finset.sum_le_sum_of_subset_of_nonneg (fibre_subset_primeBlock hX1 hm)
          (fun p _ _ => by positivity)
    _ ≤ log ((2 * m + 2) / (2 * m)) + C * (2 * m + 2) / log X :=
        hC X (by exact_mod_cast hX) (2 * m) (2 * m + 2) (by linarith) (by linarith)
          (two_le_rpow_of_le_log hmM)
    _ ≤ 1 / m + C * (2 * m + 2) / log X := by
        gcongr
        have h := Real.log_le_sub_one_of_pos (x := (2 * (m : ℝ) + 2) / (2 * m)) (by positivity)
        have h' : (2 * (m : ℝ) + 2) / (2 * m) - 1 = 1 / m := by field_simp; ring
        linarith

theorem ρ_pos : (0 : ℝ) < ρ := by unfold ρ; norm_num

/-- The per-level term bound: `ρ^(m-1) (1/m + D (2m+2)) ≤ ρ^m / 5 + 12 D (3ρ/2)^m` for `m ≥ 10`. -/
theorem term_bound {D : ℝ} (hD : 0 ≤ D) {m : ℕ} (hm : 10 ≤ m) :
    ρ ^ (m - 1) * (1 / (m : ℝ) + D * (2 * m + 2)) ≤ ρ ^ m / 5 + D * (12 * (3 / 2 * ρ) ^ m) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hn : (9 : ℝ) ≤ n := by exact_mod_cast (by omega : 9 ≤ n)
  have hρn : (0 : ℝ) ≤ ρ ^ n := pow_nonneg ρ_pos.le n
  have hbern : 1 + (n : ℝ) * (1 / 2) ≤ (1 + 1 / 2) ^ n := one_add_mul_le_pow (by norm_num) n
  have h32 : (1 + 1 / 2 : ℝ) = 3 / 2 := by norm_num
  rw [h32] at hbern
  have h1 : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ ρ / 5 := by
    push_cast
    unfold ρ
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h2 : (2 * ((n + 1 : ℕ) : ℝ) + 2) ≤ 18 * ρ * (3 / 2) ^ n := by
    push_cast
    unfold ρ
    nlinarith [hbern]
  calc ρ ^ n * (1 / ((n + 1 : ℕ) : ℝ) + D * (2 * ((n + 1 : ℕ) : ℝ) + 2))
      = ρ ^ n * (1 / ((n + 1 : ℕ) : ℝ)) + D * (ρ ^ n * (2 * ((n + 1 : ℕ) : ℝ) + 2)) := by ring
    _ ≤ ρ ^ n * (ρ / 5) + D * (ρ ^ n * (18 * ρ * (3 / 2) ^ n)) := by gcongr
    _ = ρ ^ (n + 1) / 5 + D * (12 * (3 / 2 * ρ) ^ (n + 1)) := by ring

theorem sum_geom_ρ_le (M : ℕ) : ∑ m ∈ Finset.Ico 10 M, ρ ^ m / 5 ≤ 4 / 10000 := by
  rw [← Finset.sum_div]
  have h := geom_sum_Ico_le_of_lt_one (x := ρ) (m := 10) (n := M) ρ_pos.le (by unfold ρ; norm_num)
  have h' : ρ ^ 10 / (1 - ρ) ≤ 4 / 10000 * 5 := by unfold ρ; norm_num
  rw [div_le_iff₀ (by norm_num)]
  linarith

theorem sum_geom_σ_le (M : ℕ) : ∑ m ∈ Finset.Ico 10 M, 12 * (3 / 2 * ρ) ^ m ≤ 4 := by
  rw [← Finset.mul_sum]
  have h := geom_sum_Ico_le_of_lt_one (x := 3 / 2 * ρ) (m := 10) (n := M)
    (by unfold ρ; norm_num) (by unfold ρ; norm_num)
  have h' : (3 / 2 * ρ) ^ 10 / (1 - 3 / 2 * ρ) ≤ 4 / 12 := by unfold ρ; norm_num
  linarith

/-- The main terms: `∑_{p ∈ smallR X} ρ^(ℓ-1) / p ≤ 0.0004 + 4 C / log X`. -/
theorem sum_main_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : ℝ, 2 ≤ x → ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      2 ≤ x ^ (1 / b) → ∑ p ∈ primeBlock x a b, (1 : ℝ) / p ≤ log (b / a) + C * b / log x)
    {X : ℕ} (hX : 2 ≤ X) :
    ∑ p ∈ smallR X, ρ ^ (ℓ X p - 1) / p ≤ 4 / 10000 + C / log X * 4 := by
  have hX1 : 1 ≤ X := by omega
  have hlog : 0 < log X := Real.log_pos (by exact_mod_cast hX)
  have hD0 : 0 ≤ C / log X := div_nonneg hC0 hlog.le
  have hmaps : ∀ p ∈ smallR X, ℓ X p ∈ Finset.Ico 10 (Nat.log 2 (Nat.sqrt X)) := by
    intro p hp
    obtain ⟨hprime, hpY, -, hp20⟩ := mem_smallR.mp hp
    have h10 := ten_le_ℓ hprime.two_le hp20
    rw [Finset.mem_Ico]
    refine ⟨h10, ?_⟩
    have := ℓ_add_one_le_log (X := X) (p := p) (by unfold Y at hpY; omega) hX1 (by omega)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ m ∈ Finset.Ico 10 (Nat.log 2 (Nat.sqrt X)),
          ∑ p ∈ (smallR X).filter (fun p => ℓ X p = m), ρ ^ (ℓ X p - 1) / p
      = ∑ m ∈ Finset.Ico 10 (Nat.log 2 (Nat.sqrt X)),
          ρ ^ (m - 1) * ∑ p ∈ (smallR X).filter (fun p => ℓ X p = m), (1 : ℝ) / p := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [(Finset.mem_filter.mp hp).2]
        ring
    _ ≤ ∑ m ∈ Finset.Ico 10 (Nat.log 2 (Nat.sqrt X)),
          ρ ^ (m - 1) * (1 / m + C * (2 * m + 2) / log X) := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [Finset.mem_Ico] at hm
        exact mul_le_mul_of_nonneg_left (sum_fibre_le hC hX (by omega) (by omega))
          (pow_nonneg ρ_pos.le _)
    _ = ∑ m ∈ Finset.Ico 10 (Nat.log 2 (Nat.sqrt X)),
          ρ ^ (m - 1) * (1 / m + C / log X * (2 * m + 2)) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        ring
    _ ≤ ∑ m ∈ Finset.Ico 10 (Nat.log 2 (Nat.sqrt X)),
          (ρ ^ m / 5 + C / log X * (12 * (3 / 2 * ρ) ^ m)) :=
        Finset.sum_le_sum fun m hm => term_bound hD0 (Finset.mem_Ico.mp hm).1
    _ = (∑ m ∈ Finset.Ico 10 (Nat.log 2 (Nat.sqrt X)), ρ ^ m / 5)
          + C / log X * ∑ m ∈ Finset.Ico 10 (Nat.log 2 (Nat.sqrt X)), 12 * (3 / 2 * ρ) ^ m := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 4 / 10000 + C / log X * 4 := by
        gcongr
        · exact sum_geom_ρ_le _
        · exact sum_geom_σ_le _

/-- **Section 7**: very small primes. -/
theorem small_bound : ∀ᶠ X : ℕ in atTop,
    (∑ i, ∑ p ∈ smallR X, #(badSet X i p) : ℝ) ≤ (2 / 100) * X := by
  obtain ⟨C, hC0, hC⟩ := sum_inv_prime_block
  rw [Filter.eventually_atTop]
  refine ⟨max (3 ^ 20) ⌈Real.exp (10000 * C)⌉₊, fun X hX => ?_⟩
  have hX3 : 3 ^ 20 ≤ X := le_trans (le_max_left _ _) hX
  have hXe : ⌈Real.exp (10000 * C)⌉₊ ≤ X := le_trans (le_max_right _ _) hX
  have hX2 : 2 ≤ X := le_trans (by norm_num) hX3
  have hX1 : 1 ≤ X := by omega
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hlog : 0 < log X := Real.log_pos (by exact_mod_cast hX2)
  have hlogC : 10000 * C ≤ log X := by
    have h1 : Real.exp (10000 * C) ≤ X := (Nat.le_ceil _).trans (by exact_mod_cast hXe)
    calc 10000 * C = log (Real.exp (10000 * C)) := (Real.log_exp _).symm
      _ ≤ log X := Real.log_le_log (Real.exp_pos _) h1
  have hD : C / log X * 4 ≤ 4 / 10000 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hlog (by norm_num)]
    nlinarith
  have hi : ∀ i : Fin 6, ∑ p ∈ smallR X, (#(badSet X i p) : ℝ)
      ≤ (X : ℝ) * (4 / 10000 + C / log X * 4) + X / 1000 := by
    intro i
    calc ∑ p ∈ smallR X, (#(badSet X i p) : ℝ)
        ≤ ∑ p ∈ smallR X, ((X / p) * ρ ^ (ℓ X p - 1) + (p : ℝ) ^ (ℓ X p - 1)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          obtain ⟨hprime, hpY, -, hp20⟩ := mem_smallR.mp hp
          exact card_badSet_le_real hprime hpY i X
            (by have := ten_le_ℓ hprime.two_le hp20; omega) rfl
      _ = (X : ℝ) * ∑ p ∈ smallR X, ρ ^ (ℓ X p - 1) / p
            + ∑ p ∈ smallR X, (p : ℝ) ^ (ℓ X p - 1) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
      _ ≤ (X : ℝ) * (4 / 10000 + C / log X * 4) + X / 1000 := by
          gcongr
          · exact sum_main_le hC0 hC hX2
          · exact sum_pow_ℓ_le hX3
  calc (∑ i, ∑ p ∈ smallR X, #(badSet X i p) : ℝ)
      ≤ ∑ i : Fin 6, ((X : ℝ) * (4 / 10000 + C / log X * 4) + X / 1000) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = 6 * ((X : ℝ) * (4 / 10000 + C / log X * 4) + X / 1000) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
    _ ≤ (2 / 100) * X := by
        nlinarith [mul_nonneg hX0 (sub_nonneg.mpr hD)]

end Erdos727
