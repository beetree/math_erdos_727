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

/-! ### Levels -/

/-- `ρM = 1001/2000 ≥ (p+1)/(2p)` for `p > 1000`. -/
noncomputable def ρM : ℝ := 1001 / 2000

theorem ρM_pos : (0 : ℝ) < ρM := by unfold ρM; norm_num

theorem ρM_le_one : ρM ≤ (1 : ℝ) := by unfold ρM; norm_num

open Classical in
/-- The level of a medium prime: the largest `J ≤ 39` with `p ≤ X^{2/J - η}`. -/
noncomputable def Jlev (X p : ℕ) : ℕ :=
  Nat.findGreatest (fun J : ℕ => (p : ℝ) ≤ (X : ℝ) ^ (2 / (J : ℝ) - η)) 39

theorem Jlev_le_39 (X p : ℕ) : Jlev X p ≤ 39 := by
  unfold Jlev
  exact Nat.findGreatest_le 39

theorem four_le_Jlev {X p : ℕ} (hp : (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 2 - η)) : 4 ≤ Jlev X p := by
  unfold Jlev
  apply Nat.le_findGreatest (by norm_num)
  have : (2 : ℝ) / ((4 : ℕ) : ℝ) - η = 1 / 2 - η := by norm_num
  simp only [this]
  exact hp

theorem le_rpow_Jlev {X p : ℕ} (hp : (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 2 - η)) :
    (p : ℝ) ≤ (X : ℝ) ^ (2 / (Jlev X p : ℝ) - η) := by
  have h4 : (p : ℝ) ≤ (X : ℝ) ^ (2 / ((4 : ℕ) : ℝ) - η) := by
    have : (2 : ℝ) / ((4 : ℕ) : ℝ) - η = 1 / 2 - η := by norm_num
    rw [this]
    exact hp
  have := Nat.findGreatest_spec (P := fun J : ℕ => (p : ℝ) ≤ (X : ℝ) ^ (2 / (J : ℝ) - η))
    (n := 39) (m := 4) (by norm_num) h4
  exact this

theorem rpow_lt_of_Jlev_lt {X p : ℕ} (h : Jlev X p < 39) :
    (X : ℝ) ^ (2 / ((Jlev X p : ℝ) + 1) - η) < p := by
  by_contra hcon
  push Not at hcon
  have h1 : Jlev X p < Jlev X p + 1 := Nat.lt_succ_self _
  have h2 : Jlev X p + 1 ≤ 39 := h
  unfold Jlev at h1 h2 hcon
  refine Nat.findGreatest_is_greatest h1 h2 ?_
  push_cast
  exact hcon

/-- `p^J ≤ X^{2 - ηJ}` when `p ≤ X^{2/J - η}` (for `J ≥ 1`, `X ≥ 1`). -/
theorem pow_le_rpow_of_le_rpow {X p J : ℕ} (hJ : 1 ≤ J)
    (hp : (p : ℝ) ≤ (X : ℝ) ^ (2 / (J : ℝ) - η)) :
    (p : ℝ) ^ J ≤ (X : ℝ) ^ (2 - η * J) := by
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast (by omega : J ≠ 0)
  calc (p : ℝ) ^ J ≤ ((X : ℝ) ^ (2 / (J : ℝ) - η)) ^ J :=
        pow_le_pow_left₀ (Nat.cast_nonneg p) hp J
    _ = (X : ℝ) ^ (2 - η * J) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]
        congr 1
        rw [sub_mul, div_mul_cancel₀ _ hJ0]

/-! ### Parametrisation of the root class -/

/-- The least `v ≥ X` with `v ≡ r (mod p)`. -/
def v₀ (X p r : ℕ) : ℕ := X + (r + p - X % p) % p

theorem v₀_mod {X p r : ℕ} (hp : 0 < p) (hr : r < p) : v₀ X p r % p = r := by
  unfold v₀
  have h1 : X % p < p := Nat.mod_lt _ hp
  rw [Nat.add_mod, Nat.mod_mod, Nat.add_mod_mod, show X % p + (r + p - X % p) = r + p by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt hr]

theorem le_v₀ (X p r : ℕ) : X ≤ v₀ X p r := Nat.le_add_right _ _

theorem v₀_lt {X p : ℕ} (r : ℕ) (hp : 0 < p) : v₀ X p r < X + p := by
  unfold v₀
  have := Nat.mod_lt (r + p - X % p) hp
  omega

/-- The bad set injects into `{z < X/p + 1 : F (v₀ + p z) mod p^J ∈ T}`. -/
theorem card_badSet_le_card_filter {p : ℕ} (hp : p.Prime) (hpY : Y < p) (i : Fin 6) (X : ℕ)
    {J : ℕ} (hJ : 1 ≤ J) {r : ℕ} (hr : r < p) (hroot : ∀ v, p ∣ Lv i v ↔ v % p = r) :
    #(badSet X i p) ≤ #{z ∈ range (X / p + 1) |
      F (v₀ X p r + p * z) % p ^ J ∈ digitSet p (carryDigits p (shift i) J)} := by
  classical
  have hp0 := hp.pos
  have hpY' : 1000 < p := hpY
  have hs1 := shift_pos i
  have hs3 := shift_le_three i
  have hv₀ := v₀_mod (X := X) hp0 hr
  have hwX := le_v₀ X p r
  have hwp := v₀_lt (X := X) r hp0
  set w := v₀ X p r with hw
  have key : ∀ v ∈ badSet X i p, w ≤ v ∧ p ∣ v - w ∧ (v - w) / p < X / p + 1 := by
    intro v hv
    unfold badSet at hv
    rw [mem_filter, mem_Ico] at hv
    obtain ⟨⟨hXv, hv2X⟩, hdvd, -⟩ := hv
    have hvr : v % p = r := (hroot v).mp hdvd
    have hmod : v ≡ w [MOD p] := by
      unfold Nat.ModEq
      rw [hvr, hv₀]
    have hle : w ≤ v := by
      by_contra hlt
      push Not at hlt
      have h1 : p ∣ w - v := (Nat.modEq_iff_dvd' hlt.le).mp hmod
      have h2 : w - v < p := by omega
      have := Nat.eq_zero_of_dvd_of_lt h1 h2
      omega
    refine ⟨hle, (Nat.modEq_iff_dvd' hle).mp hmod.symm, ?_⟩
    have : v - w ≤ X := by omega
    calc (v - w) / p ≤ X / p := Nat.div_le_div_right this
      _ < X / p + 1 := Nat.lt_succ_self _
  refine card_le_card_of_injOn (fun v => (v - w) / p) ?_ ?_
  · intro v hv
    rw [Finset.mem_coe] at hv
    obtain ⟨hle, hdvd, hlt⟩ := key v hv
    have hv' := hv
    unfold badSet at hv'
    rw [mem_filter, mem_Ico] at hv'
    obtain ⟨-, hdvdL, hno⟩ := hv'
    have heq : w + p * ((v - w) / p) = v := by
      rw [Nat.mul_div_cancel' hdvd]
      omega
    show (v - w) / p ∈ {z ∈ range (X / p + 1) |
      F (w + p * z) % p ^ J ∈ digitSet p (carryDigits p (shift i) J)}
    rw [mem_filter, mem_range, heq]
    refine ⟨hlt, ?_⟩
    apply mem_carryDigitSet_of_noCarry hp (by omega) hs1 (by omega) hJ
      (F_mod_eq hp (by omega) i hdvdL)
    intro h h2 _
    exact hno h h2
  · intro v hv v' hv' heq
    rw [Finset.mem_coe] at hv hv'
    simp only at heq
    obtain ⟨hle, hdvd, -⟩ := key v hv
    obtain ⟨hle', hdvd', -⟩ := key v' hv'
    have e1 := Nat.div_mul_cancel hdvd
    have e2 := Nat.div_mul_cancel hdvd'
    rw [heq] at e1
    omega

/-- On the root class, `F (v₀ + p z) ≡ p - shift i (mod p)`. -/
theorem F_v₀_add_mod {p : ℕ} (hp : p.Prime) (hpY : Y < p) (i : Fin 6) {X r : ℕ} (hr : r < p)
    (hroot : ∀ v, p ∣ Lv i v ↔ v % p = r) (z : ℕ) :
    F (v₀ X p r + p * z) % p = p - shift i := by
  have hpY' : 1000 < p := hpY
  apply F_mod_eq hp (by omega) i
  rw [hroot, Nat.add_mul_mod_self_left, v₀_mod hp.pos hr]

theorem dvd_Lv_v₀ {p : ℕ} (hp : p.Prime) (i : Fin 6) {X r : ℕ} (hr : r < p)
    (hroot : ∀ v, p ∣ Lv i v ↔ v % p = r) : p ∣ Lv i (v₀ X p r) := by
  rw [hroot, v₀_mod hp.pos hr]


/-! ### The Weyl-sum bound -/

/-- The bound `Wb2 L p J = 4L²/p + 4L(2 + J log p) + 2p^{J-2}(1 + J log p)` for `‖W(h)‖²`. -/
noncomputable def Wb2 (L p : ℝ) (J : ℕ) : ℝ :=
  4 * L ^ 2 / p + 4 * L * (2 + J * log p) + 2 * p ^ (J - 2) * (1 + J * log p)

theorem Wb2_nonneg {L p : ℝ} (hL : 0 ≤ L) (hp : 1 ≤ p) (J : ℕ) : 0 ≤ Wb2 L p J := by
  have hlog : 0 ≤ log p := Real.log_nonneg hp
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have h1 : 0 ≤ (J : ℝ) * log p := mul_nonneg hJ hlog
  unfold Wb2
  have h2 : 0 ≤ 4 * L ^ 2 / p := by positivity
  have h3 : 0 ≤ 4 * L * (2 + J * log p) := mul_nonneg (by positivity) (by linarith)
  have h4 : 0 ≤ 2 * p ^ (J - 2) * (1 + J * log p) := mul_nonneg (by positivity) (by linarith)
  linarith

theorem Wb2_mono {L L' p : ℝ} (hL : 0 ≤ L) (hLL' : L ≤ L') (hp : 1 ≤ p) (J : ℕ) :
    Wb2 L p J ≤ Wb2 L' p J := by
  have hlog : 0 ≤ log p := Real.log_nonneg hp
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have h1 : 0 ≤ (J : ℝ) * log p := mul_nonneg hJ hlog
  unfold Wb2
  have h2 : 4 * L ^ 2 / p ≤ 4 * L' ^ 2 / p := by gcongr
  have h3 : 4 * L * (2 + J * log p) ≤ 4 * L' * (2 + J * log p) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  linarith

/-- The phase identity `h n(z) / p^J = h' D z²/p^s + h'(2Dw+E) z/p^{s+1} + h' F(w)/p^{s+2}`
for `h = p^t h'`, `J = t + 2 + s`. -/
theorem phase_eq {p : ℕ} (hp0 : (p : ℝ) ≠ 0) (t s h' w z : ℕ) :
    ((p ^ t * h' : ℕ) : ℝ) * (F (w + p * z) : ℝ) / (p : ℝ) ^ (t + 2 + s) =
      ((h' * D : ℕ) : ℝ) / (p : ℝ) ^ s * (z : ℝ) ^ 2
        + ((h' * (2 * D * w + E) : ℕ) : ℝ) / (p : ℝ) ^ (s + 1) * z
        + ((h' * F w : ℕ) : ℝ) / (p : ℝ) ^ (s + 2) := by
  rw [F_eq (w + p * z), F_eq w]
  push_cast
  field_simp
  ring

/-- `p ∤ D` for primes `p > 1000`. -/
theorem not_dvd_D {p : ℕ} (hp : p.Prime) (hpY : Y < p) : ¬ p ∣ D := by
  intro h
  unfold D at h
  have hpY' : 1000 < p := hpY
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  · have := prime_dvd_Q_le hp (hp.dvd_of_dvd_pow h)
    unfold Y at this
    omega

/-- **The Weyl-sum bound**: for `J ≥ 4`, `p^{J-1} ∤ h`, and `p ∣ Lv i w`,
`‖∑_{z<L} e(h F(w + pz) / p^J)‖² ≤ Wb2 L p J`. -/
theorem norm_sq_weyl_le {p : ℕ} (hp : p.Prime) (hpY : Y < p) (i : Fin 6) {w : ℕ}
    (hw : p ∣ Lv i w) {J : ℕ} (hJ : 4 ≤ J) {h : ℕ} (hh : ¬ p ^ (J - 1) ∣ h) (L : ℕ) :
    ‖∑ z ∈ range L, e ((h : ℝ) * F (w + p * z) / p ^ J)‖ ^ 2 ≤ Wb2 L p J := by
  have hpY' : 1000 < p := hpY
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hpR1 : (1 : ℝ) ≤ p := by exact_mod_cast hp0
  have hpR' : (p : ℝ) ≠ 0 := hpR.ne'
  have hlog : 0 ≤ log (p : ℝ) := Real.log_natCast_nonneg p
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  -- factor out the power of `p`
  have hne : h ≠ 0 := by
    rintro rfl
    exact hh (dvd_zero _)
  obtain ⟨t, h', hh', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hne p hp.ne_one
  have ht : t + 2 ≤ J := by
    by_contra hcon
    push Not at hcon
    exact hh ((Nat.pow_dvd_pow p (by omega : J - 1 ≤ t)).mul_right h')
  obtain ⟨s, rfl⟩ : ∃ s, J = t + 2 + s := ⟨J - t - 2, by omega⟩
  have hphase := phase_eq hpR' t s h' w
  have hJR : (0 : ℝ) ≤ ((t + 2 + s : ℕ) : ℝ) := Nat.cast_nonneg _
  have hJlog : 0 ≤ ((t + 2 + s : ℕ) : ℝ) * log p := mul_nonneg hJR hlog
  -- the linear coefficient is not divisible by `p`
  have hlin : ¬ p ∣ h' * (2 * D * w + E) := by
    intro hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
    · exact hh' hd
    · apply not_dvd_D_add_E hp hpY i hw (Nat.ModEq.refl w)
      rw [show D * (w + w) + E = 2 * D * w + E by ring]
      exact hd
  rcases Nat.eq_zero_or_pos s with hs | hs
  · -- `s = 0`: the quadratic coefficient is an integer
    subst hs
    have ht2 : 2 ≤ t := by omega
    obtain ⟨α, hα⟩ : ∃ α : ℝ, α = ((h' * (2 * D * w + E) : ℕ) : ℝ) / p := ⟨_, rfl⟩
    obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = ((h' * F w : ℕ) : ℝ) / (p : ℝ) ^ 2 := ⟨_, rfl⟩
    have hsum : ∑ z ∈ range L,
        e (((p ^ t * h' : ℕ) : ℝ) * (F (w + p * z) : ℝ) / (p : ℝ) ^ (t + 2 + 0))
        = ∑ z ∈ range L, e (α * z + β) := by
      refine Finset.sum_congr rfl fun z _ => ?_
      have key : ((h' * D : ℕ) : ℝ) / (p : ℝ) ^ 0 * (z : ℝ) ^ 2
          + ((h' * (2 * D * w + E) : ℕ) : ℝ) / (p : ℝ) ^ (0 + 1) * z
          + ((h' * F w : ℕ) : ℝ) / (p : ℝ) ^ (0 + 2)
          = α * z + β + (((h' * D * z ^ 2 : ℕ) : ℤ) : ℝ) := by
        rw [hα, hβ]
        push_cast
        ring
      rw [hphase z, key, e_add_int]
    have hdist : 1 / (p : ℝ) ≤ dist₁ α := by
      have := inv_le_dist₁_div hp0 (c := ((h' * (2 * D * w + E) : ℕ) : ℤ))
        (by exact_mod_cast hlin)
      rw [hα]
      push_cast at this ⊢
      exact this
    have hdist0 : dist₁ α ≠ 0 := by
      intro h0
      rw [h0] at hdist
      have := one_div_pos.mpr hpR
      linarith
    have hnorm : ‖∑ z ∈ range L, e (α * z + β)‖ ≤ (p : ℝ) / 2 := by
      calc ‖∑ z ∈ range L, e (α * z + β)‖ ≤ 1 / (2 * dist₁ α) :=
            norm_sum_e_le_inv_dist₁ hdist0 β L
        _ ≤ 1 / (2 * (1 / p)) := one_div_le_one_div_of_le (by positivity) (by linarith)
        _ = p / 2 := by field_simp
    rw [hsum]
    clear hα hβ hphase hsum hdist hdist0 hlin hh
    have hJ2 : t + 2 + 0 - 2 = t := by omega
    rw [Wb2, hJ2]
    have hp2 : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ t := pow_le_pow_right₀ hpR1 ht2
    have hn0 : 0 ≤ ‖∑ z ∈ range L, e (α * z + β)‖ := norm_nonneg _
    have hsq : ‖∑ z ∈ range L, e (α * z + β)‖ ^ 2 ≤ ((p : ℝ) / 2) ^ 2 :=
      pow_le_pow_left₀ hn0 hnorm 2
    have h1 : 0 ≤ 4 * (L : ℝ) ^ 2 / p := by positivity
    have h2 : 0 ≤ 4 * (L : ℝ) * (2 + ((t + 2 + 0 : ℕ) : ℝ) * log p) :=
      mul_nonneg (by positivity) (by linarith)
    have h3 : (p : ℝ) ^ t ≤ (p : ℝ) ^ t * (1 + ((t + 2 + 0 : ℕ) : ℝ) * log p) :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    nlinarith
  · -- `s ≥ 1`: Weyl's inequality with `q = p^s`
    have hq : 0 < p ^ s := pow_pos hp0 s
    have hodd : Odd (p ^ s) := (hp.odd_of_ne_two (by omega)).pow
    have hcop : Nat.Coprime (h' * D) (p ^ s) := by
      apply Nat.Coprime.pow_right
      apply Nat.Coprime.mul_left
      · exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hh').symm
      · exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr (not_dvd_D hp hpY)).symm
    have hgcd : Int.gcd ((h' * D : ℕ) : ℤ) ((p ^ s : ℕ) : ℤ) = 1 := by
      rw [Int.gcd_natCast_natCast]
      exact hcop
    have hweyl := weyl_quadratic hq hodd hgcd (((h' * (2 * D * w + E) : ℕ) : ℝ) / (p : ℝ) ^ (s + 1))
      (((h' * F w : ℕ) : ℝ) / (p : ℝ) ^ (s + 2)) 0 L
    have hsum : ∑ z ∈ range L,
        e (((p ^ t * h' : ℕ) : ℝ) * (F (w + p * z) : ℝ) / (p : ℝ) ^ (t + 2 + s))
        = ∑ z ∈ range L, e ((((h' * D : ℕ) : ℤ) : ℝ) / ((p ^ s : ℕ) : ℝ) * (((0 : ℤ) : ℝ) + z) ^ 2
            + ((h' * (2 * D * w + E) : ℕ) : ℝ) / (p : ℝ) ^ (s + 1) * (((0 : ℤ) : ℝ) + z)
            + ((h' * F w : ℕ) : ℝ) / (p : ℝ) ^ (s + 2)) := by
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [hphase z]
      push_cast
      simp only [zero_add]
    rw [hsum]
    refine le_trans hweyl ?_
    push_cast
    have hpq : (p : ℝ) ≤ (p : ℝ) ^ s := le_self_pow₀ hpR1 (by omega)
    have hqJ : (p : ℝ) ^ s ≤ (p : ℝ) ^ (t + 2 + s - 2) := pow_le_pow_right₀ hpR1 (by omega)
    have hsJ : (s : ℝ) * log p ≤ ((t + 2 + s : ℕ) : ℝ) * log p := by
      apply mul_le_mul_of_nonneg_right _ hlog
      exact_mod_cast (by omega : s ≤ t + 2 + s)
    have hs0 : 0 ≤ (s : ℝ) * log p := mul_nonneg (Nat.cast_nonneg s) hlog
    rw [Real.log_pow]
    have hq0 : 0 < (p : ℝ) ^ s := by positivity
    have e1 : 4 * (L : ℝ) ^ 2 / (p : ℝ) ^ s ≤ 4 * L ^ 2 / p :=
      div_le_div_of_nonneg_left (by positivity) hpR hpq
    have e2 : 2 * (p : ℝ) ^ s * (1 + s * log p) ≤
        2 * (p : ℝ) ^ (t + 2 + s - 2) * (1 + ((t + 2 + s : ℕ) : ℝ) * log p) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
    have e3 : (L : ℝ) * ((s : ℝ) * log p) ≤ L * (((t + 2 + s : ℕ) : ℝ) * log p) :=
      mul_le_mul_of_nonneg_left hsJ hL0
    have expand : (2 * (L : ℝ) / (p : ℝ) ^ s + 1) * (2 * L + 2 * (p : ℝ) ^ s * (1 + s * log p)) =
        4 * L ^ 2 / (p : ℝ) ^ s + 4 * L * (1 + s * log p) + 2 * L
          + 2 * (p : ℝ) ^ s * (1 + s * log p) := by
      field_simp
      ring
    rw [expand]
    unfold Wb2
    nlinarith

/-- **Per-prime bound** (Section 9): for `J ≥ 4`,
`#(badSet X i p) ≤ (X/p + 1) ρ^{J-1} + (2(2 + log p))^J √(Wb2 (X/p + 1) p J)`. -/
theorem card_badSet_le_main_add_err {p : ℕ} (hp : p.Prime) (hpY : Y < p) (i : Fin 6) (X : ℕ)
    {J : ℕ} (hJ : 4 ≤ J) :
    (#(badSet X i p) : ℝ) ≤ ((X : ℝ) / p + 1) * ρM ^ (J - 1) +
      (2 * (2 + log p)) ^ J * √(Wb2 ((X : ℝ) / p + 1) p J) := by
  have hpY' : 1000 < p := hpY
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hpR1 : (1 : ℝ) ≤ p := by exact_mod_cast hp0
  have hlog : 0 ≤ log (p : ℝ) := Real.log_natCast_nonneg p
  have hs1 := shift_pos i
  have hs3 := shift_le_three i
  obtain ⟨r, hr, hroot⟩ := exists_root hp hpY i
  have hcard := card_badSet_le_card_filter hp hpY i X (by omega : 1 ≤ J) hr hroot
  have hn : ∀ z, F (v₀ X p r + p * z) % p = p - shift i := F_v₀_add_mod hp hpY i hr hroot
  have hmain := card_filter_le_main_add_error hp (by omega : 1 ≤ J) hs1 (by omega)
    (fun z => F (v₀ X p r + p * z)) hn (X / p + 1)
  beta_reduce at hmain
  have hF := sum_norm_fourier_digitSet_le hp.two_le (carryDigits p (shift i) J)
    (carryDigits_interval hp0 (by omega) J) (carryDigits_subset_range hp0 hs1 (by omega) J)
  rw [carryDigits_length] at hF
  have hW : ∀ h ∈ (range (p ^ J)).filter (fun h => ¬ p ^ (J - 1) ∣ h),
      ‖∑ z ∈ range (X / p + 1), e ((h : ℝ) * F (v₀ X p r + p * z) / p ^ J)‖
        ≤ √(Wb2 ((X : ℝ) / p + 1) p J) := by
    intro h hh
    rw [mem_filter] at hh
    have h1 := norm_sq_weyl_le hp hpY i (dvd_Lv_v₀ (X := X) hp i hr hroot) hJ hh.2 (X / p + 1)
    have hLR : ((X / p + 1 : ℕ) : ℝ) ≤ (X : ℝ) / p + 1 := by
      push_cast
      gcongr
      exact Nat.cast_div_le
    have h2 := Wb2_mono (Nat.cast_nonneg _) hLR hpR1 J
    rw [← abs_norm]
    exact Real.abs_le_sqrt (h1.trans h2)
  set L := X / p + 1 with hL
  set w := v₀ X p r with hw
  set T := digitSet p (carryDigits p (shift i) J) with hT
  have hLR : (L : ℝ) ≤ (X : ℝ) / p + 1 := by
    rw [hL]
    push_cast
    gcongr
    exact Nat.cast_div_le
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  -- main term
  have hTle : (#T : ℝ) ≤ (((p : ℝ) + 1) / 2) ^ (J - 1) := by
    have h1 := card_carryDigitSet_le p (shift i) (by omega : 1 ≤ J)
    have h2 : (((p + 1) / 2 : ℕ) : ℝ) ≤ ((p : ℝ) + 1) / 2 := by
      have := Nat.cast_div_le (α := ℝ) (m := p + 1) (n := 2)
      push_cast at this
      exact this
    calc (#T : ℝ) ≤ (((p + 1) / 2 : ℕ) : ℝ) ^ (J - 1) := by exact_mod_cast h1
      _ ≤ (((p : ℝ) + 1) / 2) ^ (J - 1) := pow_le_pow_left₀ (by positivity) h2 _
  have hmainle : (L : ℝ) * #T / (p : ℝ) ^ (J - 1) ≤ ((X : ℝ) / p + 1) * ρM ^ (J - 1) := by
    have hρ : ((p : ℝ) + 1) / (2 * p) ≤ ρM := by
      have hp1000 : (1000 : ℝ) < p := by exact_mod_cast hpY'
      unfold ρM
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    calc (L : ℝ) * #T / (p : ℝ) ^ (J - 1)
        ≤ ((X : ℝ) / p + 1) * (((p : ℝ) + 1) / 2) ^ (J - 1) / (p : ℝ) ^ (J - 1) := by
          gcongr
      _ = ((X : ℝ) / p + 1) * (((p : ℝ) + 1) / (2 * p)) ^ (J - 1) := by
          rw [mul_div_assoc, ← div_pow, div_div]
      _ ≤ ((X : ℝ) / p + 1) * ρM ^ (J - 1) := by gcongr
  -- error term
  have herr : (1 / (p : ℝ) ^ J) * ∑ h ∈ (range (p ^ J)).filter (fun h => ¬ p ^ (J - 1) ∣ h),
        ‖fourier (p ^ J) T h‖ * ‖∑ z ∈ range L, e ((h : ℝ) * F (w + p * z) / p ^ J)‖
      ≤ (2 * (2 + log p)) ^ J * √(Wb2 ((X : ℝ) / p + 1) p J) := by
    have hsq : 0 ≤ √(Wb2 ((X : ℝ) / p + 1) p J) := Real.sqrt_nonneg _
    have hpJ : 0 < (p : ℝ) ^ J := by positivity
    calc (1 / (p : ℝ) ^ J) * ∑ h ∈ (range (p ^ J)).filter (fun h => ¬ p ^ (J - 1) ∣ h),
          ‖fourier (p ^ J) T h‖ * ‖∑ z ∈ range L, e ((h : ℝ) * F (w + p * z) / p ^ J)‖
        ≤ (1 / (p : ℝ) ^ J) * ∑ h ∈ (range (p ^ J)).filter (fun h => ¬ p ^ (J - 1) ∣ h),
          ‖fourier (p ^ J) T h‖ * √(Wb2 ((X : ℝ) / p + 1) p J) := by
          gcongr with h hh
          exact hW h hh
      _ = (1 / (p : ℝ) ^ J) * (∑ h ∈ (range (p ^ J)).filter (fun h => ¬ p ^ (J - 1) ∣ h),
          ‖fourier (p ^ J) T h‖) * √(Wb2 ((X : ℝ) / p + 1) p J) := by
          rw [← Finset.sum_mul]
          ring
      _ ≤ (1 / (p : ℝ) ^ J) * (∑ h ∈ range (p ^ J), ‖fourier (p ^ J) T h‖) *
          √(Wb2 ((X : ℝ) / p + 1) p J) := by
          gcongr
          exact filter_subset _ _
      _ ≤ (1 / (p : ℝ) ^ J) * (2 * p * (2 + log p)) ^ J * √(Wb2 ((X : ℝ) / p + 1) p J) := by
          gcongr
      _ = (2 * (2 + log p)) ^ J * √(Wb2 ((X : ℝ) / p + 1) p J) := by
          rw [show (2 * (p : ℝ) * (2 + log p)) = (2 * (2 + log p)) * p by ring, mul_pow]
          field_simp
  calc (#(badSet X i p) : ℝ) ≤ (#{z ∈ range L | F (w + p * z) % p ^ J ∈ T} : ℝ) := by
        exact_mod_cast hcard
    _ ≤ _ := hmain
    _ ≤ _ := add_le_add hmainle herr

/-! ### Uniform smallness of the error term -/

/-- The quantity controlling the error term: `(2(2 + log x))^78 · Ω(x)`. -/
noncomputable def Ωb (x : ℝ) : ℝ :=
  (2 * (2 + log x)) ^ 78 * (16 * x ^ (-(1 / 20 : ℝ)) + 8 * (2 + 39 * log x) * x ^ (-(1 / 2 : ℝ))
    + 2 * (1 + 39 * log x) * x ^ (-(4 * η)))

theorem mul_sqrt_le {A B C : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B) (hC : 0 ≤ C) (h : A ^ 2 * B ≤ C ^ 2) :
    A * √B ≤ C := by
  calc A * √B = √(A ^ 2) * √B := by rw [Real.sqrt_sq hA]
    _ = √(A ^ 2 * B) := (Real.sqrt_mul (by positivity) B).symm
    _ ≤ √(C ^ 2) := Real.sqrt_le_sqrt h
    _ = C := Real.sqrt_sq hC

/-- The error term is at most `X/(10⁴ p)` for `X^{1/20} < p ≤ X^{1/2-η}` once `Ωb X ≤ 10⁻⁸`. -/
theorem err_le {X p : ℕ} (hX : 1 ≤ X) (hΩ : Ωb X ≤ 1 / 10 ^ 8)
    (hp1 : (X : ℝ) ^ ((1 : ℝ) / 20) < p) (hp2 : (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 2 - η)) :
    (2 * (2 + log p)) ^ Jlev X p * √(Wb2 ((X : ℝ) / p + 1) p (Jlev X p)) ≤
      (X : ℝ) / p / 10000 := by
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hlogX : 0 ≤ log (X : ℝ) := Real.log_nonneg hXR
  have hX20 : (1 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 20) := Real.one_le_rpow hXR (by norm_num)
  have hpR1 : (1 : ℝ) < p := lt_of_le_of_lt hX20 hp1
  have hpR : (0 : ℝ) < p := by linarith
  have hlogp : 0 ≤ log (p : ℝ) := Real.log_nonneg hpR1.le
  have hpX : (p : ℝ) ≤ X := by
    calc (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 2 - η) := hp2
      _ ≤ (X : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hXR (by unfold η; norm_num)
      _ = X := Real.rpow_one _
  have hlogpX : log (p : ℝ) ≤ log X := Real.log_le_log hpR hpX
  have hJ4 : 4 ≤ Jlev X p := four_le_Jlev hp2
  have hJ39 : Jlev X p ≤ 39 := Jlev_le_39 X p
  have hpJ0 := le_rpow_Jlev hp2
  set J := Jlev X p with hJ
  have hJR4 : (4 : ℝ) ≤ J := by exact_mod_cast hJ4
  have hJR39 : (J : ℝ) ≤ 39 := by exact_mod_cast hJ39
  set M : ℝ := (X : ℝ) / p with hM
  have hM0 : 0 < M := by positivity
  have hMp : M * p = X := by rw [hM]; field_simp
  -- `p^J ≤ X² X^{-4η}`
  have hpJ : (p : ℝ) ^ J ≤ (X : ℝ) ^ 2 * (X : ℝ) ^ (-(4 * η)) := by
    calc (p : ℝ) ^ J ≤ (X : ℝ) ^ (2 - η * J) := pow_le_rpow_of_le_rpow (by omega) hpJ0
      _ ≤ (X : ℝ) ^ (2 - η * 4) := by
          apply Real.rpow_le_rpow_of_exponent_le hXR
          have : 0 < η := by unfold η; norm_num
          nlinarith
      _ = (X : ℝ) ^ 2 * (X : ℝ) ^ (-(4 * η)) := by
          rw [show (2 - η * 4 : ℝ) = ((2 : ℕ) : ℝ) + (-(4 * η)) by push_cast; ring,
            Real.rpow_add hX0, Real.rpow_natCast]
  have hpJ2 : (p : ℝ) ^ (J - 2) ≤ M ^ 2 * (X : ℝ) ^ (-(4 * η)) := by
    have e : (p : ℝ) ^ (J - 2) * (p : ℝ) ^ 2 = (p : ℝ) ^ J := by
      rw [← pow_add]
      congr 1
      omega
    have hp2pos : 0 < (p : ℝ) ^ 2 := by positivity
    apply le_of_mul_le_mul_right _ hp2pos
    rw [e]
    calc (p : ℝ) ^ J ≤ (X : ℝ) ^ 2 * (X : ℝ) ^ (-(4 * η)) := hpJ
      _ = M ^ 2 * (X : ℝ) ^ (-(4 * η)) * (p : ℝ) ^ 2 := by rw [← hMp]; ring
  -- `1/p ≤ X^{-1/20}` and `p/X ≤ X^{-1/2}`
  have hinvp : 1 / (p : ℝ) ≤ (X : ℝ) ^ (-(1 / 20 : ℝ)) := by
    rw [Real.rpow_neg hX0.le, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hp1.le
  have hpX' : (p : ℝ) / X ≤ (X : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have h1 : (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 2) :=
      hp2.trans (Real.rpow_le_rpow_of_exponent_le hXR (by unfold η; norm_num))
    rw [div_le_iff₀ hX0]
    calc (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 2) := h1
      _ = (X : ℝ) ^ (-(1 / 2 : ℝ) + 1) := by norm_num
      _ = (X : ℝ) ^ (-(1 / 2 : ℝ)) * X := Real.rpow_add_one hX0.ne' _
  -- the bound on `Wb2`
  have hL : (X : ℝ) / p + 1 ≤ 2 * M := by
    have : 1 ≤ (X : ℝ) / p := by
      rw [le_div_iff₀ hpR]
      linarith
    rw [hM]
    linarith
  have hL0 : 0 ≤ (X : ℝ) / p + 1 := by positivity
  set Ω : ℝ := 16 * (X : ℝ) ^ (-(1 / 20 : ℝ)) + 8 * (2 + 39 * log X) * (X : ℝ) ^ (-(1 / 2 : ℝ))
    + 2 * (1 + 39 * log X) * (X : ℝ) ^ (-(4 * η)) with hΩdef
  have hJlog : (J : ℝ) * log p ≤ 39 * log X := by
    calc (J : ℝ) * log p ≤ 39 * log p := mul_le_mul_of_nonneg_right hJR39 hlogp
      _ ≤ 39 * log X := by linarith
  have hJlog0 : 0 ≤ (J : ℝ) * log p := mul_nonneg (by positivity) hlogp
  have hWb2 : Wb2 ((X : ℝ) / p + 1) p J ≤ M ^ 2 * Ω := by
    have t1 : 4 * ((X : ℝ) / p + 1) ^ 2 / p ≤ M ^ 2 * (16 * (X : ℝ) ^ (-(1 / 20 : ℝ))) := by
      calc 4 * ((X : ℝ) / p + 1) ^ 2 / p ≤ 4 * (2 * M) ^ 2 / p := by gcongr
        _ = M ^ 2 * (16 * (1 / p)) := by ring
        _ ≤ M ^ 2 * (16 * (X : ℝ) ^ (-(1 / 20 : ℝ))) := by gcongr
    have t2 : 4 * ((X : ℝ) / p + 1) * (2 + J * log p) ≤
        M ^ 2 * (8 * (2 + 39 * log X) * (X : ℝ) ^ (-(1 / 2 : ℝ))) := by
      have hMpX : M * (p / X) = 1 := by rw [hM]; field_simp
      calc 4 * ((X : ℝ) / p + 1) * (2 + J * log p) ≤ 4 * (2 * M) * (2 + 39 * log X) :=
            mul_le_mul (by gcongr) (by linarith) (by linarith) (by positivity)
        _ = M ^ 2 * (8 * (2 + 39 * log X) * (p / X)) := by
            calc 4 * (2 * M) * (2 + 39 * log X)
                = 8 * (2 + 39 * log X) * M * (M * (p / X)) := by rw [hMpX]; ring
              _ = M ^ 2 * (8 * (2 + 39 * log X) * (p / X)) := by ring
        _ ≤ M ^ 2 * (8 * (2 + 39 * log X) * (X : ℝ) ^ (-(1 / 2 : ℝ))) := by
            have : 0 ≤ 8 * (2 + 39 * log X) := by linarith
            gcongr
    have t3 : 2 * (p : ℝ) ^ (J - 2) * (1 + J * log p) ≤
        M ^ 2 * (2 * (1 + 39 * log X) * (X : ℝ) ^ (-(4 * η))) := by
      calc 2 * (p : ℝ) ^ (J - 2) * (1 + J * log p)
          ≤ 2 * (M ^ 2 * (X : ℝ) ^ (-(4 * η))) * (1 + 39 * log X) :=
            mul_le_mul (by gcongr) (by linarith) (by linarith) (by positivity)
        _ = M ^ 2 * (2 * (1 + 39 * log X) * (X : ℝ) ^ (-(4 * η))) := by ring
    unfold Wb2
    rw [hΩdef, mul_add, mul_add]
    linarith
  -- the bound on the prefactor
  have hA : (2 * (2 + log p)) ^ J ≤ (2 * (2 + log X)) ^ 39 := by
    calc (2 * (2 + log p)) ^ J ≤ (2 * (2 + log X)) ^ J :=
          pow_le_pow_left₀ (by linarith) (by linarith) J
      _ ≤ (2 * (2 + log X)) ^ 39 := pow_le_pow_right₀ (by linarith) hJ39
  have hA0 : 0 ≤ (2 * (2 + log p)) ^ J := pow_nonneg (by linarith) J
  apply mul_sqrt_le hA0 (Wb2_nonneg hL0 hpR1.le J) (by positivity)
  have hΩ' : (2 * (2 + log X)) ^ 78 * Ω ≤ 1 / 10 ^ 8 := by
    unfold Ωb at hΩ
    rw [hΩdef]
    exact hΩ
  have hΩ0 : 0 ≤ Ω := by
    rw [hΩdef]
    have e1 : 0 ≤ (X : ℝ) ^ (-(1 / 20 : ℝ)) := by positivity
    have e2 : 0 ≤ (X : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    have e3 : 0 ≤ (X : ℝ) ^ (-(4 * η)) := by positivity
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (by linarith : 0 ≤ 2 + 39 * log X)) e2
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ 1 + 39 * log X)) e3
    have := mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) e1
    linarith
  calc ((2 * (2 + log p)) ^ J) ^ 2 * Wb2 ((X : ℝ) / p + 1) p J
      ≤ ((2 * (2 + log X)) ^ 39) ^ 2 * (M ^ 2 * Ω) := by
        apply mul_le_mul _ hWb2 (Wb2_nonneg hL0 hpR1.le J) (by positivity)
        exact pow_le_pow_left₀ hA0 hA 2
    _ = M ^ 2 * ((2 * (2 + log X)) ^ 78 * Ω) := by ring
    _ ≤ M ^ 2 * (1 / 10 ^ 8) := by gcongr
    _ = (M / 10000) ^ 2 := by ring

theorem tendsto_log_pow_mul_rpow_neg (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => log x ^ n * x ^ (-c)) atTop (nhds 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (n : ℝ) hc).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.rpow_natCast, Real.rpow_neg hx.le, div_eq_mul_inv]

/-- A majorant of `Ωb` valid for `log x ≥ 1`. -/
noncomputable def Ωc (x : ℝ) : ℝ :=
  6 ^ 78 * (16 * (log x ^ 78 * x ^ (-(1 / 20 : ℝ))) + 328 * (log x ^ 79 * x ^ (-(1 / 2 : ℝ)))
    + 80 * (log x ^ 79 * x ^ (-(4 * η))))

theorem tendsto_Ωc : Tendsto Ωc atTop (nhds 0) := by
  have h1 := tendsto_log_pow_mul_rpow_neg 78 (c := 1 / 20) (by norm_num)
  have h2 := tendsto_log_pow_mul_rpow_neg 79 (c := 1 / 2) (by norm_num)
  have h3 := tendsto_log_pow_mul_rpow_neg 79 (c := 4 * η) (by unfold η; norm_num)
  have h := (((h1.const_mul 16).add (h2.const_mul 328)).add (h3.const_mul 80)).const_mul
    ((6 : ℝ) ^ 78)
  simp only [mul_zero, add_zero] at h
  exact h

theorem Ωb_le_Ωc {x : ℝ} (hx : 1 ≤ log x) (hx0 : 0 < x) : Ωb x ≤ Ωc x := by
  unfold Ωb Ωc
  have h1 : 2 * (2 + log x) ≤ 6 * log x := by linarith
  have h2 : (2 * (2 + log x)) ^ 78 ≤ (6 * log x) ^ 78 := pow_le_pow_left₀ (by linarith) h1 78
  have e1 : 0 ≤ x ^ (-(1 / 20 : ℝ)) := by positivity
  have e2 : 0 ≤ x ^ (-(1 / 2 : ℝ)) := by positivity
  have e3 : 0 ≤ x ^ (-(4 * η)) := by positivity
  have h3 : (2 + 39 * log x) * x ^ (-(1 / 2 : ℝ)) ≤ (41 * log x) * x ^ (-(1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith) e2
  have h4 : (1 + 39 * log x) * x ^ (-(4 * η)) ≤ (40 * log x) * x ^ (-(4 * η)) :=
    mul_le_mul_of_nonneg_right (by linarith) e3
  have hS : 0 ≤ 16 * x ^ (-(1 / 20 : ℝ)) + 8 * (2 + 39 * log x) * x ^ (-(1 / 2 : ℝ))
      + 2 * (1 + 39 * log x) * x ^ (-(4 * η)) := by
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (by linarith : 0 ≤ 2 + 39 * log x)) e2
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ 1 + 39 * log x)) e3
    have := mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) e1
    linarith
  calc (2 * (2 + log x)) ^ 78 * (16 * x ^ (-(1 / 20 : ℝ)) + 8 * (2 + 39 * log x) * x ^ (-(1 / 2 : ℝ))
        + 2 * (1 + 39 * log x) * x ^ (-(4 * η)))
      ≤ (6 * log x) ^ 78 * (16 * x ^ (-(1 / 20 : ℝ)) + 8 * ((41 * log x) * x ^ (-(1 / 2 : ℝ)))
        + 2 * ((40 * log x) * x ^ (-(4 * η)))) := by
        apply mul_le_mul h2 _ hS (by positivity)
        linarith
    _ = 6 ^ 78 * (16 * (log x ^ 78 * x ^ (-(1 / 20 : ℝ))) + 328 * (log x ^ 79 * x ^ (-(1 / 2 : ℝ)))
        + 80 * (log x ^ 79 * x ^ (-(4 * η)))) := by ring

theorem eventually_Ωb : ∀ᶠ X : ℕ in atTop, Ωb X ≤ 1 / 10 ^ 8 := by
  have h1 : ∀ᶠ x : ℝ in atTop, Ωc x < 1 / 10 ^ 8 :=
    tendsto_Ωc.eventually (gt_mem_nhds (by norm_num))
  have h2 : ∀ᶠ x : ℝ in atTop, 1 ≤ log x := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have h3 : ∀ᶠ x : ℝ in atTop, 0 < x := eventually_gt_atTop 0
  have h : ∀ᶠ x : ℝ in atTop, Ωb x ≤ 1 / 10 ^ 8 := by
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    exact (Ωb_le_Ωc hx2 hx3).trans hx1.le
  exact tendsto_natCast_atTop_atTop.eventually h


/-! ### The medium range and its two parts -/

theorem mem_mediumR {X p : ℕ} : p ∈ mediumR X ↔ p.Prime ∧ Y < p ∧ p ≤ 2 * Cb * X ∧
    (X : ℝ) ^ ((1 : ℝ) / 20) < p ∧ (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 2 + η) := by
  unfold mediumR
  rw [Finset.mem_filter, mem_primeRange]
  tauto

theorem card_mediumR_le (X : ℕ) : (#(mediumR X) : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 2 + η) + 1 := by
  have hsub : mediumR X ⊆ Finset.range (⌊(X : ℝ) ^ ((1 : ℝ) / 2 + η)⌋₊ + 1) := by
    intro p hp
    rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (by positivity)]
    exact (mem_mediumR.mp hp).2.2.2.2
  have h := Finset.card_le_card hsub
  rw [Finset.card_range] at h
  calc (#(mediumR X) : ℝ) ≤ ((⌊(X : ℝ) ^ ((1 : ℝ) / 2 + η)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h
    _ = (⌊(X : ℝ) ^ ((1 : ℝ) / 2 + η)⌋₊ : ℝ) + 1 := by push_cast; ring
    _ ≤ (X : ℝ) ^ ((1 : ℝ) / 2 + η) + 1 := by
        gcongr
        exact Nat.floor_le (by positivity)

/-- The proper medium range `X^{1/20} < p ≤ X^{1/2-η}`. -/
noncomputable def properR (X : ℕ) : Finset ℕ :=
  (mediumR X).filter fun p => (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 2 - η)

/-- The strip `X^{1/2-η} < p ≤ X^{1/2+η}`. -/
noncomputable def stripR (X : ℕ) : Finset ℕ := mediumR X \ properR X

theorem properR_subset (X : ℕ) : properR X ⊆ mediumR X := Finset.filter_subset _ _

theorem stripR_subset (X : ℕ) : stripR X ⊆ mediumR X := Finset.sdiff_subset

theorem sum_mediumR_split (X : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ mediumR X, f p = ∑ p ∈ properR X, f p + ∑ p ∈ stripR X, f p := by
  rw [stripR, add_comm, Finset.sum_sdiff (properR_subset X)]

theorem mem_properR {X p : ℕ} (hp : p ∈ properR X) : p.Prime ∧ Y < p ∧ p ≤ 2 * Cb * X ∧
    (X : ℝ) ^ ((1 : ℝ) / 20) < p ∧ (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 2 - η) := by
  unfold properR at hp
  rw [Finset.mem_filter, mem_mediumR] at hp
  exact ⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1, hp.2⟩

theorem mem_stripR {X p : ℕ} (hp : p ∈ stripR X) : p.Prime ∧ Y < p ∧
    (X : ℝ) ^ ((1 : ℝ) / 2 - η) < p ∧ (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 2 + η) := by
  unfold stripR at hp
  rw [Finset.mem_sdiff] at hp
  obtain ⟨hmed, hnot⟩ := hp
  obtain ⟨hpr, hpY, -, -, hle⟩ := mem_mediumR.mp hmed
  refine ⟨hpr, hpY, ?_, hle⟩
  by_contra hcon
  push Not at hcon
  apply hnot
  unfold properR
  rw [Finset.mem_filter]
  exact ⟨hmed, hcon⟩

/-- `X ≥ 1` whenever the medium range is nonempty. -/
theorem pos_of_mem_mediumR {X p : ℕ} (hp : p ∈ mediumR X) : 0 < X := by
  obtain ⟨hpr, -, hpX, -, -⟩ := mem_mediumR.mp hp
  rcases Nat.eq_zero_or_pos X with h | h
  · subst h
    rw [mul_zero] at hpX
    have := hpr.two_le
    omega
  · exact h

/-! ### The strip -/

/-- `badSet X i p` lies in a single class modulo `p`, so it has at most `X / p + 1` elements. -/
theorem card_badSet_le_div_add_one_med {p : ℕ} (hp : p.Prime) (hpY : Y < p) (i : Fin 6) (X : ℕ) :
    (#(badSet X i p) : ℝ) ≤ X / p + 1 := by
  classical
  obtain ⟨r, -, hr⟩ := exists_root hp hpY i
  have hsub : badSet X i p ⊆ {v ∈ Ico X (X + X) | v % p = r} := by
    intro v hv
    unfold badSet at hv
    rw [Finset.mem_filter] at hv ⊢
    rw [two_mul] at hv
    exact ⟨hv.1, (hr v).mp hv.2.1⟩
  calc (#(badSet X i p) : ℝ) ≤ #{v ∈ Ico X (X + X) | v % p = r} := by
        exact_mod_cast card_le_card hsub
    _ ≤ X / p + 1 := card_filter_mod_eq_le_real hp.pos

theorem stripR_subset_primeBlock (X : ℕ) :
    stripR X ⊆ primeBlock X (1 / ((1 : ℝ) / 2 + η)) (1 / ((1 : ℝ) / 2 - η)) := by
  intro p hp
  obtain ⟨hpr, -, hgt, hle⟩ := mem_stripR hp
  unfold primeBlock
  rw [Finset.mem_filter, Nat.mem_primesLE, one_div_one_div, one_div_one_div]
  refine ⟨⟨?_, hpr⟩, hgt⟩
  rw [Nat.le_floor_iff (by positivity)]
  exact hle

/-- `∑_{p ∈ stripR X} 1/p ≤ 5η + 3 C / log X`. -/
theorem sum_inv_stripR_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : ℝ, 2 ≤ x → ∀ a b : ℝ, 1 ≤ a → a ≤ b → 2 ≤ x ^ (1 / b) →
      ∑ p ∈ primeBlock x a b, (1 : ℝ) / p ≤ log (b / a) + C * b / log x)
    {X : ℕ} (hX : 2 ≤ X) (hX2 : 2 ≤ (X : ℝ) ^ ((1 : ℝ) / 2 - η)) :
    ∑ p ∈ stripR X, (1 : ℝ) / p ≤ 5 * η + 3 * (C / log X) := by
  have hXR : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hlog : 0 < log (X : ℝ) := Real.log_pos (by linarith)
  have ha : (1 : ℝ) ≤ 1 / ((1 : ℝ) / 2 + η) := by unfold η; norm_num
  have hab : 1 / ((1 : ℝ) / 2 + η) ≤ 1 / ((1 : ℝ) / 2 - η) := by unfold η; norm_num
  have hb : 1 / ((1 : ℝ) / 2 - η) ≤ 3 := by unfold η; norm_num
  have h1 := hC X hXR _ _ ha hab (by rw [one_div_one_div]; exact hX2)
  have h2 : log ((1 / ((1 : ℝ) / 2 - η)) / (1 / ((1 : ℝ) / 2 + η))) ≤ 5 * η := by
    have := Real.log_le_sub_one_of_pos
      (x := (1 / ((1 : ℝ) / 2 - η)) / (1 / ((1 : ℝ) / 2 + η))) (by unfold η; norm_num)
    have e : (1 / ((1 : ℝ) / 2 - η)) / (1 / ((1 : ℝ) / 2 + η)) - 1 ≤ 5 * η := by
      unfold η
      norm_num
    linarith
  have h3 : C * (1 / ((1 : ℝ) / 2 - η)) / log X ≤ 3 * (C / log X) := by
    have hCl : 0 ≤ C / log X := div_nonneg hC0 hlog.le
    calc C * (1 / ((1 : ℝ) / 2 - η)) / log X = (C / log X) * (1 / ((1 : ℝ) / 2 - η)) := by ring
      _ ≤ (C / log X) * 3 := mul_le_mul_of_nonneg_left hb hCl
      _ = 3 * (C / log X) := by ring
  calc ∑ p ∈ stripR X, (1 : ℝ) / p
      ≤ ∑ p ∈ primeBlock X (1 / ((1 : ℝ) / 2 + η)) (1 / ((1 : ℝ) / 2 - η)), (1 : ℝ) / p :=
        Finset.sum_le_sum_of_subset_of_nonneg (stripR_subset_primeBlock X)
          (fun _ _ _ => by positivity)
    _ ≤ _ := h1
    _ ≤ 5 * η + 3 * (C / log X) := add_le_add h2 h3

/-- The strip contributes at most `X (5η + 3C/log X) + #(mediumR X)`. -/
theorem sum_stripR_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : ℝ, 2 ≤ x → ∀ a b : ℝ, 1 ≤ a → a ≤ b → 2 ≤ x ^ (1 / b) →
      ∑ p ∈ primeBlock x a b, (1 : ℝ) / p ≤ log (b / a) + C * b / log x)
    {X : ℕ} (hX : 2 ≤ X) (hX2 : 2 ≤ (X : ℝ) ^ ((1 : ℝ) / 2 - η)) (i : Fin 6) :
    ∑ p ∈ stripR X, (#(badSet X i p) : ℝ) ≤ X * (5 * η + 3 * (C / log X)) + #(mediumR X) := by
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  calc ∑ p ∈ stripR X, (#(badSet X i p) : ℝ) ≤ ∑ p ∈ stripR X, ((X : ℝ) * (1 / p) + 1) := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨hpr, hpY, -, -⟩ := mem_stripR hp
        rw [mul_one_div]
        exact card_badSet_le_div_add_one_med hpr hpY i X
    _ = X * ∑ p ∈ stripR X, (1 : ℝ) / p + #(stripR X) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum]
    _ ≤ X * (5 * η + 3 * (C / log X)) + #(mediumR X) := by
        have h1 := sum_inv_stripR_le hC0 hC hX hX2
        have h2 : (#(stripR X) : ℝ) ≤ #(mediumR X) := by
          exact_mod_cast Finset.card_le_card (stripR_subset X)
        have h3 := mul_le_mul_of_nonneg_left h1 hX0
        linarith

/-! ### The proper range: grouping by level -/

theorem fibre_subset_primeBlock_med {X J : ℕ} (hJ4 : 4 ≤ J) (hJ39 : J ≤ 39) :
    (properR X).filter (fun p => Jlev X p = J) ⊆
      primeBlock X (1 / (2 / (J : ℝ) - η)) (1 / (2 / ((J : ℝ) + 1) - η)) := by
  intro p hp
  rw [Finset.mem_filter] at hp
  obtain ⟨hp, hJ⟩ := hp
  have hX : 0 < X := pos_of_mem_mediumR (properR_subset X hp)
  obtain ⟨hpr, -, -, h20, hle⟩ := mem_properR hp
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  unfold primeBlock
  rw [Finset.mem_filter, Nat.mem_primesLE, one_div_one_div, one_div_one_div]
  refine ⟨⟨?_, hpr⟩, ?_⟩
  · rw [Nat.le_floor_iff (by positivity)]
    have := le_rpow_Jlev hle
    rw [hJ] at this
    exact this
  · rcases lt_or_eq_of_le hJ39 with h | h
    · have := rpow_lt_of_Jlev_lt (X := X) (p := p) (by rw [hJ]; exact h)
      rw [hJ] at this
      exact this
    · subst h
      refine lt_of_le_of_lt ?_ h20
      apply Real.rpow_le_rpow_of_exponent_le hXR
      unfold η
      norm_num

/-- The harmonic sum over the primes at level `J`. -/
theorem sum_fibre_le_med {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : ℝ, 2 ≤ x → ∀ a b : ℝ, 1 ≤ a → a ≤ b → 2 ≤ x ^ (1 / b) →
      ∑ p ∈ primeBlock x a b, (1 : ℝ) / p ≤ log (b / a) + C * b / log x)
    {X : ℕ} (hX : 2 ≤ X) (hX20 : 2 ≤ (X : ℝ) ^ ((1 : ℝ) / 20 - η))
    {J : ℕ} (hJ4 : 4 ≤ J) (hJ39 : J ≤ 39) :
    ∑ p ∈ (properR X).filter (fun p => Jlev X p = J), (1 : ℝ) / p ≤
      1 / J + 1 / 10 ^ 5 + 21 * (C / log X) := by
  have hXR : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hXR1 : (1 : ℝ) ≤ X := by linarith
  have hlog : 0 < log (X : ℝ) := Real.log_pos (by linarith)
  have hCl : 0 ≤ C / log X := div_nonneg hC0 hlog.le
  have hJR : (4 : ℝ) ≤ J := by exact_mod_cast hJ4
  have hJR' : (J : ℝ) ≤ 39 := by exact_mod_cast hJ39
  have hJ0 : (0 : ℝ) < J := by linarith
  have hη : (0 : ℝ) < η := by unfold η; norm_num
  have h20 : 1 / 20 ≤ 2 / ((J : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  have hJJ : 2 / ((J : ℝ) + 1) ≤ 2 / J :=
    div_le_div_of_nonneg_left (by norm_num) hJ0 (by linarith)
  have hb0 : 0 < 2 / ((J : ℝ) + 1) - η := by
    have : η ≤ 1 / 20 := by unfold η; norm_num
    have : η ≠ 1 / 20 := by unfold η; norm_num
    have : η < 1 / 20 := lt_of_le_of_ne ‹_› ‹_›
    linarith
  have ha0 : 0 < 2 / (J : ℝ) - η := by linarith
  have ha1 : 1 ≤ 1 / (2 / (J : ℝ) - η) := by
    apply one_le_one_div ha0
    have : 2 / (J : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hJ0]
      linarith
    linarith
  have hab : 1 / (2 / (J : ℝ) - η) ≤ 1 / (2 / ((J : ℝ) + 1) - η) :=
    one_div_le_one_div_of_le hb0 (by linarith)
  have hb21 : 1 / (2 / ((J : ℝ) + 1) - η) ≤ 21 := by
    rw [div_le_iff₀ hb0]
    have : η ≤ 1 / 1000 := by unfold η; norm_num
    linarith
  have hX2 : 2 ≤ (X : ℝ) ^ (1 / (1 / (2 / ((J : ℝ) + 1) - η))) := by
    rw [one_div_one_div]
    refine hX20.trans (Real.rpow_le_rpow_of_exponent_le hXR1 ?_)
    linarith
  have h1 := hC X hXR _ _ ha1 hab hX2
  have hlogba : log ((1 / (2 / ((J : ℝ) + 1) - η)) / (1 / (2 / (J : ℝ) - η))) ≤
      1 / J + 1 / 10 ^ 5 := by
    have hpos : 0 < (1 / (2 / ((J : ℝ) + 1) - η)) / (1 / (2 / (J : ℝ) - η)) :=
      div_pos (one_div_pos.mpr hb0) (one_div_pos.mpr ha0)
    refine (Real.log_le_sub_one_of_pos hpos).trans ?_
    unfold η
    interval_cases J <;> norm_num
  have h3 : C * (1 / (2 / ((J : ℝ) + 1) - η)) / log X ≤ 21 * (C / log X) := by
    calc C * (1 / (2 / ((J : ℝ) + 1) - η)) / log X
        = (C / log X) * (1 / (2 / ((J : ℝ) + 1) - η)) := by ring
      _ ≤ (C / log X) * 21 := mul_le_mul_of_nonneg_left hb21 hCl
      _ = 21 * (C / log X) := by ring
  calc ∑ p ∈ (properR X).filter (fun p => Jlev X p = J), (1 : ℝ) / p
      ≤ ∑ p ∈ primeBlock X (1 / (2 / (J : ℝ) - η)) (1 / (2 / ((J : ℝ) + 1) - η)), (1 : ℝ) / p :=
        Finset.sum_le_sum_of_subset_of_nonneg (fibre_subset_primeBlock_med hJ4 hJ39)
          (fun _ _ _ => by positivity)
    _ ≤ _ := h1
    _ ≤ 1 / J + 1 / 10 ^ 5 + 21 * (C / log X) := add_le_add hlogba h3

/-- The numerical series `∑_{J=4}^{39} ρ^{J-1}/J ≤ 0.0535`. -/
theorem sum_ρ_div_le : ∑ J ∈ Finset.Icc (4 : ℕ) 39, ρM ^ (J - 1) / (J : ℝ) ≤ 535 / 10000 := by
  have hρ0 := ρM_pos
  have hρ1 : ρM < 1 := by unfold ρM; norm_num
  have hIcc : Finset.Icc (4 : ℕ) 39 = Finset.Ico (4 : ℕ) 40 := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, ← Finset.sum_Ico_consecutive _ (show 4 ≤ 8 by norm_num) (show 8 ≤ 40 by norm_num)]
  have h1 : ∑ J ∈ Finset.Ico (4 : ℕ) 8, ρM ^ (J - 1) / (J : ℝ) ≤ 514 / 10000 := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [Finset.sum_range_succ, ρM]
  have h2 : ∑ J ∈ Finset.Ico (8 : ℕ) 40, ρM ^ (J - 1) / (J : ℝ) ≤ 20 / 10000 := by
    have hterm : ∀ J ∈ Finset.Ico (8 : ℕ) 40, ρM ^ (J - 1) / (J : ℝ) ≤ (1 / (8 * ρM)) * ρM ^ J := by
      intro J hJ
      rw [Finset.mem_Ico] at hJ
      have hJR : (8 : ℝ) ≤ J := by exact_mod_cast hJ.1
      have e : ρM ^ J = ρM ^ (J - 1) * ρM := by
        rw [← pow_succ]
        congr 1
        omega
      calc ρM ^ (J - 1) / (J : ℝ) ≤ ρM ^ (J - 1) / 8 :=
            div_le_div_of_nonneg_left (pow_nonneg hρ0.le _) (by norm_num) hJR
        _ = (1 / (8 * ρM)) * ρM ^ J := by
            rw [e]
            field_simp
    calc ∑ J ∈ Finset.Ico (8 : ℕ) 40, ρM ^ (J - 1) / (J : ℝ)
        ≤ ∑ J ∈ Finset.Ico (8 : ℕ) 40, (1 / (8 * ρM)) * ρM ^ J := Finset.sum_le_sum hterm
      _ = (1 / (8 * ρM)) * ∑ J ∈ Finset.Ico (8 : ℕ) 40, ρM ^ J := by rw [Finset.mul_sum]
      _ ≤ (1 / (8 * ρM)) * (ρM ^ 8 / (1 - ρM)) := by
          gcongr
          exact geom_sum_Ico_le_of_lt_one hρ0.le hρ1
      _ ≤ 20 / 10000 := by
          unfold ρM
          norm_num
  linarith

/-- The main terms over the proper range: `∑_p ρ^{J(p)-1}/p ≤ 0.0535 + 36 (10⁻⁵ + 21 C/log X)`. -/
theorem sum_main_properR_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : ℝ, 2 ≤ x → ∀ a b : ℝ, 1 ≤ a → a ≤ b → 2 ≤ x ^ (1 / b) →
      ∑ p ∈ primeBlock x a b, (1 : ℝ) / p ≤ log (b / a) + C * b / log x)
    {X : ℕ} (hX : 2 ≤ X) (hX20 : 2 ≤ (X : ℝ) ^ ((1 : ℝ) / 20 - η)) :
    ∑ p ∈ properR X, ρM ^ (Jlev X p - 1) / p ≤
      535 / 10000 + 36 * (1 / 10 ^ 5 + 21 * (C / log X)) := by
  have hXR : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hlog : 0 < log (X : ℝ) := Real.log_pos (by linarith)
  have hδ : 0 ≤ 1 / 10 ^ 5 + 21 * (C / log X) := by
    have := div_nonneg hC0 hlog.le
    positivity
  have hmaps : ∀ p ∈ properR X, Jlev X p ∈ Finset.Icc (4 : ℕ) 39 := by
    intro p hp
    rw [Finset.mem_Icc]
    exact ⟨four_le_Jlev (mem_properR hp).2.2.2.2, Jlev_le_39 X p⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ J ∈ Finset.Icc (4 : ℕ) 39, ∑ p ∈ (properR X).filter (fun p => Jlev X p = J),
          ρM ^ (Jlev X p - 1) / p
      = ∑ J ∈ Finset.Icc (4 : ℕ) 39,
          ρM ^ (J - 1) * ∑ p ∈ (properR X).filter (fun p => Jlev X p = J), (1 : ℝ) / p := by
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [(Finset.mem_filter.mp hp).2]
        ring
    _ ≤ ∑ J ∈ Finset.Icc (4 : ℕ) 39, ρM ^ (J - 1) * (1 / J + (1 / 10 ^ 5 + 21 * (C / log X))) := by
        refine Finset.sum_le_sum fun J hJ => ?_
        rw [Finset.mem_Icc] at hJ
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ρM_pos.le _)
        have := sum_fibre_le_med hC0 hC hX hX20 hJ.1 hJ.2
        linarith
    _ = ∑ J ∈ Finset.Icc (4 : ℕ) 39, ρM ^ (J - 1) / J
          + ∑ J ∈ Finset.Icc (4 : ℕ) 39, ρM ^ (J - 1) * (1 / 10 ^ 5 + 21 * (C / log X)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun J _ => ?_
        ring
    _ ≤ 535 / 10000 + 36 * (1 / 10 ^ 5 + 21 * (C / log X)) := by
        have h1 := sum_ρ_div_le
        have h2 : ∑ J ∈ Finset.Icc (4 : ℕ) 39, ρM ^ (J - 1) * (1 / 10 ^ 5 + 21 * (C / log X))
            ≤ 36 * (1 / 10 ^ 5 + 21 * (C / log X)) := by
          calc ∑ J ∈ Finset.Icc (4 : ℕ) 39, ρM ^ (J - 1) * (1 / 10 ^ 5 + 21 * (C / log X))
              ≤ ∑ J ∈ Finset.Icc (4 : ℕ) 39, 1 * (1 / 10 ^ 5 + 21 * (C / log X)) := by
                refine Finset.sum_le_sum fun J _ => ?_
                exact mul_le_mul_of_nonneg_right (pow_le_one₀ ρM_pos.le ρM_le_one) hδ
            _ = 36 * (1 / 10 ^ 5 + 21 * (C / log X)) := by
                rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
                norm_num
        linarith

theorem properR_subset_primeBlock (X : ℕ) : properR X ⊆ primeBlock X 2 20 := by
  intro p hp
  have hX : 0 < X := pos_of_mem_mediumR (properR_subset X hp)
  obtain ⟨hpr, -, -, h20, hle⟩ := mem_properR hp
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  unfold primeBlock
  rw [Finset.mem_filter, Nat.mem_primesLE]
  refine ⟨⟨?_, hpr⟩, h20⟩
  rw [Nat.le_floor_iff (by positivity)]
  exact hle.trans (Real.rpow_le_rpow_of_exponent_le hXR (by unfold η; norm_num))

/-- `∑_{p ∈ properR X} 1/p ≤ log 10 + 20 C / log X ≤ 9 + 20 C / log X`. -/
theorem sum_inv_properR_le {C : ℝ}
    (hC : ∀ x : ℝ, 2 ≤ x → ∀ a b : ℝ, 1 ≤ a → a ≤ b → 2 ≤ x ^ (1 / b) →
      ∑ p ∈ primeBlock x a b, (1 : ℝ) / p ≤ log (b / a) + C * b / log x)
    {X : ℕ} (hX : 2 ≤ X) (hX20 : 2 ≤ (X : ℝ) ^ ((1 : ℝ) / 20)) :
    ∑ p ∈ properR X, (1 : ℝ) / p ≤ 9 + 20 * (C / log X) := by
  have hXR : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have h1 := hC X hXR 2 20 (by norm_num) (by norm_num) hX20
  have h2 : log ((20 : ℝ) / 2) ≤ 9 := by
    have := Real.log_le_sub_one_of_pos (x := (20 : ℝ) / 2) (by norm_num)
    linarith
  calc ∑ p ∈ properR X, (1 : ℝ) / p ≤ ∑ p ∈ primeBlock X 2 20, (1 : ℝ) / p :=
        Finset.sum_le_sum_of_subset_of_nonneg (properR_subset_primeBlock X)
          (fun _ _ _ => by positivity)
    _ ≤ log (20 / 2) + C * 20 / log X := h1
    _ ≤ 9 + 20 * (C / log X) := by
        have : C * 20 / log X = 20 * (C / log X) := by ring
        linarith

/-- The proper range, all together. -/
theorem sum_properR_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : ℝ, 2 ≤ x → ∀ a b : ℝ, 1 ≤ a → a ≤ b → 2 ≤ x ^ (1 / b) →
      ∑ p ∈ primeBlock x a b, (1 : ℝ) / p ≤ log (b / a) + C * b / log x)
    {X : ℕ} (hX : 2 ≤ X) (hX20 : 2 ≤ (X : ℝ) ^ ((1 : ℝ) / 20 - η)) (hΩ : Ωb X ≤ 1 / 10 ^ 8)
    (i : Fin 6) :
    ∑ p ∈ properR X, (#(badSet X i p) : ℝ) ≤
      X * (535 / 10000 + 36 * (1 / 10 ^ 5 + 21 * (C / log X))) + #(mediumR X)
        + X / 10000 * (9 + 20 * (C / log X)) := by
  have hX1 : 1 ≤ X := by omega
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hX20' : 2 ≤ (X : ℝ) ^ ((1 : ℝ) / 20) :=
    hX20.trans (Real.rpow_le_rpow_of_exponent_le hXR (by unfold η; norm_num))
  have hterm : ∀ p ∈ properR X, (#(badSet X i p) : ℝ) ≤
      ((X : ℝ) / p + 1) * ρM ^ (Jlev X p - 1) + (X : ℝ) / p / 10000 := by
    intro p hp
    obtain ⟨hpr, hpY, -, h20, hle⟩ := mem_properR hp
    have h1 := card_badSet_le_main_add_err hpr hpY i X (four_le_Jlev hle)
    have h2 := err_le hX1 hΩ h20 hle
    linarith
  have hmain := sum_main_properR_le hC0 hC hX hX20
  have hcount : ∑ p ∈ properR X, ρM ^ (Jlev X p - 1) ≤ (#(mediumR X) : ℝ) := by
    calc ∑ p ∈ properR X, ρM ^ (Jlev X p - 1) ≤ ∑ p ∈ properR X, (1 : ℝ) :=
          Finset.sum_le_sum fun p _ => pow_le_one₀ ρM_pos.le ρM_le_one
      _ = #(properR X) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ #(mediumR X) := by exact_mod_cast Finset.card_le_card (properR_subset X)
  have hinv := sum_inv_properR_le hC hX hX20'
  calc ∑ p ∈ properR X, (#(badSet X i p) : ℝ)
      ≤ ∑ p ∈ properR X, (((X : ℝ) / p + 1) * ρM ^ (Jlev X p - 1) + (X : ℝ) / p / 10000) :=
        Finset.sum_le_sum hterm
    _ = X * ∑ p ∈ properR X, ρM ^ (Jlev X p - 1) / p + ∑ p ∈ properR X, ρM ^ (Jlev X p - 1)
          + X / 10000 * ∑ p ∈ properR X, (1 : ℝ) / p := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
    _ ≤ X * (535 / 10000 + 36 * (1 / 10 ^ 5 + 21 * (C / log X))) + #(mediumR X)
          + X / 10000 * (9 + 20 * (C / log X)) := by
        have h1 := mul_le_mul_of_nonneg_left hmain hX0
        have h2 := mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ X / 10000)
        linarith


/-- **Sections 9 and 10**: medium primes and boundary strips. -/
theorem medium_bound : ∀ᶠ X : ℕ in atTop,
    (∑ i, ∑ p ∈ mediumR X, #(badSet X i p) : ℝ) ≤ (35 / 100) * X := by
  obtain ⟨C, hC0, hC⟩ := sum_inv_prime_block
  have ev1 : ∀ᶠ X : ℕ in atTop, Ωb X ≤ 1 / 10 ^ 8 := eventually_Ωb
  have ev2 : ∀ᶠ X : ℕ in atTop, (2 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 20 - η) :=
    ((tendsto_rpow_atTop (by unfold η; norm_num)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have ev3 : ∀ᶠ X : ℕ in atTop, max 1 (10 ^ 7 * C) ≤ log (X : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have ev4 : ∀ᶠ X : ℕ in atTop, (X : ℝ) ^ ((1 : ℝ) / 2 + η) + 1 ≤ (X : ℝ) / 10 ^ 4 := by
    have h1 : Tendsto (fun x : ℝ => x ^ (-((1 : ℝ) / 2 - η)) + x⁻¹) atTop (nhds 0) := by
      have := (tendsto_rpow_neg_atTop (y := (1 : ℝ) / 2 - η) (by unfold η; norm_num)).add
        (tendsto_inv_atTop_zero (𝕜 := ℝ))
      rw [add_zero] at this
      exact this
    have h2 : ∀ᶠ x : ℝ in atTop, x ^ (-((1 : ℝ) / 2 - η)) + x⁻¹ < 1 / 10 ^ 4 :=
      h1.eventually (gt_mem_nhds (by norm_num))
    have h3 : ∀ᶠ x : ℝ in atTop, x ^ ((1 : ℝ) / 2 + η) + 1 ≤ x / 10 ^ 4 := by
      filter_upwards [h2, eventually_gt_atTop 0] with x hx hx0
      have e : x ^ ((1 : ℝ) / 2 + η) + 1 = x * (x ^ (-((1 : ℝ) / 2 - η)) + x⁻¹) := by
        rw [mul_add, mul_inv_cancel₀ hx0.ne',
          show ((1 : ℝ) / 2 + η) = 1 + (-((1 : ℝ) / 2 - η)) by ring, Real.rpow_add hx0,
          Real.rpow_one]
      rw [e]
      calc x * (x ^ (-((1 : ℝ) / 2 - η)) + x⁻¹) ≤ x * (1 / 10 ^ 4) :=
            mul_le_mul_of_nonneg_left hx.le hx0.le
        _ = x / 10 ^ 4 := by ring
    exact tendsto_natCast_atTop_atTop.eventually h3
  have ev5 : ∀ᶠ X : ℕ in atTop, 2 ≤ X := eventually_ge_atTop 2
  filter_upwards [ev1, ev2, ev3, ev4, ev5] with X hX1 hX2 hX3 hX4 hX5
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hlog1 : 1 ≤ log (X : ℝ) := le_trans (le_max_left _ _) hX3
  have hlogC : 10 ^ 7 * C ≤ log (X : ℝ) := le_trans (le_max_right _ _) hX3
  have hlog : 0 < log (X : ℝ) := by linarith
  have hCl : C / log X ≤ 1 / 10 ^ 7 := by
    rw [div_le_iff₀ hlog]
    linarith
  have hX2' : 2 ≤ (X : ℝ) ^ ((1 : ℝ) / 2 - η) :=
    hX2.trans (Real.rpow_le_rpow_of_exponent_le hXR (by unfold η; norm_num))
  have hmed : (#(mediumR X) : ℝ) ≤ X / 10 ^ 4 := (card_mediumR_le X).trans hX4
  have hform : ∀ i : Fin 6, ∑ p ∈ mediumR X, (#(badSet X i p) : ℝ) ≤ (56 / 1000) * X := by
    intro i
    rw [sum_mediumR_split]
    have h1 := sum_properR_le hC0 hC hX5 hX2 hX1 i
    have h2 := sum_stripR_le hC0 hC hX5 hX2' i
    have h3 := mul_le_mul_of_nonneg_left hCl hX0
    unfold η at h2
    nlinarith
  calc (∑ i, ∑ p ∈ mediumR X, #(badSet X i p) : ℝ)
      ≤ ∑ i : Fin 6, (56 / 1000) * (X : ℝ) := Finset.sum_le_sum fun i _ => hform i
    _ = 6 * ((56 / 1000) * X) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
    _ ≤ (35 / 100) * X := by nlinarith

end Erdos727
