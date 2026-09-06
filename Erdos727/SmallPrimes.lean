import Erdos727.Carries
import Erdos727.Polynomial

/-!
# One progression handles every prime at most 1000 (Section 4)

For the six primes `p ∈ S = {2, 3, 5, 7, 13, 181}` dividing `G(0) = 180·181·182` we fix
exponents `e_p = v_p(180·181·182)`, `b_p > max_j v_p(179 + j)`, `k_p = b_p + 2 e_p`, and an
explicit local witness `t_p ≡ 0 (mod p)` with

  `f(t_p) ≡ (179 mod p^{b_p}) + p^{b_p} (p^{2 e_p} - 1)  (mod p^{k_p})`.

Every `t ≡ t_p (mod p^{k_p})` then has `v_p(f t + j) = v_p(179 + j)` and a block of `2 e_p`
consecutive digits `p - 1`, hence `carry p (f t) ≥ 2 e_p = 2 v_p(A (f t))`.
For the other primes `p ≤ 1000` we impose `t ≡ 0 (mod p)`, so that `p ∤ A (f t)`.
The Chinese remainder theorem produces the progression `t = t₀ + Q v`.

Witness table (checked by `decide`/`norm_num` below):

| p   | e_p | b_p | k_p | t_p        |
|-----|-----|-----|-----|------------|
| 2   | 3   | 3   | 9   | 248        |
| 3   | 2   | 3   | 7   | 1107       |
| 5   | 1   | 2   | 4   | 300        |
| 7   | 1   | 2   | 4   | 196        |
| 13  | 1   | 2   | 4   | 17238      |
| 181 | 1   | 2   | 4   | 491349478  |
-/

namespace Erdos727

open Finset

/-- `e_p = v_p(180 · 181 · 182)` for `p ∈ S` (and `0` otherwise). -/
def eS (p : ℕ) : ℕ := if p = 2 then 3 else if p = 3 then 2 else if p ∈ S then 1 else 0

/-- `b_p`, exceeding every `v_p(179 + j)`. -/
def bS (p : ℕ) : ℕ := if p = 2 then 3 else if p = 3 then 3 else if p ∈ S then 2 else 0

/-- `k_p = b_p + 2 e_p`. -/
def kS (p : ℕ) : ℕ := bS p + 2 * eS p

/-- The local witnesses `t_p`. -/
def tS (p : ℕ) : ℕ :=
  if p = 2 then 248 else if p = 3 then 1107 else if p = 5 then 300 else if p = 7 then 196
  else if p = 13 then 17238 else if p = 181 then 491349478 else 0

/-- The modulus imposed at the prime `p ≤ 1000`. -/
def modulus (p : ℕ) : ℕ := if p ∈ S then p ^ kS p else p

/-- The residue imposed at the prime `p ≤ 1000`. -/
def residue (p : ℕ) : ℕ := if p ∈ S then tS p else 0

/-- The primes `p ≤ 1000`. -/
def smallPrimes : Finset ℕ := (range (Y + 1)).filter Nat.Prime

theorem mem_S_iff {p : ℕ} : p ∈ S ↔ p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 181 := by
  simp [S]

theorem prime_of_mem_S {p : ℕ} (hp : p ∈ S) : p.Prime := by
  rw [mem_S_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- `A (f 0) = 180 · 181 · 182 = 5929560`. -/
theorem A_f_zero_eq : A (f 0) = 5929560 := by
  norm_num [A, f]

/-- `v_p(n) = e` follows from `p^e ∣ n` and `p^(e+1) ∤ n`. -/
theorem factorization_eq_of_dvd_of_not_dvd {p n e : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (h1 : p ^ e ∣ n) (h2 : ¬ p ^ (e + 1) ∣ n) : n.factorization p = e := by
  rw [hp.pow_dvd_iff_le_factorization hn] at h1 h2
  omega

/-- `v_p(n) < b` follows from `p^b ∤ n`. -/
theorem factorization_lt_of_not_dvd {p n b : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (h : ¬ p ^ b ∣ n) : n.factorization p < b := by
  rw [hp.pow_dvd_iff_le_factorization hn] at h
  omega

theorem mem_S_of_dvd_A_f_zero {p : ℕ} (hp : p.Prime) (h : p ∣ A (f 0)) : p ∈ S := by
  rw [A_f_zero_eq, show (5929560 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 * 7 * 13 * 181 by norm_num] at h
  rw [hp.dvd_mul, hp.dvd_mul, hp.dvd_mul, hp.dvd_mul, hp.dvd_mul] at h
  rw [mem_S_iff]
  rcases h with ((((h | h) | h) | h) | h) | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)))
  · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)))))

/-- `e_p = v_p (A (f 0))` for `p ∈ S`. -/
theorem factorization_A_f_zero {p : ℕ} (hp : p ∈ S) : (A (f 0)).factorization p = eS p := by
  rw [A_f_zero_eq]
  rw [mem_S_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [eS, S] <;>
    exact factorization_eq_of_dvd_of_not_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `v_p (179 + j) < b_p` for `p ∈ S` and `j ∈ {1,2,3}`. -/
theorem factorization_lt_bS {p : ℕ} (hp : p ∈ S) (j : ℕ) (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    (179 + j).factorization p < bS p := by
  rw [mem_S_iff] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    refine factorization_lt_of_not_dvd (by norm_num) (by norm_num) ?_ <;> norm_num [bS, S]

/-- The local witness satisfies `f (t_p) ≡ 179 (mod p^{b_p})`. -/
theorem f_tS_modEq {p : ℕ} (hp : p ∈ S) : f (tS p) ≡ 179 [MOD p ^ bS p] := by
  rw [mem_S_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [Nat.ModEq, f, tS, bS, S]

/-- The local witness has the block of digits `p - 1` at positions `b_p, …, k_p - 1`:
every level `b_p < h ≤ k_p` carries. -/
theorem f_tS_block {p : ℕ} (hp : p ∈ S) :
    ∀ h, bS p < h → h ≤ kS p → p ^ h ≤ 2 * ((f (tS p) % p ^ kS p) % p ^ h) := by
  rw [mem_S_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [bS, kS, eS, tS, S] <;> norm_num <;>
    intro h h1 h2 <;> interval_cases h <;> norm_num [f]

/-- **Local statement for `p ∈ S`.** -/
theorem local_good_S {p : ℕ} (hp : p ∈ S) {t : ℕ} (ht : t ≡ tS p [MOD p ^ kS p]) :
    2 * (A (f t)).factorization p ≤ carry p (f t) := by
  have hpp : p.Prime := prime_of_mem_S hp
  have hbk : bS p ≤ kS p := by unfold kS; omega
  have hkb : kS p - bS p = 2 * eS p := by unfold kS; omega
  -- `f t ≡ f (tS p) (mod p^{k_p})`
  have hf : f t ≡ f (tS p) [MOD p ^ kS p] := by
    unfold f
    exact (((ht.pow 2).mul_left 210).add (ht.mul_left 391)).add_right 179
  -- the block of carries
  have hc : kS p - bS p ≤ carry p (f t) := carry_ge_of_block hpp hbk hf (f_tS_block hp)
  -- the valuation of `A (f t)`
  have hfb : f t ≡ 179 [MOD p ^ bS p] :=
    (Nat.ModEq.of_dvd (Nat.pow_dvd_pow p hbk) hf).trans (f_tS_modEq hp)
  have hv : ∀ j ∈ ({1, 2, 3} : Finset ℕ),
      (f t + j).factorization p = (179 + j).factorization p := fun j hj =>
    factorization_eq_of_modEq hpp (by omega) (factorization_lt_bS hp j hj) (hfb.add_right j)
  have hA : (A (f t)).factorization p = eS p := by
    rw [← factorization_A_f_zero hp]
    have h0 : f 0 = 179 := by norm_num [f]
    unfold A
    rw [h0]
    have h1 : f t + 1 ≠ 0 := by omega
    have h2 : f t + 2 ≠ 0 := by omega
    have h3 : f t + 3 ≠ 0 := by omega
    rw [Nat.factorization_mul (mul_ne_zero h1 h2) h3, Nat.factorization_mul h1 h2,
      Nat.factorization_mul (by norm_num : (179 + 1) * (179 + 2) ≠ 0) (by norm_num : 179 + 3 ≠ 0),
      Nat.factorization_mul (by norm_num : 179 + 1 ≠ 0) (by norm_num : 179 + 2 ≠ 0)]
    simp only [Finsupp.coe_add, Pi.add_apply]
    rw [hv 1 (by simp), hv 2 (by simp), hv 3 (by simp)]
  rw [hA, ← hkb]
  exact hc

/-- **Local statement for primes `p ∉ S`.** If `t ≡ 0 (mod p)` then `p ∤ A (f t)`. -/
theorem local_good_nonS {p : ℕ} (hp : p.Prime) (hpS : p ∉ S) {t : ℕ} (ht : t ≡ 0 [MOD p]) :
    (A (f t)).factorization p = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro h
  apply hpS
  apply mem_S_of_dvd_A_f_zero hp
  have hf : f t ≡ f 0 [MOD p] := by
    unfold f
    exact (((ht.pow 2).mul_left 210).add (ht.mul_left 391)).add_right 179
  have hA : A (f t) ≡ A (f 0) [MOD p] := by
    unfold A
    exact ((hf.add_right 1).mul (hf.add_right 2)).mul (hf.add_right 3)
  exact (hA.dvd_iff dvd_rfl).mp h

theorem modulus_pos {p : ℕ} (hp : p.Prime) : 0 < modulus p := by
  unfold modulus
  split_ifs
  · exact pow_pos hp.pos _
  · exact hp.pos

/-- `modulus p` is a power of `p`. -/
theorem modulus_eq_pow (p : ℕ) : modulus p = p ^ (if p ∈ S then kS p else 1) := by
  unfold modulus
  split_ifs <;> simp

theorem modulus_pairwise_coprime :
    Set.Pairwise (smallPrimes : Set ℕ) (fun p q => Nat.Coprime (modulus p) (modulus q)) := by
  intro p hp q hq hne
  have hp' : p.Prime := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
  have hq' : q.Prime := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
  rw [modulus_eq_pow, modulus_eq_pow]
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp' hq').mpr hne)

/-- Prime factors of `modulus p` are `p` itself. -/
theorem prime_dvd_modulus {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : q ∣ modulus p) : q = p := by
  rw [modulus_eq_pow] at h
  exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h)

/-- **Section 4**: there is a progression `t = t₀ + Q v` on which every prime `p ≤ 1000`
satisfies the carry inequality, and `Q` has no prime factor above `1000`. -/
theorem exists_progression :
    ∃ Q t₀ : ℕ, 0 < Q ∧ (∀ p, p.Prime → p ∣ Q → p ≤ Y) ∧
      ∀ v p, p.Prime → p ≤ Y → 2 * (A (f (t₀ + Q * v))).factorization p ≤ carry p (f (t₀ + Q * v)) := by
  have hs : ∀ p ∈ smallPrimes, modulus p ≠ 0 := fun p hp =>
    (modulus_pos (Finset.mem_filter.mp hp).2).ne'
  have hpp : Set.Pairwise (smallPrimes : Set ℕ) (Function.onFun Nat.Coprime modulus) :=
    modulus_pairwise_coprime
  obtain ⟨t₀, ht₀⟩ := Nat.chineseRemainderOfFinset residue modulus smallPrimes hs hpp
  refine ⟨∏ p ∈ smallPrimes, modulus p, t₀, ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun p hp => modulus_pos (Finset.mem_filter.mp hp).2
  · intro p hp hdvd
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd
    have hq' := Finset.mem_filter.mp hq
    rw [prime_dvd_modulus hq'.2 hp hpq]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hq'.1)
  · intro v p hp hpY
    have hpm : p ∈ smallPrimes :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpY), hp⟩
    have hmod : t₀ + (∏ q ∈ smallPrimes, modulus q) * v ≡ residue p [MOD modulus p] := by
      have h1 : (∏ q ∈ smallPrimes, modulus q) * v ≡ 0 [MOD modulus p] :=
        Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hpm) v)
      have h2 := (Nat.ModEq.refl t₀).add h1
      rw [add_zero] at h2
      exact h2.trans (ht₀ p hpm)
    by_cases hS : p ∈ S
    · have hm : modulus p = p ^ kS p := by simp [modulus, hS]
      have hr : residue p = tS p := by simp [residue, hS]
      rw [hm, hr] at hmod
      exact local_good_S hS hmod
    · have hm : modulus p = p := by simp [modulus, hS]
      have hr : residue p = 0 := by simp [residue, hS]
      rw [hm, hr] at hmod
      rw [local_good_nonS hp hS hmod]
      simp

/-- The modulus `Q` of the progression. -/
noncomputable def Q : ℕ := exists_progression.choose

/-- The starting point `t₀` of the progression. -/
noncomputable def t₀ : ℕ := exists_progression.choose_spec.choose

theorem Q_pos : 0 < Q := exists_progression.choose_spec.choose_spec.1

theorem prime_dvd_Q_le {p : ℕ} (hp : p.Prime) (h : p ∣ Q) : p ≤ Y :=
  exists_progression.choose_spec.choose_spec.2.1 p hp h

theorem small_primes_good (v p : ℕ) (hp : p.Prime) (hpY : p ≤ Y) :
    2 * (A (f (t₀ + Q * v))).factorization p ≤ carry p (f (t₀ + Q * v)) :=
  exists_progression.choose_spec.choose_spec.2.2 v p hp hpY

end Erdos727
