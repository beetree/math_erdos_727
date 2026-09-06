import Erdos727.DigitSets
import Erdos727.Analytic.WeylSum

/-!
# Finite Fourier analysis of the carry digit sets (Section 9, reorganised)

Instead of equidistribution on the torus, we expand the indicator of the carry digit set
`T = digitSet p (carryDigits p j J) ⊆ [0, p^J)` in additive characters of `ℤ/p^J`:

  `[n mod q ∈ T] = (1/q) ∑_{h<q} \hat T(h) e(h n / q)`,  `\hat T(h) = ∑_{r∈T} e(-h r/q)`, `q = p^J`.

For a sequence `n z` with `n z ≡ p - j (mod p)` for all `z`, the frequencies `h` divisible by
`p^(J-1)` contribute exactly the main term `L · #T / p^(J-1)` (both `n z` and every `r ∈ T` are
`≡ p - j (mod p)`), and the remaining frequencies are bounded by `‖\hat T(h)‖ ‖∑_z e(h n z/q)‖`.

The `ℓ¹`-norm of `\hat T` over `ℤ/p^J` is at most `(2p (2 + log p))^J`: peeling off the top digit
of `h` and using that every digit set is an interval, the lowest-digit factor is a geometric sum
whose complete residue sum is `≤ 2p (2 + log p)` (`sum_geomBound_le`), and induction on the list
of digit sets does the rest.
-/

namespace Erdos727

open Finset Real

/-- Fourier coefficient of a finite set of residues: `\hat T(h) = ∑_{r ∈ T} e(-h r / q)`. -/
noncomputable def fourier (q : ℕ) (T : Finset ℕ) (h : ℕ) : ℂ := ∑ r ∈ T, e (-((h : ℝ) * r) / q)

/-- Orthogonality: `∑_{h<q} e(h m / q) = q` if `q ∣ m`, and `0` otherwise. -/
theorem sum_e_div_eq {q : ℕ} (hq : 0 < q) (m : ℤ) :
    ∑ h ∈ range q, e ((h : ℝ) * m / q) = if (q : ℤ) ∣ m then (q : ℂ) else 0 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hterm : ∀ h : ℕ, e ((h : ℝ) * m / q) = e ((m : ℝ) / q) ^ h := by
    intro h
    rw [← e_nat_mul]
    congr 1
    ring
  simp_rw [hterm]
  split_ifs with hdvd
  · obtain ⟨k, rfl⟩ := hdvd
    have h1 : e ((((q : ℤ) * k : ℤ) : ℝ) / q) = 1 := by
      rw [show (((q : ℤ) * k : ℤ) : ℝ) / q = ((k : ℤ) : ℝ) by push_cast; field_simp]
      exact e_int k
    simp only [h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · have hx : e ((m : ℝ) / q) ≠ 1 := by
      intro h1
      unfold e at h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨k, hk⟩ := h1
      apply hdvd
      have h2 : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
        have := Real.pi_ne_zero
        simp [Complex.I_ne_zero, this]
      have h3 : (2 * (π : ℂ) * Complex.I) * (((m : ℝ) / q : ℝ) : ℂ)
          = (2 * (π : ℂ) * Complex.I) * (k : ℂ) := by rw [hk]; ring
      have h4 : (((m : ℝ) / q : ℝ) : ℂ) = ((k : ℝ) : ℂ) := by
        rw [Complex.ofReal_intCast]
        exact mul_left_cancel₀ h2 h3
      have h5 : (m : ℝ) / q = (k : ℝ) := Complex.ofReal_injective h4
      have h6 : (m : ℝ) = (q : ℝ) * k := by
        rw [div_eq_iff hq'.ne'] at h5
        linarith
      exact ⟨k, by exact_mod_cast h6⟩
    have hpow : e ((m : ℝ) / q) ^ q = 1 := by
      rw [← e_nat_mul, div_mul_cancel₀ _ hq'.ne', e_int]
    rw [geom_sum_eq hx q, hpow, sub_self, zero_div]

/-- Fourier inversion for the indicator of `T ⊆ [0, q)`. -/
theorem indicator_eq_fourier {q : ℕ} (hq : 0 < q) {T : Finset ℕ} (hT : T ⊆ range q) (n : ℕ) :
    (if n % q ∈ T then (1 : ℂ) else 0) =
      (1 / q : ℂ) * ∑ h ∈ range q, fourier q T h * e ((h : ℝ) * n / q) := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have key : ∑ h ∈ range q, fourier q T h * e ((h : ℝ) * n / q)
      = ∑ r ∈ T, ∑ h ∈ range q, e ((h : ℝ) * (((n : ℤ) - r : ℤ) : ℝ) / q) := by
    unfold fourier
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun h _ => ?_
    rw [← e_add]
    congr 1
    push_cast
    ring
  have hterm : ∀ r ∈ T, (∑ h ∈ range q, e ((h : ℝ) * (((n : ℤ) - r : ℤ) : ℝ) / q))
      = if r = n % q then (q : ℂ) else 0 := by
    intro r hr
    rw [sum_e_div_eq hq]
    have hrq : r < q := mem_range.mp (hT hr)
    have hiff : (q : ℤ) ∣ (n : ℤ) - r ↔ r = n % q := by
      rw [← Nat.modEq_iff_dvd, Nat.ModEq, Nat.mod_eq_of_lt hrq]
    simp only [hiff]
  rw [key, Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  split_ifs
  · field_simp
  · simp

/-- Counting through Fourier coefficients. -/
theorem card_filter_eq_fourier {q : ℕ} (hq : 0 < q) {T : Finset ℕ} (hT : T ⊆ range q)
    (n : ℕ → ℕ) (L : ℕ) :
    (#{z ∈ range L | n z % q ∈ T} : ℂ) =
      (1 / q : ℂ) * ∑ h ∈ range q, fourier q T h * ∑ z ∈ range L, e ((h : ℝ) * n z / q) := by
  have h1 : (#{z ∈ range L | n z % q ∈ T} : ℂ)
      = ∑ z ∈ range L, if n z % q ∈ T then (1 : ℂ) else 0 := by
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [h1, Finset.sum_congr rfl fun z _ => indicator_eq_fourier hq hT (n z), ← Finset.mul_sum,
    Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.mul_sum]

/-- Auxiliary: the Fourier coefficient is `q`-periodic in `h`. -/
theorem fourier_add_mul {q : ℕ} (hq : 0 < q) (T : Finset ℕ) (h c : ℕ) :
    fourier q T (h + q * c) = fourier q T h := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold fourier
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← e_add_int (-((h : ℝ) * r) / q) (-((c : ℤ) * r))]
  congr 1
  push_cast
  field_simp
  ring

/-- Auxiliary: splitting a sum over `range (a * b)` by the quotient modulo `a`. -/
theorem sum_range_mul_eq (F : ℕ → ℝ) (a b : ℕ) :
    ∑ h ∈ range (a * b), F h = ∑ c ∈ range b, ∑ h₁ ∈ range a, F (h₁ + a * c) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun h₁ _ => ?_
    rw [add_comm]

/-- Auxiliary: factorisation of the Fourier coefficient of `digitSet p (D :: Ds)`. -/
theorem fourier_digitSet_cons {p : ℕ} (hp : 0 < p) (D : Finset ℕ) (hD : D ⊆ range p)
    (Ds : List (Finset ℕ)) (h : ℕ) :
    fourier (p ^ Ds.length * p) (digitSet p (D :: Ds)) h
      = (∑ d ∈ D, e (-((h : ℝ) * d) / (p ^ Ds.length * p))) *
          fourier (p ^ Ds.length) (digitSet p Ds) h := by
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold fourier
  rw [digitSet, Finset.sum_image, Finset.sum_product, Finset.sum_mul_sum]
  · refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun r _ => ?_
    rw [← e_add]
    congr 1
    push_cast
    field_simp
    ring
  · rintro ⟨d, r⟩ hdr ⟨d', r'⟩ hdr' heq
    simp only [Finset.mem_coe, mem_product] at hdr hdr'
    have hd : d < p := mem_range.mp (hD hdr.1)
    have hd' : d' < p := mem_range.mp (hD hdr'.1)
    simp only at heq
    have h1 : d = d' := by
      have := congrArg (· % p) heq
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hd'] using this
    subst h1
    have h2 : r = r' := Nat.eq_of_mul_eq_mul_left hp (by omega)
    rw [h2]

/-- The `ℓ¹` bound for interval digit sets contained in `[0, p)`. -/
theorem sum_norm_fourier_digitSet_le {p : ℕ} (hp : 2 ≤ p) (Ds : List (Finset ℕ))
    (hDs : ∀ D ∈ Ds, ∃ s m, D = Ico s (s + m) ∧ m ≤ p) (hDs' : ∀ D ∈ Ds, D ⊆ range p) :
    ∑ h ∈ range (p ^ Ds.length), ‖fourier (p ^ Ds.length) (digitSet p Ds) h‖
      ≤ (2 * p * (2 + log p)) ^ Ds.length := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hlog : 0 ≤ log (p : ℝ) := Real.log_natCast_nonneg p
  have hC : 0 ≤ 2 * (p : ℝ) * (2 + log p) := by positivity
  induction Ds with
  | nil =>
    simp [fourier, digitSet, e_zero]
  | cons D Ds ih =>
    have hD := hDs D (List.mem_cons_self ..)
    have hD' := hDs' D (List.mem_cons_self ..)
    have ih' := ih (fun D' hD' => hDs D' (List.mem_cons_of_mem _ hD'))
      (fun D' hD' => hDs' D' (List.mem_cons_of_mem _ hD'))
    have hfac := fourier_digitSet_cons hp0 D hD' Ds
    obtain ⟨s, m, rfl, hm⟩ := hD
    rw [List.length_cons, pow_succ]
    obtain ⟨q', hq'⟩ : ∃ q', q' = p ^ Ds.length := ⟨_, rfl⟩
    rw [← hq'] at hfac ih' ⊢
    have hq'cast : ((p : ℝ) ^ Ds.length) = (q' : ℝ) := by rw [hq']; push_cast; rfl
    rw [hq'cast] at hfac
    have hq'pos : 0 < q' := by rw [hq']; exact pow_pos hp0 _
    have hq'R : (q' : ℝ) ≠ 0 := by exact_mod_cast hq'pos.ne'
    have hinner : ∀ h₁ ∈ range q', ∑ c ∈ range p,
        ‖∑ d ∈ Ico s (s + m), e (-(((h₁ + q' * c : ℕ) : ℝ) * d) / ((q' : ℕ) * p))‖
          ≤ 2 * p * (2 + log p) := by
      intro h₁ _
      calc ∑ c ∈ range p,
            ‖∑ d ∈ Ico s (s + m), e (-(((h₁ + q' * c : ℕ) : ℝ) * d) / ((q' : ℕ) * p))‖
          ≤ ∑ c ∈ range p, geomBound p ((c : ℝ) / p + (h₁ : ℝ) / (q' * p)) := by
            refine Finset.sum_le_sum fun c _ => ?_
            rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
            have hb := norm_sum_e_le_geomBound (-((c : ℝ) / p + h₁ / (q' * p)))
              (-((c : ℝ) / p + h₁ / (q' * p)) * s) m
            rw [geomBound_neg] at hb
            refine le_trans (le_of_eq ?_) (hb.trans (geomBound_mono hm _))
            congr 1
            refine Finset.sum_congr rfl fun k _ => ?_
            congr 1
            push_cast
            field_simp
            ring
        _ ≤ 2 * p + 2 * p * (1 + log p) := sum_geomBound_le p hp0 p _
        _ = 2 * p * (2 + log p) := by ring
    calc ∑ h ∈ range (q' * p), ‖fourier (q' * p) (digitSet p (Ico s (s + m) :: Ds)) h‖
        = ∑ c ∈ range p, ∑ h₁ ∈ range q',
            ‖fourier (q' * p) (digitSet p (Ico s (s + m) :: Ds)) (h₁ + q' * c)‖ :=
          sum_range_mul_eq _ q' p
      _ = ∑ c ∈ range p, ∑ h₁ ∈ range q',
            ‖∑ d ∈ Ico s (s + m), e (-(((h₁ + q' * c : ℕ) : ℝ) * d) / ((q' : ℕ) * p))‖ *
              ‖fourier q' (digitSet p Ds) h₁‖ := by
          refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun h₁ _ => ?_
          rw [hfac, norm_mul, fourier_add_mul hq'pos]
      _ = ∑ h₁ ∈ range q', ‖fourier q' (digitSet p Ds) h₁‖ * ∑ c ∈ range p,
            ‖∑ d ∈ Ico s (s + m), e (-(((h₁ + q' * c : ℕ) : ℝ) * d) / ((q' : ℕ) * p))‖ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun h₁ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => mul_comm _ _
      _ ≤ ∑ h₁ ∈ range q', ‖fourier q' (digitSet p Ds) h₁‖ * (2 * p * (2 + log p)) :=
          Finset.sum_le_sum fun h₁ hh₁ =>
            mul_le_mul_of_nonneg_left (hinner h₁ hh₁) (norm_nonneg _)
      _ = (2 * p * (2 + log p)) * ∑ h₁ ∈ range q', ‖fourier q' (digitSet p Ds) h₁‖ := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ (2 * p * (2 + log p)) * (2 * p * (2 + log p)) ^ Ds.length :=
          mul_le_mul_of_nonneg_left ih' hC
      _ = (2 * p * (2 + log p)) ^ (Ds.length + 1) := by rw [pow_succ, mul_comm]

/-- **Main Fourier counting bound.**  Let `q = p^J`, `T = digitSet p (carryDigits p j J)`, and
let `n z ≡ p - j (mod p)` for all `z`.  Then
`#{z < L | n z mod q ∈ T} ≤ L #T / p^(J-1)
  + q⁻¹ ∑_{h < q, p^(J-1) ∤ h} ‖\hat T(h)‖ ‖∑_{z<L} e(h n z / q)‖`. -/
theorem card_filter_le_main_add_error {p j J : ℕ} (hp : p.Prime) (hJ : 1 ≤ J) (hj : 1 ≤ j)
    (hjp : j ≤ p) (n : ℕ → ℕ) (hn : ∀ z, n z % p = p - j) (L : ℕ) :
    (#{z ∈ range L | n z % p ^ J ∈ digitSet p (carryDigits p j J)} : ℝ) ≤
      L * #(digitSet p (carryDigits p j J)) / p ^ (J - 1) +
      (1 / p ^ J : ℝ) * ∑ h ∈ (range (p ^ J)).filter (fun h => ¬ p ^ (J - 1) ∣ h),
        ‖fourier (p ^ J) (digitSet p (carryDigits p j J)) h‖ * ‖∑ z ∈ range L, e ((h : ℝ) * n z / p ^ J)‖ := by
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hpR' : (p : ℝ) ≠ 0 := hpR.ne'
  -- the set `T` and its two properties
  set T := digitSet p (carryDigits p j J) with hT
  have hTsub : T ⊆ range (p ^ J) := by
    have := digitSet_subset_range hp0 (carryDigits p j J) (carryDigits_subset_range hp0 hj hjp J)
    rwa [carryDigits_length] at this
  have hTmod : ∀ r ∈ T, r % p = p - j := fun r hr => mod_p_of_mem_carryDigitSet hp0 hj hjp hJ hr
  clear_value T
  -- the residue `a = p - j`
  obtain ⟨a, ha⟩ : ∃ a, a = p - j := ⟨_, rfl⟩
  rw [← ha] at hn hTmod
  -- `q = p^J = q' * p`
  obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  obtain ⟨q', hq'⟩ : ∃ q', q' = p ^ J' := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = p ^ (J' + 1) := ⟨_, rfl⟩
  have hqq' : q = q' * p := by rw [hq, hq', pow_succ]
  have hq'R : ((p : ℝ) ^ J') = (q' : ℝ) := by rw [hq']; push_cast; rfl
  have hqR : ((p : ℝ) ^ (J' + 1)) = (q : ℝ) := by rw [hq]; push_cast; rfl
  rw [← hq] at hTsub
  rw [← hq, ← hq', hq'R, hqR]
  have hq'pos : 0 < q' := by rw [hq']; exact pow_pos hp0 _
  have hqpos : 0 < q := by rw [hq]; exact pow_pos hp0 _
  have hq'ne : (q' : ℝ) ≠ 0 := by exact_mod_cast hq'pos.ne'
  have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
  -- the Fourier expansion of the count
  have hcount := card_filter_eq_fourier hqpos hTsub n L
  rw [← Finset.sum_filter_add_sum_filter_not (range q) (fun h => q' ∣ h)] at hcount
  -- the main term
  have hmain : ∑ h ∈ (range q).filter (fun h => q' ∣ h),
      fourier q T h * ∑ z ∈ range L, e ((h : ℝ) * n z / q) = (p : ℂ) * ((#T : ℂ) * L) := by
    have himg : (range q).filter (fun h => q' ∣ h) = (range p).image (fun c => q' * c) := by
      ext h
      simp only [mem_filter, mem_range, mem_image]
      constructor
      · rintro ⟨hlt, c, rfl⟩
        refine ⟨c, ?_, rfl⟩
        rw [hqq'] at hlt
        exact Nat.lt_of_mul_lt_mul_left hlt
      · rintro ⟨c, hc, rfl⟩
        refine ⟨?_, dvd_mul_right _ _⟩
        rw [hqq']
        exact Nat.mul_lt_mul_of_pos_left hc hq'pos
    have hterm : ∀ c ∈ range p, fourier q T (q' * c) *
        ∑ z ∈ range L, e (((q' * c : ℕ) : ℝ) * n z / q) = (#T : ℂ) * L := by
      intro c _
      have hF : fourier q T (q' * c) = (#T : ℂ) * e (-((c : ℝ) * a) / p) := by
        unfold fourier
        have hz : ∀ r ∈ T, e (-(((q' * c : ℕ) : ℝ) * r) / q) = e (-((c : ℝ) * a) / p) := by
          intro r hr
          obtain ⟨k, hk⟩ : ∃ k, r = p * k + a := ⟨r / p, by
            have := Nat.div_add_mod r p
            rw [hTmod r hr] at this
            omega⟩
          rw [← e_add_int (-((c : ℝ) * a) / p) (-((c : ℤ) * k))]
          congr 1
          rw [hqq', hk]
          push_cast
          field_simp
          ring
        rw [Finset.sum_congr rfl hz, Finset.sum_const, nsmul_eq_mul]
      have hW : ∑ z ∈ range L, e (((q' * c : ℕ) : ℝ) * n z / q) = (L : ℂ) * e (((c : ℝ) * a) / p) := by
        have hz : ∀ z ∈ range L, e (((q' * c : ℕ) : ℝ) * n z / q) = e (((c : ℝ) * a) / p) := by
          intro z _
          obtain ⟨k, hk⟩ : ∃ k, n z = p * k + a := ⟨n z / p, by
            have := Nat.div_add_mod (n z) p
            rw [hn z] at this
            omega⟩
          rw [← e_add_int (((c : ℝ) * a) / p) ((c : ℤ) * k)]
          congr 1
          rw [hqq', hk]
          push_cast
          field_simp
          ring
        rw [Finset.sum_congr rfl hz, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [hF, hW]
      have h1 : e (-((c : ℝ) * a) / p) * e (((c : ℝ) * a) / p) = 1 := by
        rw [← e_add, neg_div, neg_add_cancel, e_zero]
      calc (#T : ℂ) * e (-((c : ℝ) * a) / p) * ((L : ℂ) * e (((c : ℝ) * a) / p))
          = (#T : ℂ) * L * (e (-((c : ℝ) * a) / p) * e (((c : ℝ) * a) / p)) := by ring
        _ = (#T : ℂ) * L := by rw [h1, mul_one]
    rw [himg, Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hq'pos hab)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmain' : (1 / q : ℂ) * ((p : ℂ) * ((#T : ℂ) * L)) = (((L : ℝ) * #T / q' : ℝ) : ℂ) := by
    have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
    have hq'C : (q' : ℂ) ≠ 0 := by exact_mod_cast hq'pos.ne'
    rw [hqq']
    push_cast
    field_simp
  -- the error term
  have herr : ‖(1 / q : ℂ) * ∑ h ∈ (range q).filter (fun h => ¬ q' ∣ h),
      fourier q T h * ∑ z ∈ range L, e ((h : ℝ) * n z / q)‖
      ≤ (1 / q : ℝ) * ∑ h ∈ (range q).filter (fun h => ¬ q' ∣ h),
          ‖fourier q T h‖ * ‖∑ z ∈ range L, e ((h : ℝ) * n z / q)‖ := by
    rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
    gcongr
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun h _ => norm_mul _ _))
  -- assemble via real parts
  have hre : (#{z ∈ range L | n z % q ∈ T} : ℝ) = (L : ℝ) * #T / q' +
      ((1 / q : ℂ) * ∑ h ∈ (range q).filter (fun h => ¬ q' ∣ h),
        fourier q T h * ∑ z ∈ range L, e ((h : ℝ) * n z / q)).re := by
    have h := congrArg Complex.re hcount
    rw [mul_add, hmain, hmain', Complex.natCast_re, Complex.add_re, Complex.ofReal_re] at h
    exact h
  rw [hre]
  gcongr
  exact (Complex.re_le_norm _).trans herr

end Erdos727
