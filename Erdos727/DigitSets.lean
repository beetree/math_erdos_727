import Erdos727.Failure

/-!
# Digit sets and the residue-count bound (Section 7)

`digitSet p Ds` is the set of integers `d₀ + d₁ p + d₂ p² + ⋯` whose base-`p` digits `d_k` lie
in the prescribed finite sets `Ds[k]`.  The digits describing "lowest digit `p - j`, then no
carry at the levels `2, …, J`" are

  `carryDigits p j J = [{p - j}, range ((p-1)/2), range ((p+1)/2), …, range ((p+1)/2)]`

(`J` entries).  Indeed, once the lower digits produce no carry, level `2` carries iff
`d₁ ≥ (p-1)/2` (the units digit `p - j` carries), and level `h ≥ 3` carries iff `d_{h-1} ≥ (p+1)/2`.
Hence a residue `n mod p^J` with `n ≡ p - j (mod p)` and no carry at levels `2..J` lies in
`digitSet p (carryDigits p j J)`, a set of size at most `((p+1)/2)^(J-1)`.

Combining with the injectivity `modEq_of_F_modEq` on a root class gives the residue-count bound
`#(badSet X i p) ≤ ((p+1)/2)^(ℓ-1) (X / p^ℓ + 1)` of (7.1).
-/

namespace Erdos727

open Finset

/-- Integers whose base-`p` digits lie in the prescribed sets (lowest digit first). -/
def digitSet (p : ℕ) : List (Finset ℕ) → Finset ℕ
  | [] => {0}
  | D :: Ds => (D ×ˢ digitSet p Ds).image fun x => x.1 + p * x.2

theorem mem_digitSet_nil {p r : ℕ} : r ∈ digitSet p [] ↔ r = 0 := by
  simp [digitSet]

theorem mem_digitSet_cons {p : ℕ} {D : Finset ℕ} {Ds : List (Finset ℕ)} {r : ℕ} :
    r ∈ digitSet p (D :: Ds) ↔ ∃ d ∈ D, ∃ r' ∈ digitSet p Ds, r = d + p * r' := by
  simp only [digitSet, mem_image, mem_product, Prod.exists]
  constructor
  · rintro ⟨d, r', ⟨hd, hr'⟩, rfl⟩
    exact ⟨d, hd, r', hr', rfl⟩
  · rintro ⟨d, hd, r', hr', rfl⟩
    exact ⟨d, r', ⟨hd, hr'⟩, rfl⟩

theorem digitSet_subset_range {p : ℕ} (hp : 0 < p) (Ds : List (Finset ℕ))
    (hDs : ∀ D ∈ Ds, D ⊆ range p) : digitSet p Ds ⊆ range (p ^ Ds.length) := by
  induction Ds with
  | nil =>
    intro r hr
    rw [mem_digitSet_nil] at hr
    simp [hr]
  | cons D Ds ih =>
    intro r hr
    obtain ⟨d, hd, r', hr', rfl⟩ := mem_digitSet_cons.mp hr
    have hd' : d < p := mem_range.mp (hDs D (List.mem_cons.mpr (Or.inl rfl)) hd)
    have hr'' : r' < p ^ Ds.length :=
      mem_range.mp (ih (fun D' hD' => hDs D' (List.mem_cons.mpr (Or.inr hD'))) hr')
    rw [mem_range, List.length_cons, pow_succ]
    have _ := hp
    have h1 : p * (r' + 1) ≤ p * p ^ Ds.length := Nat.mul_le_mul_left _ hr''
    calc d + p * r' < p + p * r' := by omega
      _ = p * (r' + 1) := by ring
      _ ≤ p * p ^ Ds.length := h1
      _ = p ^ Ds.length * p := mul_comm _ _

theorem card_digitSet_le (p : ℕ) (Ds : List (Finset ℕ)) :
    #(digitSet p Ds) ≤ (Ds.map Finset.card).prod := by
  induction Ds with
  | nil => simp [digitSet]
  | cons D Ds ih =>
    simp only [digitSet, List.map_cons, List.prod_cons]
    refine card_image_le.trans ?_
    rw [card_product]
    exact Nat.mul_le_mul_left _ ih

/-- Appending a top digit. -/
theorem digitSet_append_singleton {p : ℕ} (hp : 0 < p) (Ds : List (Finset ℕ))
    (hDs : ∀ D ∈ Ds, D ⊆ range p) (D' : Finset ℕ) :
    digitSet p (Ds ++ [D']) = (digitSet p Ds ×ˢ D').image fun x => x.1 + p ^ Ds.length * x.2 := by
  have _ := hp
  induction Ds with
  | nil =>
    ext r
    rw [List.nil_append, mem_digitSet_cons, mem_image]
    constructor
    · rintro ⟨d, hd, r', hr', rfl⟩
      rw [mem_digitSet_nil] at hr'
      subst hr'
      refine ⟨(0, d), mem_product.mpr ⟨mem_digitSet_nil.mpr rfl, hd⟩, ?_⟩
      simp
    · rintro ⟨⟨a, b⟩, hab, rfl⟩
      rw [mem_product, mem_digitSet_nil] at hab
      obtain ⟨rfl, hb⟩ := hab
      exact ⟨b, hb, 0, mem_digitSet_nil.mpr rfl, by simp⟩
  | cons D Ds ih =>
    have ih' := ih (fun D' hD' => hDs D' (List.mem_cons.mpr (Or.inr hD')))
    ext r
    rw [List.cons_append, mem_digitSet_cons, ih', mem_image]
    constructor
    · rintro ⟨d, hd, r', hr', rfl⟩
      rw [mem_image] at hr'
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := hr'
      rw [mem_product] at hab
      refine ⟨(d + p * a, b), ?_, ?_⟩
      · rw [mem_product]
        exact ⟨mem_digitSet_cons.mpr ⟨d, hd, a, hab.1, rfl⟩, hab.2⟩
      · simp only [List.length_cons]
        ring
    · rintro ⟨⟨a, b⟩, hab, rfl⟩
      rw [mem_product] at hab
      obtain ⟨d, hd, r', hr', rfl⟩ := mem_digitSet_cons.mp hab.1
      refine ⟨d, hd, r' + p ^ Ds.length * b, ?_, ?_⟩
      · rw [mem_image]
        exact ⟨(r', b), mem_product.mpr ⟨hr', hab.2⟩, rfl⟩
      · simp only [List.length_cons]
        ring

/-- The digit sets for "lowest digit `p - j`, no carry at levels `2..J`". -/
def carryDigits (p j : ℕ) : ℕ → List (Finset ℕ)
  | 0 => []
  | 1 => [{p - j}]
  | 2 => [{p - j}, range ((p - 1) / 2)]
  | J + 3 => carryDigits p j (J + 2) ++ [range ((p + 1) / 2)]

/-- Auxiliary: the recursive step of `carryDigits`. -/
theorem carryDigits_add_three (p j J : ℕ) :
    carryDigits p j (J + 3) = carryDigits p j (J + 2) ++ [range ((p + 1) / 2)] := by
  rw [carryDigits]

@[simp] theorem carryDigits_length (p j J : ℕ) : (carryDigits p j J).length = J := by
  induction J with
  | zero => rfl
  | succ J ih =>
    rcases J with _ | _ | J
    · rfl
    · rfl
    · have ih' : (carryDigits p j (J + 2)).length = J + 2 := ih
      show (carryDigits p j (J + 3)).length = J + 3
      rw [carryDigits_add_three, List.length_append, ih']
      rfl

/-- Auxiliary: `carryDigits_subset_range` under the additional hypothesis `1 ≤ j` (needed so
that `p - j < p`). -/
theorem carryDigits_subset_range' {p j : ℕ} (hp : 0 < p) (hj1 : 1 ≤ j) (hj : j ≤ p) (J : ℕ) :
    ∀ D ∈ carryDigits p j J, D ⊆ range p := by
  have h1 : ({p - j} : Finset ℕ) ⊆ range p :=
    singleton_subset_iff.mpr (mem_range.mpr (by omega))
  have h2 : range ((p - 1) / 2) ⊆ range p :=
    range_subset.mpr fun x hx => mem_range.mpr (by omega)
  have h3 : range ((p + 1) / 2) ⊆ range p :=
    range_subset.mpr fun x hx => mem_range.mpr (by omega)
  induction J with
  | zero => simp [carryDigits]
  | succ J ih =>
    rcases J with _ | _ | J
    · intro D hD
      simp only [carryDigits, List.mem_singleton] at hD
      subst hD
      exact h1
    · intro D hD
      simp only [carryDigits, List.mem_cons, List.not_mem_nil, or_false] at hD
      rcases hD with rfl | rfl
      · exact h1
      · exact h2
    · intro D hD
      have hD' : D ∈ carryDigits p j (J + 3) := hD
      rw [carryDigits_add_three, List.mem_append, List.mem_singleton] at hD'
      rcases hD' with hD' | rfl
      · exact ih D hD'
      · exact h3

theorem carryDigits_subset_range {p j : ℕ} (hp : 0 < p) (hj1 : 1 ≤ j) (hj : j ≤ p) (J : ℕ) :
    ∀ D ∈ carryDigits p j J, D ⊆ range p :=
  carryDigits_subset_range' hp hj1 hj J

/-- Every digit set in `carryDigits` is an interval `Ico s (s + m)` with `m ≤ p`. -/
theorem carryDigits_interval {p j : ℕ} (hp : 0 < p) (_hj : j ≤ p) (J : ℕ) :
    ∀ D ∈ carryDigits p j J, ∃ s m, D = Ico s (s + m) ∧ m ≤ p := by
  have h1 : ∃ s m, ({p - j} : Finset ℕ) = Ico s (s + m) ∧ m ≤ p :=
    ⟨p - j, 1, (Nat.Ico_succ_singleton (p - j)).symm, hp⟩
  have h2 : ∃ s m, range ((p - 1) / 2) = Ico s (s + m) ∧ m ≤ p :=
    ⟨0, (p - 1) / 2, by rw [zero_add, range_eq_Ico], by omega⟩
  have h3 : ∃ s m, range ((p + 1) / 2) = Ico s (s + m) ∧ m ≤ p :=
    ⟨0, (p + 1) / 2, by rw [zero_add, range_eq_Ico], by omega⟩
  induction J with
  | zero => simp [carryDigits]
  | succ J ih =>
    rcases J with _ | _ | J
    · intro D hD
      simp only [carryDigits, List.mem_singleton] at hD
      subst hD
      exact h1
    · intro D hD
      simp only [carryDigits, List.mem_cons, List.not_mem_nil, or_false] at hD
      rcases hD with rfl | rfl
      · exact h1
      · exact h2
    · intro D hD
      have hD' : D ∈ carryDigits p j (J + 3) := hD
      rw [carryDigits_add_three, List.mem_append, List.mem_singleton] at hD'
      rcases hD' with hD' | rfl
      · exact ih D hD'
      · exact h3

theorem card_carryDigitSet_le (p j : ℕ) {J : ℕ} (hJ : 1 ≤ J) :
    #(digitSet p (carryDigits p j J)) ≤ ((p + 1) / 2) ^ (J - 1) := by
  refine (card_digitSet_le p _).trans ?_
  induction J with
  | zero => omega
  | succ J ih =>
    rcases J with _ | _ | J
    · simp [carryDigits]
    · simp [carryDigits]
      omega
    · have ih' : ((carryDigits p j (J + 2)).map Finset.card).prod ≤ ((p + 1) / 2) ^ (J + 1) :=
        ih (by omega)
      show ((carryDigits p j (J + 3)).map Finset.card).prod ≤ ((p + 1) / 2) ^ (J + 2)
      rw [carryDigits_add_three, List.map_append, List.prod_append, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one, card_range, pow_succ]
      exact Nat.mul_le_mul_right _ ih'

/-- Auxiliary: for `J ≥ 1`, the first digit set of `carryDigits p j J` is `{p - j}`. -/
theorem carryDigits_eq_cons (p j : ℕ) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ rest, carryDigits p j J = {p - j} :: rest := by
  induction J with
  | zero => omega
  | succ J ih =>
    rcases J with _ | _ | J
    · exact ⟨[], rfl⟩
    · exact ⟨[range ((p - 1) / 2)], rfl⟩
    · obtain ⟨rest, hrest⟩ := ih (by omega)
      refine ⟨rest ++ [range ((p + 1) / 2)], ?_⟩
      show carryDigits p j (J + 3) = _
      rw [carryDigits_add_three, hrest, List.cons_append]

/-- Auxiliary: `mod_p_of_mem_carryDigitSet` under the additional hypothesis `1 ≤ j`. -/
theorem mod_p_of_mem_carryDigitSet' {p j J r : ℕ} (_hp : 0 < p) (hj1 : 1 ≤ j) (hj : j ≤ p)
    (hJ : 1 ≤ J) (hr : r ∈ digitSet p (carryDigits p j J)) : r % p = p - j := by
  obtain ⟨rest, hrest⟩ := carryDigits_eq_cons p j hJ
  rw [hrest, mem_digitSet_cons] at hr
  obtain ⟨d, hd, r', -, rfl⟩ := hr
  rw [mem_singleton] at hd
  subst hd
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem mod_p_of_mem_carryDigitSet {p j J r : ℕ} (hp : 0 < p) (hj1 : 1 ≤ j) (hj : j ≤ p)
    (hJ : 1 ≤ J) (hr : r ∈ digitSet p (carryDigits p j J)) : r % p = p - j :=
  mod_p_of_mem_carryDigitSet' hp hj1 hj hJ hr

/-- **Key digit lemma**: if `n ≡ p - j (mod p)` with `2j < p`, `p` odd, and no level
`2 ≤ h ≤ J` carries when doubling `n`, then `n mod p^J` lies in the carry digit set. -/
theorem mem_carryDigitSet_of_noCarry {p j J n : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hj : 1 ≤ j)
    (hjp : 2 * j < p) (hJ : 1 ≤ J) (h1 : n % p = p - j)
    (hno : ∀ h, 2 ≤ h → h ≤ J → 2 * (n % p ^ h) < p ^ h) :
    n % p ^ J ∈ digitSet p (carryDigits p j J) := by
  have hp0 : 0 < p := hp.pos
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hodd
  induction J with
  | zero => omega
  | succ J ih =>
    rcases J with _ | _ | J
    · -- `J = 1`
      show n % p ^ 1 ∈ digitSet p [{p - j}]
      rw [pow_one, h1]
      exact mem_digitSet_cons.mpr
        ⟨p - j, mem_singleton_self _, 0, mem_digitSet_nil.mpr rfl, by ring⟩
    · -- `J = 2`
      show n % p ^ 2 ∈ digitSet p [{p - j}, range ((p - 1) / 2)]
      have hsplit : n % p ^ 2 = n % p + p * (n / p % p) := by
        have h := @Nat.mod_pow_succ n p 1
        rwa [pow_one] at h
      have hno2 : 2 * (n % p ^ 2) < p ^ 2 := hno 2 le_rfl (by norm_num)
      set d := n / p % p with hd
      have hd' : d < (p - 1) / 2 := by
        rw [hsplit, h1, sq] at hno2
        obtain ⟨q, hq⟩ : ∃ q, p = q + j := ⟨p - j, by omega⟩
        rw [show p - j = q by omega] at hno2
        have key : 2 * d + 1 < p := by
          by_contra hcon
          push Not at hcon
          nlinarith [Nat.mul_le_mul_left p hcon]
        omega
      rw [hsplit, h1]
      exact mem_digitSet_cons.mpr ⟨p - j, mem_singleton_self _, d,
        mem_digitSet_cons.mpr ⟨d, mem_range.mpr hd', 0, mem_digitSet_nil.mpr rfl, by ring⟩,
        rfl⟩
    · -- `J + 3`
      have ih' : n % p ^ (J + 2) ∈ digitSet p (carryDigits p j (J + 2)) :=
        ih (by omega) (fun h h2 hh => hno h h2 (by omega))
      show n % p ^ (J + 3) ∈ digitSet p (carryDigits p j (J + 3))
      have hsplit : n % p ^ (J + 3) = n % p ^ (J + 2) + p ^ (J + 2) * (n / p ^ (J + 2) % p) :=
        Nat.mod_pow_succ
      set d := n / p ^ (J + 2) % p with hd
      clear_value d
      have hno' : 2 * (n % p ^ (J + 3)) < p ^ (J + 3) := hno (J + 3) (by omega) (by omega)
      have hd' : d < (p + 1) / 2 := by
        have hpow : p ^ (J + 3) = p ^ (J + 2) * p := pow_succ p (J + 2)
        have h2d : 2 * d < p := by
          by_contra hcon
          push Not at hcon
          rw [hsplit, hpow] at hno'
          have h3 : p ^ (J + 2) * p ≤ 2 * (p ^ (J + 2) * d) :=
            calc p ^ (J + 2) * p ≤ p ^ (J + 2) * (2 * d) := Nat.mul_le_mul_left _ hcon
              _ = 2 * (p ^ (J + 2) * d) := by ring
          -- `omega` loses the nonnegativity of `n % p ^ (J + 2)` when it pushes the cast
          -- through `%`; generalize the remainder to a fresh natural first.
          generalize n % p ^ (J + 2) = r at hno'
          omega
        omega
      rw [carryDigits_add_three,
        digitSet_append_singleton hp0 _ (carryDigits_subset_range' hp0 hj (by omega) _),
        mem_image]
      refine ⟨(n % p ^ (J + 2), d), mem_product.mpr ⟨ih', mem_range.mpr hd'⟩, ?_⟩
      show n % p ^ (J + 2) + p ^ (carryDigits p j (J + 2)).length * d = n % p ^ (J + 3)
      rw [carryDigits_length, hsplit]

/-- **(7.1)**: the residue-count bound. -/
theorem card_badSet_le {p : ℕ} (hp : p.Prime) (hpY : Y < p) (i : Fin 6) (X : ℕ) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) : #(badSet X i p) ≤ ((p + 1) / 2) ^ (ℓ - 1) * (X / p ^ ℓ + 1) := by
  have hp0 : 0 < p := hp.pos
  have hpY' : 1000 < p := hpY
  have hs1 := shift_pos i
  have hs3 := shift_le_three i
  obtain ⟨r, -, hroot⟩ := exists_root hp hpY i
  have hM : 0 < p ^ ℓ := pow_pos hp0 _
  have hsub : badSet X i p ⊆
      {v ∈ Ico X (X + X) | v % p = r ∧ F v % p ^ ℓ ∈ digitSet p (carryDigits p (shift i) ℓ)} := by
    intro v hv
    classical
    unfold badSet at hv
    rw [mem_filter] at hv ⊢
    obtain ⟨hvI, hdvd, hno⟩ := hv
    refine ⟨by rwa [two_mul] at hvI, (hroot v).mp hdvd, ?_⟩
    apply mem_carryDigitSet_of_noCarry hp (by omega) hs1 (by omega) hℓ
      (F_mod_eq hp (by omega) i hdvd)
    intro h h2 _
    exact hno h h2
  refine (card_le_card hsub).trans ?_
  refine (card_filter_image_mod_le hM F _ ?_).trans ?_
  · intro v v' hv hv' hF
    exact modEq_of_F_modEq hp hpY i ((hroot v).mpr hv) ((hroot v').mpr hv') hF
  · exact Nat.mul_le_mul_right _ (card_carryDigitSet_le p _ hℓ)

end Erdos727
