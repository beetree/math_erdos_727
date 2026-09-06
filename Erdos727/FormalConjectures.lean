import Erdos727.Defs

/-!
# The Formal Conjectures statement of Erdős Problem 727

Reproduces the right-hand sides of the propositions in
`FormalConjectures/ErdosProblems/727.lean` of google-deepmind/formal-conjectures
(pinned revision in `third_party/formal_conjectures/REVISION`).  The upstream file states, with
`answer(sorry)`, the question whether `((n+k)!)^2 ∣ (2n)!` holds for infinitely many `n`,
for every `k ≥ 2` (`erdos_727`) and for `k = 2` (`erdos_727.variants.k_2`).

`scripts/check_fc_source.py` compares the propositions below with the pinned upstream source.
-/

open scoped Nat

namespace Erdos727

/-- The full Erdős Problem 727 proposition, as in upstream `erdos_727`. -/
def formalConjecturesStatement : Prop := ∀ k ≥ 2,
    Set.Infinite {n : ℕ | (Nat.factorial (n + k)) ^ 2 ∣ Nat.factorial (2 * n)}

/-- The `k = 2` proposition, as in upstream `erdos_727.variants.k_2`. -/
def formalConjecturesStatement_k2 : Prop :=
    letI k := 2
    Set.Infinite {n : ℕ | (Nat.factorial (n + k)) ^ 2 ∣ Nat.factorial (2 * n)}

/-- The `k = 3` proposition, in the same shape. -/
def formalConjecturesStatement_k3 : Prop :=
    letI k := 3
    Set.Infinite {n : ℕ | (Nat.factorial (n + k)) ^ 2 ∣ Nat.factorial (2 * n)}

theorem formalConjecturesStatement_k3_iff :
    formalConjecturesStatement_k3 ↔ Set.Infinite {n : ℕ | Good n} := Iff.rfl

end Erdos727
