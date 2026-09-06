import Mathlib

/-!
# Erdős Problem 727, case `k = 3`: basic definitions

We follow `expert_advice/erdos_727_k2_k3_proof.md`. All arithmetic is in `ℕ`.

* `f t = 210 t² + 391 t + 179` is the quadratic polynomial of Section 1.
* `A n = (n+1)(n+2)(n+3)`, so that `(n+3)! = n! * A n`.
* `L i t = slope i * t + icept i` are the six linear forms of Section 3, with
  `f t + shift i = L (2j-2) t * L (2j-1) t` for the pair `j`.
* `carry p n = v_p (binom(2n, n))`, the number of carries when `n` is added to
  itself in base `p` (Kummer).
* `Good n` is the target property `((n+3)!)² ∣ (2n)!`.
-/

namespace Erdos727

/-- The quadratic polynomial `f(t) = 210 t² + 391 t + 179`. -/
def f (t : ℕ) : ℕ := 210 * t ^ 2 + 391 * t + 179

/-- `A n = (n+1)(n+2)(n+3)`. -/
def A (n : ℕ) : ℕ := (n + 1) * (n + 2) * (n + 3)

/-- Slopes `a_i` of the six linear forms. -/
def slope : Fin 6 → ℕ := ![35, 6, 1, 210, 15, 14]

/-- Intercepts `b_i` of the six linear forms. -/
def icept : Fin 6 → ℕ := ![36, 5, 1, 181, 14, 13]

/-- The shift `j_i ∈ {1,2,3}` with `L_i ∣ f + j_i`. -/
def shift : Fin 6 → ℕ := ![1, 1, 2, 2, 3, 3]

/-- The linear forms `L_i(t) = a_i t + b_i`. -/
def L (i : Fin 6) (t : ℕ) : ℕ := slope i * t + icept i

/-- The number of carries when `n` is added to itself in base `p`; by Kummer's theorem this
is `v_p (binom(2n, n))`. -/
def carry (p n : ℕ) : ℕ := (Nat.centralBinom n).factorization p

/-- The target property `((n+3)!)² ∣ (2n)!`. -/
def Good (n : ℕ) : Prop := (n + 3).factorial ^ 2 ∣ (2 * n).factorial

/-- The set of exceptional primes for `G(0) = 180 · 181 · 182` (Section 4). -/
def S : Finset ℕ := {2, 3, 5, 7, 13, 181}

/-- `Y = 1000`: the threshold below which the fixed progression handles every prime. -/
def Y : ℕ := 1000

end Erdos727
