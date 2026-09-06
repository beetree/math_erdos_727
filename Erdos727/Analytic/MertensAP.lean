import Erdos727.Analytic.CharacterSums

/-!
# Mertens' theorem in arithmetic progressions modulo 210

This is the single analytic obligation of the formalization: the proposition `MertensAP 210`
of `Erdos727/Analytic/Mertens.lean`.  Classically it follows from Mertens' first theorem in
arithmetic progressions, i.e. from `∑_{p ≤ x} χ(p) log p / p = O(1)` for every nontrivial
Dirichlet character `χ` modulo `210`, which in turn rests on `L(1, χ) ≠ 0`
(`DirichletCharacter.LFunction_apply_one_ne_zero` in Mathlib) and partial summation.

It is discharged by `mertensAP_of_neZero` from `Erdos727/Analytic/MertensAPProof.lean`; its
status is that of the character-sum chain in `Erdos727/Analytic/CharacterSums.lean`.
-/

namespace Erdos727

theorem mertensAP_210 : MertensAP 210 := mertensAP_of_neZero 210

end Erdos727
