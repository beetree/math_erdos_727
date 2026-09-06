# Erdős Problem 727 (k = 3): paper correspondence

Navigation from the sections of
[`expert_advice/erdos_727_k2_k3_proof.md`](../expert_advice/erdos_727_k2_k3_proof.md) to the
Lean development.  See [FORMALIZATION.md](../FORMALIZATION.md) for status and design decisions.

| Paper component | Formulation | Lean location | Principal declarations |
| --- | --- | --- | --- |
| §1 Theorem, (1.2) | infinitely many `n` with `((n+3)!)² ∣ (2n)!` | `Main.lean`, `Final.lean` | `infinite_good`, `k3_of_mertensAP`, `erdos727_k3` |
| §1 Corollary, (1.3) | the `k = 2` case | `Main.lean`, `Final.lean` | `k2_of_k3`, `erdos727_k2` |
| §2 (2.1)–(2.3) | `((n+3)!)² ∣ (2n)! ↔ A(n)² ∣ binom(2n,n) ↔ ∀ p, 2 v_p(A n) ≤ carry p n` | `Carries.lean` | `good_iff_sq_dvd_centralBinom`, `good_iff`, `carry_eq_card` |
| §3 (3.1), table | six linear factors, derivative values `c_i`, resultants | `Polynomial.lean` | `f_add_one/two/three`, `A_f`, `slope_mul_fderiv`, `eq_of_prime_dvd_two_forms`, `not_dvd_fderiv` |
| §4 (4.1)–(4.3) | local congruences, Hensel witnesses, CRT, the progression | `SmallPrimes.lean` | `local_good_S`, `local_good_nonS`, `exists_progression`, `Q`, `t₀`, `small_primes_good` |
| §4 end | `F(v)`, `𝓛_i(v)`, size bounds | `Progression.lean` | `F`, `Lv`, `Lv_le`, `F_le`, `sq_le_F` |
| §5 (5.1) | repeated prime factors | `Failure.lean`, `Range/Square.lean` | `sqSet`, `card_sqSet_le`, `sum_inv_sq_le`, `sq_bound` |
| §5 (5.2) | failure events, first carry, `v_p(A) ≤ 1` | `Progression.lean`, `Failure.lean` | `first_carry`, `factorization_A_F_le_one`, `good_F_of`, `exists_bad_prime_of_not_good`, `badSet`, `card_failSet_le` |
| §6 (6.2)–(6.3) | Mertens' second theorem, block sums | `Analytic/Mertens.lean` (+ vendored `MertensSource.lean`) | `mertens_second`, `sum_inv_prime_block` |
| §6 (6.4), (6.1) | primes in progressions (Mertens strength suffices) | `Analytic/Mertens.lean`, `Analytic/Character*.lean`, `Analytic/MertensAPProof.lean` | `MertensAP`, `mertens_first_AP`, `mertensAP_of_neZero`, `mertensAP_210` |
| §7 (7.1)–(7.4) | residue counting with digit sets, blocks `ℓ(p) = m` | `DigitSets.lean`, `Range/Small.lean` | `carryDigits`, `mem_carryDigitSet_of_noCarry`, `card_badSet_le`, `small_bound` |
| §8 Lemma (8.1) | quadratic exponential sums (via Weyl differencing) | `Analytic/WeylSum.lean` | `norm_sum_e_le_inv_dist₁`, `sum_geomBound_le`, `weyl_quadratic` |
| §9 (9.3)–(9.7) | uniform distribution, replaced by finite Fourier on `ℤ/p^J` | `Analytic/DigitFourier.lean`, `Range/Medium.lean` | `card_filter_le_main_add_error`, `sum_norm_fourier_digitSet_le`, `medium_bound` |
| §10 (10.1)–(10.3) | boundary strips | `Range/Medium.lean` | `medium_bound` |
| §11 (11.2)–(11.7) | exact identities, residue tables, class counting | `Polynomial.lean`, `Range/Large.lean` | `f_eq_L0`…`f_eq_L5`, `badRes`, `large_bound` |
| §12 (12.1) | summation of proportions, infinitude | `Main.lean`, `Failure.lean` | `card_failSet_lt`, `exists_good_of_card_lt`, `infinite_good_of_eventually` |
| §13 | finite checks (not needed for the theorem) | — | — |

## Representation choices

* Levels and carries.  The manuscript's `{n/p^h} ≥ 1/2` is `p^h ≤ 2 (n % p^h)`; `carry p n` is
  `(Nat.centralBinom n).factorization p`, and Kummer's theorem is Mathlib's `Nat.factorization_choose'`.
* The failure set is a `Finset` of parameters `v ∈ [X, 2X)`, and every limiting proportion of the
  manuscript becomes an eventual inequality `∀ᶠ X in atTop, (count : ℝ) ≤ c X` with slackened `c`.
* Section 9's torus equidistribution is replaced by an exact identity on `ℤ/p^J`; the error is bounded
  explicitly instead of by a limiting argument over Fourier approximants.
