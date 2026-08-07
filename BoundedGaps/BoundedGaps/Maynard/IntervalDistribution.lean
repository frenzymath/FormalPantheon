import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

import BoundedGaps.Maynard.Growth

/-!
# Interval prime discrepancies

Maynard2013v3, Section 5, defines the interval error `E(N,q)` for
`N <= n < 2N`.  This file keeps those endpoints explicit and proves the finite
count identity needed to compare it with global prime counts.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

/-- The number of primes in `[N, 2*N)` in one residue class. -/
def primeCountInInterval (N q a : ℕ) : ℕ :=
  ((Finset.Ico N (2 * N)).filter
    (fun n => n.Prime ∧ n % q = a % q)).card

/-- The total number of primes in `[N, 2*N)`. -/
def primeCountTotalInInterval (N : ℕ) : ℕ :=
  (Finset.Ico N (2 * N)).filter Nat.Prime |>.card

/-- Absolute discrepancy for one residue class on `[N,2*N)`. -/
noncomputable def intervalProgressionDiscrepancy (N q a : ℕ) : ℝ :=
  |(primeCountInInterval N q a : ℝ) -
    (primeCountTotalInInterval N : ℝ) / (Nat.totient q : ℝ)|

/-- Maynard's `E(N,q)`: one plus the largest reduced-residue discrepancy. -/
noncomputable def maxIntervalError (N q : ℕ) : ℝ :=
  if hq : 0 < q then
    1 + (coprimeResidues q).sup' (coprimeResidues_nonempty hq)
      (intervalProgressionDiscrepancy N q)
  else 1

theorem cast_primeCountInInterval {N q a : ℕ} (hN : 0 < N) :
    (primeCountInInterval N q a : ℝ) =
      (primeCountUpTo (2 * N - 1) q a : ℝ) -
        (primeCountUpTo (N - 1) q a : ℝ) := by
  have h2N : 1 ≤ 2 * N := by omega
  have hupper : 2 * N - 1 + 1 = 2 * N := by omega
  have hlower : N - 1 + 1 = N := by omega
  unfold primeCountInInterval primeCountUpTo
  rw [hupper, hlower]
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter,
    Finset.natCast_card_filter]
  exact Finset.sum_Ico_eq_sub _ (by omega)

theorem cast_primeCountTotalInInterval {N : ℕ} (hN : 0 < N) :
    (primeCountTotalInInterval N : ℝ) =
      (primeCountTotal (2 * N - 1) : ℝ) -
        (primeCountTotal (N - 1) : ℝ) := by
  have h2N : 1 ≤ 2 * N := by omega
  have hupper : 2 * N - 1 + 1 = 2 * N := by omega
  have hlower : N - 1 + 1 = N := by omega
  unfold primeCountTotalInInterval primeCountTotal Nat.primeCounting
    Nat.primeCounting'
  rw [hupper, hlower, Nat.count_eq_card_filter_range,
    Nat.count_eq_card_filter_range]
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter,
    Finset.natCast_card_filter]
  exact Finset.sum_Ico_eq_sub _ (by omega)

theorem intervalProgressionDiscrepancy_le_global_sum
    {N q a : ℕ} (hN : 0 < N) :
    intervalProgressionDiscrepancy N q a ≤
      progressionDiscrepancy (2 * N - 1) q a +
        progressionDiscrepancy (N - 1) q a := by
  unfold intervalProgressionDiscrepancy progressionDiscrepancy
  rw [cast_primeCountInInterval hN, cast_primeCountTotalInInterval hN]
  have hrearrange :
      ((primeCountUpTo (2 * N - 1) q a : ℝ) -
          (primeCountUpTo (N - 1) q a : ℝ)) -
          ((primeCountTotal (2 * N - 1) : ℝ) -
            (primeCountTotal (N - 1) : ℝ)) / (Nat.totient q : ℝ) =
        ((primeCountUpTo (2 * N - 1) q a : ℝ) -
          (primeCountTotal (2 * N - 1) : ℝ) / (Nat.totient q : ℝ)) -
        ((primeCountUpTo (N - 1) q a : ℝ) -
          (primeCountTotal (N - 1) : ℝ) / (Nat.totient q : ℝ)) := by
    ring
  rw [hrearrange]
  let A : ℝ := (primeCountUpTo (2 * N - 1) q a : ℝ) -
    (primeCountTotal (2 * N - 1) : ℝ) / (Nat.totient q : ℝ)
  let B : ℝ := (primeCountUpTo (N - 1) q a : ℝ) -
    (primeCountTotal (N - 1) : ℝ) / (Nat.totient q : ℝ)
  change |A - B| ≤ |A| + |B|
  calc
    |A - B| ≤ |A - 0| + |0 - B| := abs_sub_le A 0 B
    _ = |A| + |B| := by simp only [sub_zero, zero_sub, abs_neg]

theorem maxIntervalError_le_global_sum {N q : ℕ} (hN : 0 < N)
    (hq : 0 < q) :
    maxIntervalError N q ≤
      1 + maxProgressionDiscrepancy (2 * N - 1) q +
        maxProgressionDiscrepancy (N - 1) q := by
  rw [maxIntervalError, dif_pos hq]
  calc
    1 + (coprimeResidues q).sup' (coprimeResidues_nonempty hq)
          (intervalProgressionDiscrepancy N q) ≤
        1 + (maxProgressionDiscrepancy (2 * N - 1) q +
          maxProgressionDiscrepancy (N - 1) q) := by
      apply add_le_add_right
      refine Finset.sup'_le (coprimeResidues_nonempty hq)
        (intervalProgressionDiscrepancy N q) ?_
      intro a ha
      exact (intervalProgressionDiscrepancy_le_global_sum hN).trans
        (add_le_add (progressionDiscrepancy_le_max hq ha)
          (progressionDiscrepancy_le_max hq ha))
    _ = 1 + maxProgressionDiscrepancy (2 * N - 1) q +
        maxProgressionDiscrepancy (N - 1) q := by ring

theorem sum_maxIntervalError_le_global_sums {N : ℕ} (hN : 0 < N)
    (S : Finset ℕ) (hS : ∀ q ∈ S, 0 < q) :
    (∑ q ∈ S, maxIntervalError N q) ≤
      (S.card : ℝ) +
        (∑ q ∈ S, maxProgressionDiscrepancy (2 * N - 1) q) +
        (∑ q ∈ S, maxProgressionDiscrepancy (N - 1) q) := by
  calc
    (∑ q ∈ S, maxIntervalError N q) ≤
        ∑ q ∈ S, (1 + maxProgressionDiscrepancy (2 * N - 1) q +
          maxProgressionDiscrepancy (N - 1) q) := by
      apply Finset.sum_le_sum
      intro q hq
      exact maxIntervalError_le_global_sum hN (hS q hq)
    _ = (S.card : ℝ) +
        (∑ q ∈ S, maxProgressionDiscrepancy (2 * N - 1) q) +
        (∑ q ∈ S, maxProgressionDiscrepancy (N - 1) q) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        mul_one]

theorem hasPrimeLevel_implies_raw_interval_bound {θ : ℝ}
    (hθ : 0 ≤ θ) (hlevel : hasPrimeLevel θ) :
    ∀ A : ℝ, 0 < A →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
        ∀ N : ℕ, N₀ ≤ N →
          (∑ q ∈ Finset.Icc 1 (modulusCutoff θ (N - 1)),
            maxIntervalError N q) ≤
            ((Finset.Icc 1 (modulusCutoff θ (N - 1))).card : ℝ) +
              C * ((2 * N - 1 : ℕ) : ℝ) /
                Real.rpow (Real.log ((2 * N - 1 : ℕ) : ℝ)) A +
              C * ((N - 1 : ℕ) : ℝ) /
                Real.rpow (Real.log ((N - 1 : ℕ) : ℝ)) A := by
  intro A hA
  obtain ⟨C, hC, X₀, hX₀, hbound⟩ := hlevel A hA
  refine ⟨C, hC, max 3 (X₀ + 1), le_max_left _ _, ?_⟩
  intro N hN
  have hN3 : 3 ≤ N := le_trans (le_max_left 3 (X₀ + 1)) hN
  have hNm1 : X₀ ≤ N - 1 := by omega
  have hN2m1 : X₀ ≤ 2 * N - 1 := by omega
  have hboundL := hbound (N - 1) hNm1
  have hboundU := hbound (2 * N - 1) hN2m1
  let S := Finset.Icc 1 (modulusCutoff θ (N - 1))
  have hSpos : ∀ q ∈ S, 0 < q := by
    intro q hq
    exact (Finset.mem_Icc.mp hq).1
  have hsubset : S ⊆ Finset.Icc 1 (modulusCutoff θ (2 * N - 1)) := by
    apply Finset.Icc_subset_Icc le_rfl
    apply modulusCutoff_mono hθ
    omega
  have hsumL :
      (∑ q ∈ S, maxProgressionDiscrepancy (N - 1) q) ≤
        ∑ q ∈ Finset.Icc 1 (modulusCutoff θ (N - 1)),
          maxProgressionDiscrepancy (N - 1) q := by
    exact le_rfl
  have hsumU :
      (∑ q ∈ S, maxProgressionDiscrepancy (2 * N - 1) q) ≤
        ∑ q ∈ Finset.Icc 1 (modulusCutoff θ (2 * N - 1)),
          maxProgressionDiscrepancy (2 * N - 1) q := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro q _ hqS
    exact maxProgressionDiscrepancy_nonneg _ _
  have hfinite := sum_maxIntervalError_le_global_sums (N := N) (by omega)
    S hSpos
  change (∑ q ∈ S, maxIntervalError N q) ≤ _
  calc
    (∑ q ∈ S, maxIntervalError N q) ≤
        (S.card : ℝ) +
          (∑ q ∈ S, maxProgressionDiscrepancy (2 * N - 1) q) +
          (∑ q ∈ S, maxProgressionDiscrepancy (N - 1) q) := hfinite
    _ ≤ (S.card : ℝ) +
          (∑ q ∈ Finset.Icc 1 (modulusCutoff θ (2 * N - 1)),
            maxProgressionDiscrepancy (2 * N - 1) q) +
          (∑ q ∈ Finset.Icc 1 (modulusCutoff θ (N - 1)),
            maxProgressionDiscrepancy (N - 1) q) := by
      exact add_le_add (add_le_add le_rfl hsumU) hsumL
    _ ≤ (S.card : ℝ) +
          C * ((2 * N - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log ((2 * N - 1 : ℕ) : ℝ)) A +
          C * ((N - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log ((N - 1 : ℕ) : ℝ)) A := by
      exact add_le_add (add_le_add le_rfl hboundU) hboundL
    _ = ((Finset.Icc 1 (modulusCutoff θ (N - 1))).card : ℝ) +
          C * ((2 * N - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log ((2 * N - 1 : ℕ) : ℝ)) A +
          C * ((N - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log ((N - 1 : ℕ) : ℝ)) A := by rfl

/- The endpoint terms in Maynard2013v3, Section 5, can be put on one
   common logarithmic scale once the elementary growth bounds are available. -/
theorem hasPrimeLevel_implies_interval_bound {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) (hlevel : hasPrimeLevel θ) :
    ∀ A : ℝ, 0 < A →
      ∃ C' : ℝ, 0 ≤ C' ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
        ∀ N : ℕ, N₀ ≤ N →
          (∑ q ∈ Finset.Icc 1 (modulusCutoff θ (N - 1)),
            maxIntervalError N q) ≤
            C' * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) A := by
  intro A hA
  obtain ⟨C, hC, Nraw, hNraw, hraw⟩ :=
    hasPrimeLevel_implies_raw_interval_bound hθ₀ hlevel A hA
  obtain ⟨Ncount, hNcount, hcount⟩ :=
    exists_modulus_count_mul_log_rpow_le hθ₀ hθ₁ (le_of_lt hA)
  let K : ℝ := Real.rpow 2 A
  let C' : ℝ := 1 + 2 * C + C * K
  refine ⟨C', ?_, max 3 (max Nraw Ncount), le_max_left _ _, ?_⟩
  · dsimp [C', K]
    positivity
  · intro N hN
    have hNinner : max Nraw Ncount ≤ N := by
      exact le_trans (le_max_right (3 : ℕ) (max Nraw Ncount)) hN
    have hNraw' : Nraw ≤ N := le_trans (le_max_left Nraw Ncount) hNinner
    have hNcount' : Ncount ≤ N := le_trans (le_max_right Nraw Ncount) hNinner
    have hN3 : 3 ≤ N := le_trans (le_max_left (3 : ℕ) (max Nraw Ncount)) hN
    have hNpos : 0 < (N : ℝ) := by positivity
    have hNm1pos : 0 < ((N - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < N - 1 by omega)
    have hN2m1pos : 0 < ((2 * N - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < 2 * N - 1 by omega)
    have hlogNpos : 0 < Real.log (N : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hlogNm1pos : 0 < Real.log ((N - 1 : ℕ) : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (show 1 < N - 1 by omega))
    have hlogN2m1pos : 0 < Real.log ((2 * N - 1 : ℕ) : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (show 1 < 2 * N - 1 by omega))
    let M : ℝ := Real.rpow (Real.log (N : ℝ)) A
    let L : ℝ := Real.rpow (Real.log ((N - 1 : ℕ) : ℝ)) A
    let U : ℝ := Real.rpow (Real.log ((2 * N - 1 : ℕ) : ℝ)) A
    have hMpos : 0 < M := by
      dsimp [M]
      exact Real.rpow_pos_of_pos hlogNpos A
    have hLpos : 0 < L := by
      dsimp [L]
      exact Real.rpow_pos_of_pos hlogNm1pos A
    have hUpos : 0 < U := by
      dsimp [U]
      exact Real.rpow_pos_of_pos hlogN2m1pos A
    have hMnonneg : 0 ≤ M := hMpos.le
    have hLnonneg : 0 ≤ L := hLpos.le
    have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := hlogNpos.le
    have hlogNm1_nonneg : 0 ≤ Real.log ((N - 1 : ℕ) : ℝ) := hlogNm1pos.le
    have hlogN2m1_nonneg : 0 ≤ Real.log ((2 * N - 1 : ℕ) : ℝ) :=
      hlogN2m1pos.le
    have hN_le_N2m1 : (N : ℝ) ≤ ((2 * N - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show N ≤ 2 * N - 1 by omega)
    have hlogN_le_N2m1 : Real.log (N : ℝ) ≤
        Real.log ((2 * N - 1 : ℕ) : ℝ) :=
      Real.strictMonoOn_log.monotoneOn
        (show (N : ℝ) ∈ Set.Ioi 0 by exact hNpos)
        (show ((2 * N - 1 : ℕ) : ℝ) ∈ Set.Ioi 0 by exact hN2m1pos)
        hN_le_N2m1
    have hM_le_U : M ≤ U := by
      dsimp [M, U]
      exact Real.rpow_le_rpow hlogN_nonneg hlogN_le_N2m1 (le_of_lt hA)
    have hN_le_sq : N ≤ (N - 1) ^ 2 := by
      have hsmall : 2 ≤ N - 1 := by omega
      have hmul : 2 * (N - 1) ≤ (N - 1) * (N - 1) := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left (N - 1) hsmall
      calc
        N ≤ 2 * (N - 1) := by omega
        _ ≤ (N - 1) * (N - 1) := hmul
        _ = (N - 1) ^ 2 := by simp [pow_two]
    have hN_le_sq_real : (N : ℝ) ≤ ((N - 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hN_le_sq
    have hlogN_le_twice : Real.log (N : ℝ) ≤
        2 * Real.log ((N - 1 : ℕ) : ℝ) := by
      have hlog := Real.strictMonoOn_log.monotoneOn
        (show (N : ℝ) ∈ Set.Ioi 0 by exact hNpos)
        (show ((N - 1 : ℕ) : ℝ) ^ 2 ∈ Set.Ioi 0 by
          change 0 < ((N - 1 : ℕ) : ℝ) ^ 2
          positivity)
        hN_le_sq_real
      simpa [Real.log_pow] using hlog
    have hM_le_KL : M ≤ K * L := by
      dsimp [M, K, L]
      calc
        Real.rpow (Real.log (N : ℝ)) A ≤
            Real.rpow (2 * Real.log ((N - 1 : ℕ) : ℝ)) A :=
          Real.rpow_le_rpow hlogN_nonneg hlogN_le_twice (le_of_lt hA)
        _ = Real.rpow 2 A * Real.rpow (Real.log ((N - 1 : ℕ) : ℝ)) A := by
          exact Real.mul_rpow (x := (2 : ℝ))
            (y := Real.log ((N - 1 : ℕ) : ℝ)) (z := A) (by norm_num)
            hlogNm1_nonneg
    have hnum_upper : C * ((2 * N - 1 : ℕ) : ℝ) ≤
        (2 * C) * (N : ℝ) := by
      have hsub : ((2 * N - 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
        exact_mod_cast (Nat.sub_le (2 * N) 1)
      calc
        C * ((2 * N - 1 : ℕ) : ℝ) ≤ C * (2 * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hsub hC
        _ = (2 * C) * (N : ℝ) := by ring
    have hupper : C * ((2 * N - 1 : ℕ) : ℝ) / U ≤
        (2 * C) * (N : ℝ) / M := by
      exact div_le_div₀ (by positivity) hnum_upper hMpos hM_le_U
    have hnum_lower : C * ((N - 1 : ℕ) : ℝ) ≤ C * (N : ℝ) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.sub_le N 1)) hC
    have hlower : C * ((N - 1 : ℕ) : ℝ) / L ≤
        (C * K) * (N : ℝ) / M := by
      apply (le_div_iff₀ hMpos).2
      calc
        C * ((N - 1 : ℕ) : ℝ) / L * M =
            (C * ((N - 1 : ℕ) : ℝ) * M) / L := by ring
        _ ≤ (C * (N : ℝ) * (K * L)) / L := by
          apply div_le_div_of_nonneg_right _ hLnonneg
          calc
            C * ((N - 1 : ℕ) : ℝ) * M ≤ C * (N : ℝ) * M := by
              exact mul_le_mul_of_nonneg_right hnum_lower hMnonneg
            _ ≤ C * (N : ℝ) * (K * L) := by
              exact mul_le_mul_of_nonneg_left hM_le_KL (mul_nonneg hC hNpos.le)
        _ = (C * K) * (N : ℝ) := by field_simp
    have hcardmul := hcount N hNcount'
    have hcard :
        ((Finset.Icc 1 (modulusCutoff θ (N - 1))).card : ℝ) ≤
          (N : ℝ) / M := by
      apply (le_div_iff₀ hMpos).2
      simpa [M, mul_comm] using hcardmul
    have hraw' := hraw N hNraw'
    change (∑ q ∈ Finset.Icc 1 (modulusCutoff θ (N - 1)),
      maxIntervalError N q) ≤ _
    calc
      (∑ q ∈ Finset.Icc 1 (modulusCutoff θ (N - 1)), maxIntervalError N q) ≤
          ((Finset.Icc 1 (modulusCutoff θ (N - 1))).card : ℝ) +
            C * ((2 * N - 1 : ℕ) : ℝ) / U +
            C * ((N - 1 : ℕ) : ℝ) / L := by
        simpa [M, L, U] using hraw'
      _ ≤ (N : ℝ) / M + (2 * C) * (N : ℝ) / M +
            (C * K) * (N : ℝ) / M := by
        exact add_le_add (add_le_add hcard hupper) hlower
      _ = C' * (N : ℝ) / M := by
        dsimp [C']
        field_simp
      _ = C' * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) A := by rfl

end BoundedGaps.Maynard
