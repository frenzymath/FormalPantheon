import BoundedGaps.BombieriVinogradov.Analytic.StandardCompatibility
import BoundedGaps.BombieriVinogradov.Analytic.CenteredProgressionCorrection
import BoundedGaps.Arithmetic.ReciprocalTotientPrefix
import BoundedGaps.BombieriVinogradov.Analytic.SquareRootLogRange

/-!
# Recentring the standard weighted interface

The standard source term `y / phi(q)` is converted to the internal global
Chebyshev centre `psi(y) / phi(q)` by finite triangle inequalities.  The
modulus-one term is retained explicitly; it is the global error needed by the
later logarithmic-saving argument.  This file contains no PNT-prefix or
closed Bombieri--Vinogradov theorem.
-/

namespace BoundedGaps.BombieriVinogradov

open scoped BigOperators ArithmeticFunction.vonMangoldt

theorem maxWeightedProgressionDiscrepancyUpTo_one
    {x : Nat} (hx : 2 <= x) :
    maxWeightedProgressionDiscrepancyUpTo x 1 =
      (Finset.Icc 2 x).sup' (endpointRange_nonempty hx) (fun y =>
        |Chebyshev.psi (y : Real) - (y : Real)|) := by
  rw [maxWeightedProgressionDiscrepancyUpTo, dif_pos hx]
  simp only [reducedResidues]
  simp
  unfold weightedProgressionDiscrepancy
  simp_rw [show ∀ y : Nat, chebyshevProgressionSum y 1 0 =
      BoundedGaps.Maynard.chebyshevProgressionSum y 1 0 by intro y; rfl]
  simp_rw [BoundedGaps.Maynard.chebyshevProgressionSum_one_zero]
  norm_num [Nat.totient_one]

theorem maxWeightedProgressionDiscrepancyUpTo_nonneg (x q : Nat) :
    0 <= maxWeightedProgressionDiscrepancyUpTo x q := by
  by_cases hx : 2 <= x
  · by_cases hq : 0 < q
    · rw [maxWeightedProgressionDiscrepancyUpTo, dif_pos hx]
      rw [dif_pos hq]
      let a := (reducedResidues_nonempty hq).choose
      have ha : a ∈ reducedResidues q :=
        (reducedResidues_nonempty hq).choose_spec
      exact Finset.le_sup'_of_le
        (fun b =>
          (Finset.Icc 2 x).sup' (endpointRange_nonempty hx) (fun y =>
            weightedProgressionDiscrepancy y q b))
        ha
        (Finset.le_sup'_of_le
          (fun y => weightedProgressionDiscrepancy y q a)
          (Finset.mem_Icc.mpr ⟨le_rfl, hx⟩)
          (abs_nonneg _))
    · simp [maxWeightedProgressionDiscrepancyUpTo, hx, hq]
  · simp [maxWeightedProgressionDiscrepancyUpTo, hx]

theorem maxWeightedProgressionDiscrepancyUpTo_one_le_sum
    {x Q : Nat} (hQ : 1 <= Q) :
    maxWeightedProgressionDiscrepancyUpTo x 1 <=
      ∑ q ∈ Finset.Icc 1 Q,
        maxWeightedProgressionDiscrepancyUpTo x q := by
  calc
    maxWeightedProgressionDiscrepancyUpTo x 1 =
        ∑ q ∈ ({1} : Finset Nat),
          maxWeightedProgressionDiscrepancyUpTo x q := by simp
    _ <= ∑ q ∈ Finset.Icc 1 Q,
          maxWeightedProgressionDiscrepancyUpTo x q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        simp only [Finset.mem_singleton] at hq
        subst q
        exact Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩
      · intro q hq hqnot
        exact maxWeightedProgressionDiscrepancyUpTo_nonneg x q

theorem weightedProgressionDiscrepancy_le_centered_add_global
    {x q a : Nat} (hq : 1 <= q) :
    weightedProgressionDiscrepancy x q a <=
      BoundedGaps.Maynard.centeredProgressionDiscrepancy x q a +
        (q.totient : Real)⁻¹ *
          weightedProgressionDiscrepancy x 1 0 := by
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hφ : 0 < (q.totient : Real) := by
    exact_mod_cast (Nat.totient_pos.mpr hqpos)
  have hglobal :
      |chebyshevProgressionSum x 1 0 -
          (x : Real) / (Nat.totient 1 : Real)| =
        |Chebyshev.psi (x : Real) - (x : Real)| := by
    rw [show chebyshevProgressionSum x 1 0 =
      BoundedGaps.Maynard.chebyshevProgressionSum x 1 0 by rfl,
      BoundedGaps.Maynard.chebyshevProgressionSum_one_zero]
    norm_num [Nat.totient_one]
  unfold weightedProgressionDiscrepancy
  unfold BoundedGaps.Maynard.centeredProgressionDiscrepancy
  rw [hglobal]
  calc
    |chebyshevProgressionSum x q a - (x : Real) / (q.totient : Real)| ≤
        |chebyshevProgressionSum x q a -
            Chebyshev.psi (x : Real) / (q.totient : Real)| +
          |Chebyshev.psi (x : Real) / (q.totient : Real) -
            (x : Real) / (q.totient : Real)| :=
      abs_sub_le _ _ _
    _ = |chebyshevProgressionSum x q a -
            Chebyshev.psi (x : Real) / (q.totient : Real)| +
          (q.totient : Real)⁻¹ *
            |Chebyshev.psi (x : Real) - (x : Real)| := by
      congr 1
      rw [show Chebyshev.psi (x : Real) / (q.totient : Real) -
          (x : Real) / (q.totient : Real) =
          (q.totient : Real)⁻¹ *
            (Chebyshev.psi (x : Real) - (x : Real)) by ring]
      rw [abs_mul, abs_of_pos (inv_pos.mpr hφ)]

theorem centeredProgressionDiscrepancy_le_weighted_add_global
    {x q a : Nat} (hq : 1 <= q) :
    BoundedGaps.Maynard.centeredProgressionDiscrepancy x q a <=
      weightedProgressionDiscrepancy x q a +
        (q.totient : Real)⁻¹ *
          weightedProgressionDiscrepancy x 1 0 := by
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hφ : 0 < (q.totient : Real) := by
    exact_mod_cast (Nat.totient_pos.mpr hqpos)
  have hglobal :
      |chebyshevProgressionSum x 1 0 -
          (x : Real) / (Nat.totient 1 : Real)| =
        |Chebyshev.psi (x : Real) - (x : Real)| := by
    rw [show chebyshevProgressionSum x 1 0 =
      BoundedGaps.Maynard.chebyshevProgressionSum x 1 0 by rfl,
      BoundedGaps.Maynard.chebyshevProgressionSum_one_zero]
    norm_num [Nat.totient_one]
  unfold weightedProgressionDiscrepancy
  unfold BoundedGaps.Maynard.centeredProgressionDiscrepancy
  rw [hglobal]
  calc
    |chebyshevProgressionSum x q a -
          Chebyshev.psi (x : Real) / (q.totient : Real)| ≤
        |chebyshevProgressionSum x q a -
            (x : Real) / (q.totient : Real)| +
          |(x : Real) / (q.totient : Real) -
            Chebyshev.psi (x : Real) / (q.totient : Real)| :=
      abs_sub_le _ _ _
    _ = |chebyshevProgressionSum x q a -
            (x : Real) / (q.totient : Real)| +
          (q.totient : Real)⁻¹ *
            |Chebyshev.psi (x : Real) - (x : Real)| := by
      congr 1
      rw [show (x : Real) / (q.totient : Real) -
          Chebyshev.psi (x : Real) / (q.totient : Real) =
          (q.totient : Real)⁻¹ *
            ((x : Real) - Chebyshev.psi (x : Real)) by ring]
      rw [abs_mul, abs_of_pos (inv_pos.mpr hφ), abs_sub_comm]

theorem maxWeightedProgressionDiscrepancyUpTo_le_centered_add_global
    {x q : Nat} (hx : 2 <= x) (hq : 1 <= q) :
    maxWeightedProgressionDiscrepancyUpTo x q <=
      BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo x q +
        (q.totient : Real)⁻¹ *
          maxWeightedProgressionDiscrepancyUpTo x 1 := by
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hφ : 0 <= (q.totient : Real)⁻¹ :=
    (inv_nonneg.mpr (by positivity))
  rw [maxWeightedProgressionDiscrepancyUpTo, dif_pos hx]
  rw [dif_pos hqpos]
  rw [BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo_eq_sup_endpoint_residues
    hx hqpos]
  refine Finset.sup'_le (reducedResidues_nonempty hqpos) _ ?_
  intro a ha
  refine Finset.sup'_le (endpointRange_nonempty hx) _ ?_
  intro y hy
  have hcenter :
      BoundedGaps.Maynard.centeredProgressionDiscrepancy y q a ≤
        BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo x q := by
    rw [BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo_eq_sup_endpoint_residues
      hx hqpos]
    exact Finset.le_sup'_of_le
      (fun z =>
        (BoundedGaps.Maynard.coprimeResidues q).sup'
          (BoundedGaps.Maynard.coprimeResidues_nonempty hqpos)
          (fun b => BoundedGaps.Maynard.centeredProgressionDiscrepancy z q b))
      hy
      (Finset.le_sup'_of_le
        (fun b => BoundedGaps.Maynard.centeredProgressionDiscrepancy y q b)
        ha le_rfl)
  rw [BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo_eq_sup_endpoint_residues
    hx hqpos] at hcenter
  have hglobal : weightedProgressionDiscrepancy y 1 0 ≤
      maxWeightedProgressionDiscrepancyUpTo x 1 := by
    rw [maxWeightedProgressionDiscrepancyUpTo_one hx]
    calc
      weightedProgressionDiscrepancy y 1 0 =
          |Chebyshev.psi (y : Real) - (y : Real)| := by
        unfold weightedProgressionDiscrepancy
        simp only [show chebyshevProgressionSum y 1 0 =
          BoundedGaps.Maynard.chebyshevProgressionSum y 1 0 by rfl,
          BoundedGaps.Maynard.chebyshevProgressionSum_one_zero,
          Nat.totient_one]
        norm_num
      _ ≤ _ := Finset.le_sup'
        (fun z : Nat => |Chebyshev.psi (z : Real) - (z : Real)|) hy
  exact (weightedProgressionDiscrepancy_le_centered_add_global hq).trans
    (add_le_add hcenter (mul_le_mul_of_nonneg_left hglobal hφ))

theorem maxCenteredProgressionDiscrepancyUpTo_le_weighted_add_global
    {x q : Nat} (hx : 2 <= x) (hq : 1 <= q) :
    BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo x q <=
      maxWeightedProgressionDiscrepancyUpTo x q +
        (q.totient : Real)⁻¹ *
          maxWeightedProgressionDiscrepancyUpTo x 1 := by
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hφ : 0 <= (q.totient : Real)⁻¹ :=
    (inv_nonneg.mpr (by positivity))
  rw [BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo_eq_sup_endpoint_residues
    hx hqpos]
  refine Finset.sup'_le (endpointRange_nonempty hx) _ ?_
  intro y hy
  refine Finset.sup'_le (BoundedGaps.Maynard.coprimeResidues_nonempty hqpos) _ ?_
  intro a ha
  have hweighted : weightedProgressionDiscrepancy y q a ≤
      maxWeightedProgressionDiscrepancyUpTo x q := by
    rw [maxWeightedProgressionDiscrepancyUpTo, dif_pos hx]
    rw [dif_pos hqpos]
    exact Finset.le_sup'_of_le
      (fun b =>
        (Finset.Icc 2 x).sup' (endpointRange_nonempty hx) (fun z =>
          weightedProgressionDiscrepancy z q b))
      ha
      (Finset.le_sup'
        (fun z => weightedProgressionDiscrepancy z q a) hy)
  have hglobal : weightedProgressionDiscrepancy y 1 0 ≤
      maxWeightedProgressionDiscrepancyUpTo x 1 := by
    rw [maxWeightedProgressionDiscrepancyUpTo_one hx]
    calc
      weightedProgressionDiscrepancy y 1 0 =
          |Chebyshev.psi (y : Real) - (y : Real)| := by
        unfold weightedProgressionDiscrepancy
        simp only [show chebyshevProgressionSum y 1 0 =
          BoundedGaps.Maynard.chebyshevProgressionSum y 1 0 by rfl,
          BoundedGaps.Maynard.chebyshevProgressionSum_one_zero,
          Nat.totient_one]
        norm_num
      _ ≤ _ := Finset.le_sup'
        (fun z : Nat => |Chebyshev.psi (z : Real) - (z : Real)|) hy
  exact (centeredProgressionDiscrepancy_le_weighted_add_global hq).trans
    (add_le_add hweighted (mul_le_mul_of_nonneg_left hglobal hφ))

theorem sum_inv_totient_eq_reciprocalTotientPrefix (Q : Nat) :
    (∑ q ∈ Finset.Icc 1 Q, (q.totient : Real)⁻¹) =
      BoundedGaps.Maynard.reciprocalTotientPrefix Q := by
  unfold BoundedGaps.Maynard.reciprocalTotientPrefix
  congr 1

theorem reciprocalTotientPrefix_nonneg (Q : Nat) :
    0 <= BoundedGaps.Maynard.reciprocalTotientPrefix Q := by
  unfold BoundedGaps.Maynard.reciprocalTotientPrefix
  apply Finset.sum_nonneg
  intro q hq
  positivity

theorem reciprocalTotientPrefix_lt_five_mul_log_of_le_sqrt
    {x Q : Nat} (hx : 4 <= x) (hQ : 0 < Q)
    (hQsqrt : (Q : Real) <= Real.sqrt (x : Real)) :
    BoundedGaps.Maynard.reciprocalTotientPrefix Q <
      5 * Real.log (x : Real) := by
  exact (BoundedGaps.Maynard.reciprocalTotientPrefix_le_four_mul_one_add_log hQ).trans_lt
    (BoundedGaps.Maynard.four_mul_one_add_log_lt_five_mul_log_of_le_sqrt
      hx hQ hQsqrt)

theorem sum_maxWeightedProgressionDiscrepancyUpTo_le_centered_add_global
    {x Q : Nat} (hx : 2 <= x) :
    (∑ q ∈ Finset.Icc 1 Q,
      maxWeightedProgressionDiscrepancyUpTo x q) <=
      (∑ q ∈ Finset.Icc 1 Q,
        BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo x q) +
      BoundedGaps.Maynard.reciprocalTotientPrefix Q *
        maxWeightedProgressionDiscrepancyUpTo x 1 := by
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        maxWeightedProgressionDiscrepancyUpTo x q) ≤
      ∑ q ∈ Finset.Icc 1 Q,
        (BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo x q +
          (q.totient : Real)⁻¹ *
            maxWeightedProgressionDiscrepancyUpTo x 1) := by
      apply Finset.sum_le_sum
      intro q hq
      exact maxWeightedProgressionDiscrepancyUpTo_le_centered_add_global hx
        (Finset.mem_Icc.mp hq).1
    _ = (∑ q ∈ Finset.Icc 1 Q,
          BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo x q) +
        (∑ q ∈ Finset.Icc 1 Q, (q.totient : Real)⁻¹) *
          maxWeightedProgressionDiscrepancyUpTo x 1 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ = _ := by rw [sum_inv_totient_eq_reciprocalTotientPrefix]

theorem sum_maxCenteredProgressionDiscrepancyUpTo_le_weighted_add_global
    {x Q : Nat} (hx : 2 <= x) :
    (∑ q ∈ Finset.Icc 1 Q,
      BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo x q) <=
      (∑ q ∈ Finset.Icc 1 Q,
        maxWeightedProgressionDiscrepancyUpTo x q) +
      BoundedGaps.Maynard.reciprocalTotientPrefix Q *
        maxWeightedProgressionDiscrepancyUpTo x 1 := by
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo x q) ≤
      ∑ q ∈ Finset.Icc 1 Q,
        (maxWeightedProgressionDiscrepancyUpTo x q +
          (q.totient : Real)⁻¹ *
            maxWeightedProgressionDiscrepancyUpTo x 1) := by
      apply Finset.sum_le_sum
      intro q hq
      exact maxCenteredProgressionDiscrepancyUpTo_le_weighted_add_global hx
        (Finset.mem_Icc.mp hq).1
    _ = (∑ q ∈ Finset.Icc 1 Q,
          maxWeightedProgressionDiscrepancyUpTo x q) +
        (∑ q ∈ Finset.Icc 1 Q, (q.totient : Real)⁻¹) *
          maxWeightedProgressionDiscrepancyUpTo x 1 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ = _ := by rw [sum_inv_totient_eq_reciprocalTotientPrefix]

end BoundedGaps.BombieriVinogradov
