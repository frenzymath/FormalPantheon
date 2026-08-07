import BoundedGaps.BombieriVinogradov.Analytic.RawPrimitiveMaxima
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Raw primitive mean normalization

This file formalizes the finite reduction immediately before partial
summation on Akbary--Hambrook2013v2, Section 7, p. 25. It enlarges rough
conductors to the interval above `Q1` and rewrites the raw summand as `S(q)/q`.
The continuous Abel identity remains separate.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

noncomputable local instance roughModulusAboveDecidableForMeanNormalization
    (Q1 : ℝ) : DecidablePred (roughModulusAbove Q1) :=
  Classical.decPred _

noncomputable local instance realCutoffDecidableForMeanNormalization
    (Q1 : ℝ) : DecidablePred (fun q : ℕ ↦ Q1 < (q : ℝ)) :=
  Classical.decPred _

/-- The source weight `S(q)`: raw primitive mass normalized by `q / phi(q)`. -/
noncomputable def primitiveRawMeanValueWeight (x q : ℕ) : ℝ :=
  ((q : ℝ) / (q.totient : ℝ)) *
    ∑ ψ : primitiveCharacters q,
      primitiveRawEndpointMaximum x q ψ

/-- The totalized mean-value weight vanishes at level zero. -/
theorem primitiveRawMeanValueWeight_zero (x : ℕ) :
    primitiveRawMeanValueWeight x 0 = 0 := by
  simp [primitiveRawMeanValueWeight]

/-- The raw primitive mean-value weight is nonnegative. -/
theorem primitiveRawMeanValueWeight_nonneg (x q : ℕ) :
    0 ≤ primitiveRawMeanValueWeight x q := by
  unfold primitiveRawMeanValueWeight
  apply mul_nonneg
  · positivity
  · exact sum_primitiveRawEndpointMaximum_nonneg x q

/-- A rough nontrivial modulus lies strictly above its real least-factor
cutoff. -/
theorem roughModulusAbove_lt_level
    {Q1 : ℝ} {q : ℕ} (hq : roughModulusAbove Q1 q) :
    Q1 < (q : ℝ) := by
  have hqpos : 0 < q := lt_trans Nat.zero_lt_one hq.1
  exact hq.2.trans_le (by
    exact_mod_cast Nat.minFac_le hqpos)

/-- Positive natural levels above a real cutoff form the interval beginning
just after its natural floor. -/
theorem filter_realCutoff_eq_Ioc_natFloor (Q : ℕ) (Q1 : ℝ) :
    (Finset.Ioc 0 Q).filter (fun q : ℕ ↦ Q1 < (q : ℝ)) =
      Finset.Ioc ⌊Q1⌋₊ Q := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hqpos, hqQ⟩, hQ1q⟩
    exact ⟨(Nat.floor_lt' hqpos.ne').2 hQ1q, hqQ⟩
  · rintro ⟨hfloor, hqQ⟩
    have hqpos : 0 < q := by omega
    exact ⟨⟨hqpos, hqQ⟩, (Nat.floor_lt' hqpos.ne').1 hfloor⟩

/-- At positive level, reciprocal totient times raw mass is exactly `S(q)/q`. -/
theorem inv_totient_mul_sum_primitiveRawEndpointMaximum_eq_meanValueWeight_div
    {x q : ℕ} (hq : 0 < q) :
    (q.totient : ℝ)⁻¹ *
        (∑ ψ : primitiveCharacters q,
          primitiveRawEndpointMaximum x q ψ) =
      primitiveRawMeanValueWeight x q / (q : ℝ) := by
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast hq.ne'
  have hphi0 : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  unfold primitiveRawMeanValueWeight
  field_simp

/-- Normalize every positive summand on the enlarged real-cutoff interval. -/
theorem sum_interval_invTotient_primitiveRaw_eq_meanValueWeight_div
    (x Q : ℕ) (Q1 : ℝ) :
    (∑ q ∈ Finset.Ioc ⌊Q1⌋₊ Q,
      (q.totient : ℝ)⁻¹ *
        ∑ ψ : primitiveCharacters q,
          primitiveRawEndpointMaximum x q ψ) =
      ∑ q ∈ Finset.Ioc ⌊Q1⌋₊ Q,
        primitiveRawMeanValueWeight x q / (q : ℝ) := by
  apply Finset.sum_congr rfl
  intro q hqmem
  have hqpos : 0 < q :=
    (Nat.zero_le ⌊Q1⌋₊).trans_lt (Finset.mem_Ioc.mp hqmem).1
  exact inv_totient_mul_sum_primitiveRawEndpointMaximum_eq_meanValueWeight_div
    hqpos

/-- Enlarge rough conductor support to all natural levels above the real
cutoff. -/
theorem sum_conductorRough_invTotient_primitiveRaw_le_interval
    (x Q : ℕ) (Q1 : ℝ) :
    (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
      (q.totient : ℝ)⁻¹ *
        ∑ ψ : primitiveCharacters q,
          primitiveRawEndpointMaximum x q ψ) ≤
      ∑ q ∈ Finset.Ioc ⌊Q1⌋₊ Q,
        (q.totient : ℝ)⁻¹ *
          ∑ ψ : primitiveCharacters q,
            primitiveRawEndpointMaximum x q ψ := by
  rw [← filter_realCutoff_eq_Ioc_natFloor]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hqmem
    rcases Finset.mem_filter.mp hqmem with ⟨hqIoc, hrough⟩
    exact Finset.mem_filter.mpr ⟨hqIoc, roughModulusAbove_lt_level hrough⟩
  · intro q hqmem hqnot
    apply mul_nonneg
    · positivity
    · exact sum_primitiveRawEndpointMaximum_nonneg x q

/-- Compose support enlargement with the exact source normalization. -/
theorem sum_conductorRough_invTotient_primitiveRaw_le_meanValueInterval
    (x Q : ℕ) (Q1 : ℝ) :
    (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
      (q.totient : ℝ)⁻¹ *
        ∑ ψ : primitiveCharacters q,
          primitiveRawEndpointMaximum x q ψ) ≤
      ∑ q ∈ Finset.Ioc ⌊Q1⌋₊ Q,
        primitiveRawMeanValueWeight x q / (q : ℝ) := by
  exact (sum_conductorRough_invTotient_primitiveRaw_le_interval
    x Q Q1).trans_eq
      (sum_interval_invTotient_primitiveRaw_eq_meanValueWeight_div x Q Q1)

/-- Source-facing finite reduction: the original centered all-character sum
is bounded by `5 * log x` times the normalized interval sum. -/
theorem sum_weightedInducingPrimitiveCenteredEndpointMaximum_le_five_log_meanValueInterval
    (x Q : ℕ) (Q1 : ℝ) (hx : 4 ≤ x)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
      (q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          inducingPrimitiveCenteredEndpointMaximum x q χ) ≤
      (5 * Real.log (x : ℝ)) *
        ∑ q ∈ Finset.Ioc ⌊Q1⌋₊ Q,
          primitiveRawMeanValueWeight x q / (q : ℝ) := by
  apply (sum_weightedInducingPrimitiveCenteredEndpointMaximum_le_five_log_raw
    x Q Q1 hx hQsqrt).trans
  apply mul_le_mul_of_nonneg_left
  · exact sum_conductorRough_invTotient_primitiveRaw_le_meanValueInterval
      x Q Q1
  · apply mul_nonneg
    · norm_num
    · apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ x by omega)

end

end BoundedGaps.Maynard
