import PrimesRestrictedDigits.SieveAsymptotics.DecimalIwaniecWeightedDensity
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserFirstIntegral

/-!
# The first weighted dimension-one Rosser recurrence term

This file applies Iwaniec's weighted density estimate to the first transformed weights and
evaluates the resulting integral exactly. See `IWANIEC-ROSSER-SIEVE-1980`, Section 8, Eqs.
(8.8)--(8.9).
-/

open Finset MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The first weighted prime sum for an upper target of positive rank `R`. -/
noncomputable def dimensionOneRosserPlusFirstPrimeSum
    (P : Finset Nat) (level s0 z : Real) (R : Nat) : Real :=
  ∑ p ∈ P.filter (fun p : Nat =>
      level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
    (p : Real)⁻¹ *
      sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
      (Real.log (p : Real) / Real.log (level / (p : Real))) *
      dimensionOneRosserModelMinusPartialSum R
        (buchstabArgument level (p : Real))

/-- The first weighted prime sum for a lower target of rank `R+1`. -/
noncomputable def dimensionOneRosserMinusFirstPrimeSum
    (P : Finset Nat) (level s0 z : Real) (R : Nat) : Real :=
  ∑ p ∈ P.filter (fun p : Nat =>
      level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
    (p : Real)⁻¹ *
      sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
      (Real.log (p : Real) / Real.log (level / (p : Real))) *
      dimensionOneRosserModelPlusPartialSum R
        (buchstabArgument level (p : Real))

private theorem dimensionOneRosserFirst_log_data
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hss0 : s < s0) :
    Real.log z = Real.log level / s ∧
      Real.log (level / z) = Real.log level * (1 - 1 / s) ∧
      buchstabArgument level z = s - 1 ∧
      Real.log (level ^ (1 / s0)) = Real.log level / s0 := by
  have hlevelPos : 0 < level := by linarith
  have hzPos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hsPos : 0 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hL : Real.log level = s * Real.log z := by
    rw [hs]
    field_simp
  have hlogzEq : Real.log z = Real.log level / s := by
    rw [hL]
    field_simp
  have hlogDiv :
      Real.log (level / z) = Real.log level * (1 - 1 / s) := by
    rw [Real.log_div hlevelPos.ne' hzPos.ne', hlogzEq]
    ring
  exact ⟨hlogzEq, hlogDiv,
    buchstabArgument_eq_sub_one_of_log_ratio hs,
    log_rpow_one_div hlevelPos⟩

private theorem dimensionOneRosserPlusFirstPrimeSum_eq_scaled
    (P : Finset Nat) {level s0 z : Real} (R : Nat)
    (hprime : ∀ p ∈ P, p.Prime) (hz : 2 <= z) :
    dimensionOneRosserPlusFirstPrimeSum P level s0 z R =
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z * Real.log z) *
        (∑ p ∈ P.filter (fun p : Nat =>
            level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
          (p : Real)⁻¹ *
            (sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
              sieveDensityBelow P (fun q => (q : Real)⁻¹) z) *
            (Real.log (p : Real) / Real.log z) *
            dimensionOneRosserPlusFirstWeight R level (p : Real)) := by
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  rw [Finset.mul_sum]
  unfold dimensionOneRosserPlusFirstPrimeSum
  apply Finset.sum_congr rfl
  intro p hp
  unfold dimensionOneRosserPlusFirstWeight
  field_simp [hV.ne', hlogz.ne']

private theorem dimensionOneRosserMinusFirstPrimeSum_eq_scaled
    (P : Finset Nat) {level s0 z : Real} (R : Nat)
    (hprime : ∀ p ∈ P, p.Prime) (hz : 2 <= z) :
    dimensionOneRosserMinusFirstPrimeSum P level s0 z R =
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z * Real.log z) *
        (∑ p ∈ P.filter (fun p : Nat =>
            level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
          (p : Real)⁻¹ *
            (sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
              sieveDensityBelow P (fun q => (q : Real)⁻¹) z) *
            (Real.log (p : Real) / Real.log z) *
            dimensionOneRosserMinusFirstWeight R level (p : Real)) := by
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  rw [Finset.mul_sum]
  unfold dimensionOneRosserMinusFirstPrimeSum
  apply Finset.sum_congr rfl
  intro p hp
  unfold dimensionOneRosserMinusFirstWeight
  field_simp [hV.ne', hlogz.ne']

/-- The explicit-`K` estimate for the first upper-target recurrence term.
The rank hypothesis separates this induction step from the rank-zero base. -/
theorem dimensionOneRosserPlusFirstPrimeSum_le_of_ratio
    (P : Finset Nat) {K level z s s0 : Real} (R : Nat)
    (_hR : 0 < R) (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hRatio : ∀ u : Real, level ^ (1 / s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u)) :
    dimensionOneRosserPlusFirstPrimeSum P level s0 z R <=
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (dimensionOneRosserModelPlusPartialSum R s -
          dimensionOneRosserModelPlusPartialSum R s0 +
          (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
            dimensionOneRosserModelMinusPartialSum R (s - 1)) := by
  have hlogs := dimensionOneRosserFirst_log_data
    hlevel hz hs (by linarith) hss0
  rcases hlogs with ⟨hlogzEq, hlogDiv, hargz, hlogCutoff⟩
  have hlogLevel : 0 < Real.log level := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hsPos : 0 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hOne : 0 < 1 - 1 / s := by
    rw [sub_pos, div_lt_one hsPos]
    linarith
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hcutoffz : level ^ (1 / s0) < z :=
    dimensionOneRosserFirstCutoff_lt hlevel hz hs hss0 (by linarith)
  rcases dimensionOneRosserPlusFirstWeight_properties R hlevel hz hs hss0
      hcutoff hsLower with ⟨hB0, hBcont, hBmono⟩
  have hWeighted := iwaniecWeightedDensitySum_le_of_ratio
    P (dimensionOneRosserPlusFirstWeight R level) hK hprime hcutoff
      hcutoffz hRatio hBcont hBmono hB0
  have hScaled := mul_le_mul_of_nonneg_left hWeighted
    (mul_nonneg hV.le hlogz.le)
  rw [<- dimensionOneRosserPlusFirstPrimeSum_eq_scaled P R hprime hz]
    at hScaled
  have hIntegralMul :
      Real.log level *
          (∫ x in (level ^ (1 / s0))..z,
            dimensionOneRosserPlusFirstWeight R level x /
              (x * Real.log x)) =
        dimensionOneRosserModelPlusPartialSum R s -
          dimensionOneRosserModelPlusPartialSum R s0 := by
    rw [log_mul_integral_dimensionOneRosserPlusFirstWeight_eq
      R hlevel hz hs hss0 hsLower]
    exact integral_dimensionOneRosserModelMinusPartialSum_div_eq
      R hsLower hss0.le
  have hIntegral :
      (∫ x in (level ^ (1 / s0))..z,
        dimensionOneRosserPlusFirstWeight R level x /
          (x * Real.log x)) =
        (dimensionOneRosserModelPlusPartialSum R s -
          dimensionOneRosserModelPlusPartialSum R s0) / Real.log level := by
    apply (eq_div_iff hlogLevel.ne').2
    simpa only [mul_comm] using hIntegralMul
  have hBz : dimensionOneRosserPlusFirstWeight R level z =
      dimensionOneRosserModelMinusPartialSum R (s - 1) /
        (Real.log level * (1 - 1 / s)) := by
    unfold dimensionOneRosserPlusFirstWeight
    rw [hargz, hlogDiv]
  rw [hIntegral, hBz, hlogCutoff] at hScaled
  calc
    dimensionOneRosserPlusFirstPrimeSum P level s0 z R <=
        (sieveDensityBelow P (fun q => (q : Real)⁻¹) z * Real.log z) *
          ((dimensionOneRosserModelPlusPartialSum R s -
              dimensionOneRosserModelPlusPartialSum R s0) /
                Real.log level +
            2 * K *
                (dimensionOneRosserModelMinusPartialSum R (s - 1) /
                  (Real.log level * (1 - 1 / s))) /
              (Real.log level / s0)) := hScaled
    _ = _ := by
      rw [hlogzEq]
      field_simp [hlogLevel.ne', hsPos.ne', hs0Pos.ne', hOne.ne']

/-- The explicit-`K` estimate for the first lower-target recurrence term,
indexed by its upper predecessor rank `R`. -/
theorem dimensionOneRosserMinusFirstPrimeSum_le_of_ratio
    (P : Finset Nat) {K level z s s0 : Real} (R : Nat)
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hRatio : ∀ u : Real, level ^ (1 / s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u)) :
    dimensionOneRosserMinusFirstPrimeSum P level s0 z R <=
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (dimensionOneRosserModelMinusPartialSum (R + 1) s -
          dimensionOneRosserModelMinusPartialSum (R + 1) s0 +
          (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
            dimensionOneRosserModelPlusPartialSum R (s - 1)) := by
  have hlogs := dimensionOneRosserFirst_log_data
    hlevel hz hs hsLower hss0
  rcases hlogs with ⟨hlogzEq, hlogDiv, hargz, hlogCutoff⟩
  have hlogLevel : 0 < Real.log level := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hsPos : 0 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hOne : 0 < 1 - 1 / s := by
    rw [sub_pos, div_lt_one hsPos]
    linarith
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hcutoffz : level ^ (1 / s0) < z :=
    dimensionOneRosserFirstCutoff_lt hlevel hz hs hss0 hsLower
  rcases dimensionOneRosserMinusFirstWeight_properties R hlevel hz hs hss0
      hcutoff hsLower with ⟨hB0, hBcont, hBmono⟩
  have hWeighted := iwaniecWeightedDensitySum_le_of_ratio
    P (dimensionOneRosserMinusFirstWeight R level) hK hprime hcutoff
      hcutoffz hRatio hBcont hBmono hB0
  have hScaled := mul_le_mul_of_nonneg_left hWeighted
    (mul_nonneg hV.le hlogz.le)
  rw [<- dimensionOneRosserMinusFirstPrimeSum_eq_scaled P R hprime hz]
    at hScaled
  have hIntegralMul :
      Real.log level *
          (∫ x in (level ^ (1 / s0))..z,
            dimensionOneRosserMinusFirstWeight R level x /
              (x * Real.log x)) =
        dimensionOneRosserModelMinusPartialSum (R + 1) s -
          dimensionOneRosserModelMinusPartialSum (R + 1) s0 := by
    rw [log_mul_integral_dimensionOneRosserMinusFirstWeight_eq
      R hlevel hz hs hss0 hsLower]
    exact integral_dimensionOneRosserModelPlusPartialSum_div_eq
      R hsLower hss0.le
  have hIntegral :
      (∫ x in (level ^ (1 / s0))..z,
        dimensionOneRosserMinusFirstWeight R level x /
          (x * Real.log x)) =
        (dimensionOneRosserModelMinusPartialSum (R + 1) s -
          dimensionOneRosserModelMinusPartialSum (R + 1) s0) /
            Real.log level := by
    apply (eq_div_iff hlogLevel.ne').2
    simpa only [mul_comm] using hIntegralMul
  have hBz : dimensionOneRosserMinusFirstWeight R level z =
      dimensionOneRosserModelPlusPartialSum R (s - 1) /
        (Real.log level * (1 - 1 / s)) := by
    unfold dimensionOneRosserMinusFirstWeight
    rw [hargz, hlogDiv]
  rw [hIntegral, hBz, hlogCutoff] at hScaled
  calc
    dimensionOneRosserMinusFirstPrimeSum P level s0 z R <=
        (sieveDensityBelow P (fun q => (q : Real)⁻¹) z * Real.log z) *
          ((dimensionOneRosserModelMinusPartialSum (R + 1) s -
              dimensionOneRosserModelMinusPartialSum (R + 1) s0) /
                Real.log level +
            2 * K *
                (dimensionOneRosserModelPlusPartialSum R (s - 1) /
                  (Real.log level * (1 - 1 / s))) /
              (Real.log level / s0)) := hScaled
    _ = _ := by
      rw [hlogzEq]
      field_simp [hlogLevel.ne', hsPos.ne', hs0Pos.ne', hOne.ne']

end PrimesRestrictedDigits
