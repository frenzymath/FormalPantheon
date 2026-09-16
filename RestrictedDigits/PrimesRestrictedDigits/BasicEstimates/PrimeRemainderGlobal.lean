import PrimesRestrictedDigits.BasicEstimates.LogarithmicIntegral
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Globalizing an eventual prime-counting remainder estimate

This file extends an eventual log-square estimate over the bounded initial
interval by using monotonicity of the prime count and continuity of the
logarithmic integral. No continuity is asserted for the remainder itself.
This is the bounded-range closure implicit in `MONTGOMERY-VAUGHAN-MNT-I`,
Chapter 6, Theorem 6.9.
-/

open Asymptotics Filter Set

namespace PrimesRestrictedDigits

private theorem monotone_realPrimeCounting : Monotone realPrimeCounting := by
  intro x y hxy
  unfold realPrimeCounting
  exact_mod_cast Nat.monotone_primeCounting (Nat.floor_mono hxy)

private theorem one_div_le_pntLogSqScale {x T : Real}
    (hx : 2 ≤ x) (hxT : x ≤ T) :
    1 / T ≤ x / Real.log x ^ 2 := by
  have hxpos : 0 < x := by linarith
  have hTpos : 0 < T := hxpos.trans_le hxT
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogle : Real.log x ≤ x := Real.log_le_self hxpos.le
  apply (div_le_div_iff₀ hTpos (sq_pos_of_pos hlogpos)).2
  have hlogsq : Real.log x ^ 2 ≤ x ^ 2 := by nlinarith
  nlinarith

/-- An eventual log-square prime-counting remainder bound extends over the
bounded initial interval in the source normalization. -/
theorem exists_primeRemainder_log_sq_bound_of_isBigO
    (hR : (fun x : Real => primeRemainder x) =O[atTop]
      (fun x : Real => x / Real.log x ^ 2)) :
    ∃ C : Real, 0 < C ∧ ∀ x : Real, 2 ≤ x →
      |primeRemainder x| ≤ C * x / Real.log x ^ 2 := by
  rcases isBigO_iff'.mp hR with ⟨c, hc, hEventual⟩
  rcases eventually_atTop.mp hEventual with ⟨A, hA⟩
  let T : Real := max 2 A
  have hTtwo : 2 ≤ T := le_max_left _ _
  have hAT : A ≤ T := le_max_right _ _
  have hTpos : 0 < T := by linarith
  have hliCont : ContinuousOn logarithmicIntegral (Set.Icc 2 T) := by
    apply logarithmicIntegral_continuousOn.mono
    intro y hy
    exact lt_of_lt_of_le (by norm_num) hy.1
  rcases isCompact_Icc.exists_bound_of_continuousOn hliCont with ⟨M, hM⟩
  have hMnonneg : 0 ≤ M := by
    exact (norm_nonneg (logarithmicIntegral 2)).trans (hM 2 ⟨le_rfl, hTtwo⟩)
  let B : Real := realPrimeCounting T + M
  have hpiTnonneg : 0 ≤ realPrimeCounting T := by
    unfold realPrimeCounting
    positivity
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg hpiTnonneg hMnonneg
  refine ⟨c + B * T, by positivity, ?_⟩
  intro x hx
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hscaleNonneg : 0 ≤ x / Real.log x ^ 2 := by positivity
  rcases le_total x T with hxT | hTx
  · have hpi : realPrimeCounting x ≤ realPrimeCounting T :=
      monotone_realPrimeCounting hxT
    have hpiNorm : ‖realPrimeCounting x‖ ≤ realPrimeCounting T := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact hpi
      · unfold realPrimeCounting
        positivity
    have hlocal : |primeRemainder x| ≤ B := by
      rw [← Real.norm_eq_abs]
      change ‖realPrimeCounting x - logarithmicIntegral x‖ ≤ B
      calc
        ‖realPrimeCounting x - logarithmicIntegral x‖ ≤
            ‖realPrimeCounting x‖ + ‖logarithmicIntegral x‖ := norm_sub_le _ _
        _ ≤ realPrimeCounting T + M :=
          add_le_add hpiNorm (hM x ⟨hx, hxT⟩)
        _ = B := rfl
    have hscale := one_div_le_pntLogSqScale hx hxT
    have hBscale : B ≤ B * T * (x / Real.log x ^ 2) := by
      calc
        B = B * T * (1 / T) := by field_simp
        _ ≤ B * T * (x / Real.log x ^ 2) :=
          mul_le_mul_of_nonneg_left hscale (mul_nonneg hBnonneg hTpos.le)
    calc
      |primeRemainder x| ≤ B := hlocal
      _ ≤ B * T * (x / Real.log x ^ 2) := hBscale
      _ ≤ (c + B * T) * (x / Real.log x ^ 2) := by
        exact mul_le_mul_of_nonneg_right (by linarith) hscaleNonneg
      _ = (c + B * T) * x / Real.log x ^ 2 := by ring
  · have hLarge := hA x (hAT.trans hTx)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hscaleNonneg] at hLarge
    calc
      |primeRemainder x| ≤ c * (x / Real.log x ^ 2) := hLarge
      _ ≤ (c + B * T) * (x / Real.log x ^ 2) := by
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (mul_nonneg hBnonneg hTpos.le)) hscaleNonneg
      _ = (c + B * T) * x / Real.log x ^ 2 := by ring

end PrimesRestrictedDigits
