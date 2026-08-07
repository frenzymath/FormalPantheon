import BoundedGaps.BombieriVinogradov.Analytic.StandardCompatibility
import BoundedGaps.BombieriVinogradov.Analytic.WeightedCenterBridge
import BoundedGaps.BombieriVinogradov.Analytic.CenteredPrimeCountingComposition
import BoundedGaps.BombieriVinogradov.Analytic.WeightedPrimePower
import BoundedGaps.BombieriVinogradov.Analytic.WeightedCutoff
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Conditional weighted-to-prime level adapter

This module consumes the public weighted Bombieri--Vinogradov proposition at
the target exponent `A + 1`.  The target cutoff itself supplies the nonnegative
modulus-one summand used to recenter the estimate.  It deliberately has no
dependency on a closed weighted theorem, the PNT-prefix adapter, or the old
prime-level consumer.
-/

namespace BoundedGaps.BombieriVinogradov

open scoped BigOperators

noncomputable section

private theorem one_le_log_natCast_of_four_le {x : Nat} (hx : 4 <= x) :
    1 <= Real.log (x : Real) := by
  have hlogTwo : (2 / 3 : Real) < Real.log 2 := by
    convert Real.lt_log_one_add_of_pos (x := (1 : Real)) (by norm_num) using 1 <;>
      norm_num
  have hlogFour : (4 / 3 : Real) < Real.log 4 := by
    calc
      (4 / 3 : Real) = 2 * (2 / 3) := by ring
      _ < 2 * Real.log 2 := by nlinarith
      _ = Real.log 4 := by
        rw [show (4 : Real) = 2 * 2 by norm_num,
          Real.log_mul (by norm_num) (by norm_num)]
        ring
  have hstrict : (1 : Real) < Real.log (x : Real) := by
    calc
      (1 : Real) <= 4 / 3 := by norm_num
      _ < Real.log 4 := hlogFour
      _ <= Real.log (x : Real) := by
        apply Real.log_le_log (by norm_num)
        exact_mod_cast hx
  exact hstrict.le

/-- The weighted window implies Maynard's prime level at every fixed positive
level strictly below one half. -/
theorem hasPrimeLevel_of_weightedBombieriVinogradov
    (hBV : weightedBombieriVinogradov) {theta : Real}
    (htheta0 : 0 < theta) (htheta : theta < 1 / 2) :
    BoundedGaps.Maynard.hasPrimeLevel theta := by
  intro A hA
  obtain ⟨B, hB, Cw, hCw, Xw, hXw, hwindow⟩ :=
    (weightedBombieriVinogradov_iff_maynard.mp hBV) (A + 1) (by linarith)
  obtain ⟨Kp, hKp, hKbound⟩ :=
    exists_primePowerRemainder_mul_cutoff_le_weightedWindow
  obtain ⟨Xcut, hXcut, hcut⟩ :=
    exists_modulusCutoff_le_weightedWindow theta B htheta
  let X0 : Nat := max 3 (max Xw Xcut)
  refine ⟨(Real.log 2)⁻¹ * (6 * Cw + Kp), ?_, X0, ?_, ?_⟩
  · have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
    positivity
  · dsimp [X0]
    omega
  · intro x hx
    have hxw : Xw ≤ x := by
      dsimp [X0] at hx
      omega
    have hxc : Xcut ≤ x := by
      dsimp [X0] at hx
      omega
    have hx4 : 4 ≤ x := by
      have : 3 ≤ x := by
        dsimp [X0] at hx
        omega
      omega
    have hx2 : 2 ≤ x := by omega
    have hQone : 1 ≤ BoundedGaps.Maynard.modulusCutoff theta x :=
      one_le_modulusCutoff htheta0.le (by omega)
    let Q : Nat := BoundedGaps.Maynard.modulusCutoff theta x
    have hQone' : 1 ≤ Q := by simpa [Q] using hQone
    have hQwindow : (Q : Real) <= Real.sqrt (x : Real) /
        (Real.log (x : Real)) ^ B := by
      simpa [Q] using hcut x hxc
    have hsumM :
        (∑ q ∈ Finset.Icc 1 Q,
          BoundedGaps.Maynard.maxWeightedProgressionDiscrepancyUpTo x q) <=
          Cw * (x : Real) /
            Real.rpow (Real.log (x : Real)) (A + 1) := by
      exact hwindow x hxw Q hQone' hQwindow
    have hsumW :
        (∑ q ∈ Finset.Icc 1 Q,
          maxWeightedProgressionDiscrepancyUpTo x q) <=
          Cw * (x : Real) /
            Real.rpow (Real.log (x : Real)) (A + 1) := by
      calc
        (∑ q ∈ Finset.Icc 1 Q,
            maxWeightedProgressionDiscrepancyUpTo x q) =
            ∑ q ∈ Finset.Icc 1 Q,
              BoundedGaps.Maynard.maxWeightedProgressionDiscrepancyUpTo x q := by
          apply Finset.sum_congr rfl
          intro q hq
          exact maxWeightedProgressionDiscrepancyUpTo_eq_maynard x q
        _ <= _ := hsumM
    have hglobal :
        maxWeightedProgressionDiscrepancyUpTo x 1 <=
          Cw * (x : Real) /
            Real.rpow (Real.log (x : Real)) (A + 1) :=
      (maxWeightedProgressionDiscrepancyUpTo_one_le_sum hQone').trans hsumW
    have hlogOne : 1 <= Real.log (x : Real) :=
      one_le_log_natCast_of_four_le hx4
    have hlogPos : 0 < Real.log (x : Real) :=
      zero_lt_one.trans_le hlogOne
    have hQsqrt : (Q : Real) <= Real.sqrt (x : Real) := by
      apply hQwindow.trans
      apply div_le_self (Real.sqrt_nonneg _)
      have hpow : (1 : Real) <= (Real.log (x : Real)) ^ B := by
        exact one_le_pow₀ hlogOne
      exact hpow
    have hprefix :
        BoundedGaps.Maynard.reciprocalTotientPrefix Q <
          5 * Real.log (x : Real) :=
      reciprocalTotientPrefix_lt_five_mul_log_of_le_sqrt hx4
        (by omega) hQsqrt
    have hcentered :
        (∑ q ∈ Finset.Icc 1 Q,
          BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo x q) <=
          6 * Cw * (x : Real) /
            Real.rpow (Real.log (x : Real)) A := by
      have hsumAdd :=
        sum_maxCenteredProgressionDiscrepancyUpTo_le_weighted_add_global
          (x := x) (Q := Q) hx2
      have hglobalNonneg :
          0 <= maxWeightedProgressionDiscrepancyUpTo x 1 :=
        maxWeightedProgressionDiscrepancyUpTo_nonneg x 1
      have hsumBound :
          (∑ q ∈ Finset.Icc 1 Q,
            maxWeightedProgressionDiscrepancyUpTo x q) <=
            Cw * (x : Real) /
              Real.rpow (Real.log (x : Real)) A := by
        have hpow :
            Real.rpow (Real.log (x : Real)) A <=
              Real.rpow (Real.log (x : Real)) (A + 1) :=
          Real.rpow_le_rpow_of_exponent_le hlogOne (by linarith)
        exact hsumW.trans
          (div_le_div_of_nonneg_left (mul_nonneg hCw (by positivity))
            (Real.rpow_pos_of_pos hlogPos _) hpow)
      have hglobalBound :
          BoundedGaps.Maynard.reciprocalTotientPrefix Q *
              maxWeightedProgressionDiscrepancyUpTo x 1 <=
            5 * Cw * (x : Real) /
              Real.rpow (Real.log (x : Real)) A := by
        have hmul := mul_le_mul hprefix.le hglobal hglobalNonneg (by positivity)
        calc
          BoundedGaps.Maynard.reciprocalTotientPrefix Q *
                maxWeightedProgressionDiscrepancyUpTo x 1 <=
              (5 * Real.log (x : Real)) *
                (Cw * (x : Real) /
                  Real.rpow (Real.log (x : Real)) (A + 1)) := hmul
          _ = 5 * Cw * (x : Real) /
              Real.rpow (Real.log (x : Real)) A := by
            have hpowAdd :
                Real.rpow (Real.log (x : Real)) (A + 1) =
                  Real.rpow (Real.log (x : Real)) A * Real.log (x : Real) := by
              change (Real.log (x : Real)) ^ (A + 1) =
                (Real.log (x : Real)) ^ A * Real.log (x : Real)
              simpa only [Real.rpow_one] using
                (Real.rpow_add hlogPos A (1 : Real))
            rw [hpowAdd]
            field_simp
      apply hsumAdd.trans
      calc
        _ <= Cw * (x : Real) /
              Real.rpow (Real.log (x : Real)) A +
            5 * Cw * (x : Real) /
              Real.rpow (Real.log (x : Real)) A :=
          add_le_add hsumBound hglobalBound
        _ = 6 * Cw * (x : Real) /
            Real.rpow (Real.log (x : Real)) A := by ring
    have hQprimePower :
        (Q : Real) * (Chebyshev.psi (x : Real) - Chebyshev.theta (x : Real)) <=
          Kp * (x : Real) /
            Real.rpow (Real.log (x : Real)) A := by
      have hnat := hKbound B x Q hx2 hQwindow
      have hAB : A <= (B : Real) := by linarith
      have hpow :
          Real.rpow (Real.log (x : Real)) A <=
            Real.rpow (Real.log (x : Real)) (B : Real) :=
        Real.rpow_le_rpow_of_exponent_le hlogOne hAB
      have hpow' :
          (Real.log (x : Real)) ^ B =
            Real.rpow (Real.log (x : Real)) (B : Real) := by
        exact (Real.rpow_natCast (Real.log (x : Real)) B).symm
      rw [hpow'] at hnat
      exact hnat.trans
        (div_le_div_of_nonneg_left (mul_nonneg hKp (by positivity))
          (Real.rpow_pos_of_pos hlogPos _) hpow)
    calc
      (∑ q ∈ Finset.Icc 1 Q,
          BoundedGaps.Maynard.maxProgressionDiscrepancy x q) <=
          (Real.log 2)⁻¹ *
            ((∑ q ∈ Finset.Icc 1 Q,
                BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo x q) +
              (Q : Real) *
                (Chebyshev.psi (x : Real) - Chebyshev.theta (x : Real))) :=
        BoundedGaps.Maynard.sum_maxProgressionDiscrepancy_le_inv_log_two_mul_centeredPsiPrimePowerEnvelope
          hx2
      _ <= (Real.log 2)⁻¹ *
          ((6 * Cw + Kp) * (x : Real) /
            Real.rpow (Real.log (x : Real)) A) := by
        apply mul_le_mul_of_nonneg_left _
          ((inv_pos.mpr (Real.log_pos (by norm_num))).le)
        calc
          (∑ q ∈ Finset.Icc 1 Q,
              BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo x q) +
              (Q : Real) *
                (Chebyshev.psi (x : Real) - Chebyshev.theta (x : Real)) <=
            6 * Cw * (x : Real) /
                Real.rpow (Real.log (x : Real)) A +
              Kp * (x : Real) /
                Real.rpow (Real.log (x : Real)) A :=
            add_le_add hcentered hQprimePower
          _ = (6 * Cw + Kp) * (x : Real) /
              Real.rpow (Real.log (x : Real)) A := by ring
      _ = (Real.log 2)⁻¹ * (6 * Cw + Kp) * (x : Real) /
          Real.rpow (Real.log (x : Real)) A := by ring

end

end BoundedGaps.BombieriVinogradov
