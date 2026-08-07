import BoundedGaps.PrimeNumberTheorem.Analytic.StrongChebyshev
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Chebyshev and prime-counting asymptotics

This file converts the strong natural-endpoint Chebyshev estimate of SEM-579
to the ordinary prime-counting asymptotic. Prime powers are removed with
pinned Mathlib's `psi - theta` bound, and Abel summation is consumed through
Mathlib's prime-counting remainder. Semantic review: `SEM-580`.
-/

namespace BoundedGaps.PrimeNumberTheorem

open Asymptotics Filter
open scoped Asymptotics

noncomputable section

/-- The strong `psi - x` estimate implies `psi(n) ~ n` along natural
endpoints. -/
theorem chebyshevPsi_natCast_isEquivalent :
    (fun n : ℕ => Chebyshev.psi (n : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  obtain ⟨C, c, _hC, hc, X0, _hX0, hpsi⟩ :=
    exists_abs_chebyshevPsi_sub_natCast_le_exp_neg_sqrtLog
  rw [Asymptotics.IsEquivalent]
  refine IsLittleO.of_bound fun epsilon hepsilon => ?_
  have huTop : Tendsto
      (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hnegTop : Tendsto
      (fun n : ℕ => -c * Real.sqrt (Real.log (n : ℝ))) atTop atBot :=
    tendsto_const_nhds.neg_mul_atTop (neg_neg_iff_pos.mpr hc) huTop
  have hdecay : Tendsto
      (fun n : ℕ => C * Real.exp
        (-c * Real.sqrt (Real.log (n : ℝ)))) atTop (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp hnegTop)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      C * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) ≤ epsilon :=
    ((tendsto_order.1 hdecay).2 _ hepsilon).mono fun _ h => h.le
  filter_upwards [eventually_ge_atTop X0, hsmall] with n hn hsmalln
  have hnnonneg : (0 : ℝ) ≤ n := by positivity
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hnnonneg]
  calc
    |Chebyshev.psi (n : ℝ) - (n : ℝ)| ≤
        C * ((n : ℝ) * Real.exp
          (-c * Real.sqrt (Real.log (n : ℝ)))) := hpsi n hn
    _ = (C * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))) * (n : ℝ) := by
      ring
    _ ≤ epsilon * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hsmalln hnnonneg

/-- Removing prime powers preserves the natural-endpoint main term. -/
theorem chebyshevTheta_natCast_isEquivalent :
    (fun n : ℕ => Chebyshev.theta (n : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  have hpsiThetaO :
      (fun n : ℕ =>
        Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ)) =O[atTop]
          (fun n : ℕ => Real.sqrt (n : ℝ)) := by
    simpa [Function.comp_def] using
      Chebyshev.isBigO_psi_sub_theta_sqrt.comp_tendsto
        tendsto_natCast_atTop_atTop
  have hsqrtTop : Tendsto
      (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrtLittle :
      (fun n : ℕ => Real.sqrt (n : ℝ)) =o[atTop]
        (fun n : ℕ => (n : ℝ)) := by
    refine (isLittleO_iff_tendsto' ?_).2 ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn hzero
      have hn0 : (n : ℝ) ≠ 0 := by
        exact_mod_cast (show n ≠ 0 by omega)
      exact (hn0 (by simpa using hzero)).elim
    · refine hsqrtTop.inv_tendsto_atTop.congr' ?_
      exact Eventually.of_forall fun n => Real.sqrt_div_self.symm
  have hpsiThetaLittle := hpsiThetaO.trans_isLittleO hsqrtLittle
  refine (chebyshevPsi_natCast_isEquivalent.sub_isLittleO
    hpsiThetaLittle).congr_left ?_
  exact Eventually.of_forall fun n => by
    simp only [Pi.sub_apply]
    ring

private theorem logSquareScale_isLittleO :
    (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ) ^ 2) =o[atTop]
      (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
  refine (isLittleO_iff_tendsto' ?_).2 ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn hzero
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (show n ≠ 0 by omega)
    have hlog0 : Real.log (n : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
    exact (div_ne_zero hn0 hlog0 hzero).elim
  · have hlogTop : Tendsto
        (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    refine hlogTop.inv_tendsto_atTop.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (show n ≠ 0 by omega)
    have hlog0 : Real.log (n : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
    simp only [Pi.inv_apply]
    field_simp [hn0, hlog0]

/-- Abel summation transfers `theta(n) ~ n` to `pi(n) ~ n / log n`. -/
theorem primeCounting_natCast_isEquivalent :
    (fun n : ℕ => (Nat.primeCounting n : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
  have hthetaDiv :
      (fun n : ℕ =>
        Chebyshev.theta (n : ℝ) / Real.log (n : ℝ)) ~[atTop]
          (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
    let h := chebyshevTheta_natCast_isEquivalent.div
      (IsEquivalent.refl :
        (fun n : ℕ => Real.log (n : ℝ)) ~[atTop]
          (fun n : ℕ => Real.log (n : ℝ)))
    refine (h.congr_left ?_).congr_right ?_
    · exact Eventually.of_forall fun n => by simp only [Pi.div_apply]
    · exact Eventually.of_forall fun n => by simp only [Pi.div_apply]
  have hprimeErrorO :
      (fun n : ℕ =>
        (Nat.primeCounting n : ℝ) -
          Chebyshev.theta (n : ℝ) / Real.log (n : ℝ)) =O[atTop]
            (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ) ^ 2) := by
    simpa [Function.comp_def, Nat.floor_natCast] using
      Chebyshev.primeCounting_sub_theta_div_log_isBigO.comp_tendsto
        tendsto_natCast_atTop_atTop
  have hprimeErrorLittle :=
    hprimeErrorO.trans_isLittleO logSquareScale_isLittleO
  refine (hthetaDiv.add_isLittleO hprimeErrorLittle).congr_left ?_
  exact Eventually.of_forall fun n => by
    simp only [Pi.add_apply]
    ring

end

end BoundedGaps.PrimeNumberTheorem
