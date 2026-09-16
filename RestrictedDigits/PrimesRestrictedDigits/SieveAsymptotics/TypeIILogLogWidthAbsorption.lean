import PrimesRestrictedDigits.MajorArcs.M2Absorption
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Type II log-log width absorption

The varying Proposition 7.2 width at decimal scales tends to zero. This is the terminal scalar
input for the strict-only Lemma 7.3 transfer.
-/

open Filter

namespace PrimesRestrictedDigits

noncomputable section

/-- Maynard's varying Type II width tends to zero through decimal lengths. -/
theorem tendsto_majorArcM2LogLogDelta_powTen :
    Tendsto (fun length : Nat =>
      majorArcM2LogLogDelta (10 ^ length)) atTop (nhds 0) := by
  let scale : Nat -> Real := fun length => ((10 ^ length : Nat) : Real)
  have hscale : Tendsto scale atTop atTop := by
    simpa only [scale, Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : (1 : Real) < 10))
  have hlog : Tendsto (fun length => Real.log (scale length)) atTop atTop :=
    Real.tendsto_log_atTop.comp hscale
  have hloglog :
      Tendsto (fun length => Real.log (Real.log (scale length)))
        atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  unfold majorArcM2LogLogDelta
  convert hloglog.inv_tendsto_atTop using 1
  ext length
  simp only [scale, Pi.inv_apply]

/-- Every fixed nonnegative multiple of the varying width eventually fits a
positive scalar budget. -/
theorem exists_mul_majorArcM2LogLogDelta_powTen_le
    (C rho : Real) (_hC : 0 <= C) (hrho : 0 < rho) :
    exists length0 : Nat, 1 <= length0 ∧
      forall length : Nat, length0 <= length ->
        C * majorArcM2LogLogDelta (10 ^ length) <= rho := by
  have htendsto :
      Tendsto (fun length : Nat =>
        C * majorArcM2LogLogDelta (10 ^ length)) atTop (nhds 0) := by
    simpa only [mul_zero] using
      tendsto_const_nhds.mul tendsto_majorArcM2LogLogDelta_powTen
  obtain ⟨length1, hlength1⟩ :=
    eventually_atTop.mp (htendsto.eventually_lt_const hrho)
  refine ⟨max 1 length1, le_max_left _ _, ?_⟩
  intro length hlength
  exact (hlength1 length ((le_max_right 1 length1).trans hlength)).le

end

end PrimesRestrictedDigits
