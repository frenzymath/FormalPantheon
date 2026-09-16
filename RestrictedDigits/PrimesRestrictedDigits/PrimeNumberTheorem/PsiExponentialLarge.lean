import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaPerronOptimizedError
import PrimesRestrictedDigits.BasicEstimates.PrimeRemainderDecay

/-!
# A direct large-cutoff exponential remainder for `Chebyshev.psi`

The optimized Perron height gives a logarithmic-square error first.  This
file performs the elementary exponential absorption with an explicit direct
cutoff, preserving the coefficient needed by the later PNT bridge.
-/

namespace PrimesRestrictedDigits

theorem exists_abs_psi_sub_self_le_exp_large :
    ∃ c K L0 : Real,
      IsRiemannZetaZeroFreeConstant c ∧ 0 < K ∧
      Real.log 4 ≤ L0 ∧
      ∀ x : Real, Real.exp L0 ≤ x ->
        |Chebyshev.psi x - x| <=
          (24576 * K / c ^ 2) * x /
            Real.exp ((Real.sqrt (c / 8) / 2) *
              Real.sqrt (Real.log x)) := by
  obtain ⟨c, K, hc, hK, hError⟩ :=
    exists_abs_psi_sub_self_le_log_sq_div_zetaPerronHeight
  let L0 : Real := max (Real.log 4) (zetaPerronLogThreshold c)
  refine ⟨c, K, L0, hc, hK, ?_, ?_⟩
  · exact le_max_left _ _
  · intro x hxCutoff
    have hxPos : 0 < x := by
      have hL0One : 1 ≤ L0 :=
        (one_le_zetaPerronLogThreshold c).trans (le_max_right _ _)
      have hExpOne : 1 ≤ Real.exp L0 :=
        Real.one_le_exp (by linarith)
      exact lt_of_lt_of_le (zero_lt_one.trans_le hExpOne) hxCutoff
    have hL0Log : L0 ≤ Real.log x :=
      (Real.le_log_iff_exp_le hxPos).2 hxCutoff
    have hxFour : 4 ≤ x := by
      calc
        (4 : Real) = Real.exp (Real.log 4) :=
          (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp L0 :=
          Real.exp_le_exp.mpr (le_max_left _ _)
        _ ≤ x := hxCutoff
    have hThreshold : zetaPerronLogThreshold c ≤ Real.log x :=
      (le_max_right (Real.log 4) (zetaPerronLogThreshold c)).trans hL0Log
    have hHeight :
        zetaPerronHeight c x =
          Real.exp (2 * zetaPerronDecay c * Real.sqrt (Real.log x)) :=
      zetaPerronHeight_eq_exp_two_mul_decay_sqrt_log
        (le_trans (by norm_num) hxFour)
    have hErrorX := hError x hxFour hThreshold
    have hDecayPos : 0 < zetaPerronDecay c :=
      zetaPerronDecay_pos hc.1
    have hScale := log_sq_le_exp_sqrt_log_scale
      (c := zetaPerronDecay c) (x := x) hDecayPos
      (le_trans (by norm_num) hxFour)
    have hDecayFourth : zetaPerronDecay c ^ 4 = c ^ 2 / 1024 := by
      have hsqrt : (Real.sqrt (c / 8)) ^ 2 = c / 8 := by
        exact Real.sq_sqrt (div_nonneg hc.1.le (by norm_num))
      dsimp [zetaPerronDecay]
      calc
        (Real.sqrt (c / 8) / 2) ^ 4 =
            (Real.sqrt (c / 8)) ^ 4 / 16 := by ring
        _ = ((Real.sqrt (c / 8)) ^ 2) ^ 2 / 16 := by ring
        _ = (c / 8) ^ 2 / 16 := by rw [hsqrt]
        _ = c ^ 2 / 1024 := by ring
    have hTPos : 0 < zetaPerronHeight c x :=
      Real.exp_pos _
    have hFactorNonneg : 0 ≤ K * x / zetaPerronHeight c x := by
      positivity
    have hScaled :=
      mul_le_mul_of_nonneg_left hScale hFactorNonneg
    have hAbsScaled :
        |Chebyshev.psi x - x| <=
          (K * x / zetaPerronHeight c x) *
            (24 / zetaPerronDecay c ^ 4 *
              Real.exp (zetaPerronDecay c * Real.sqrt (Real.log x))) := by
      calc
        |Chebyshev.psi x - x| <=
            K * x * Real.log x ^ 2 / zetaPerronHeight c x := hErrorX
        _ = (K * x / zetaPerronHeight c x) * Real.log x ^ 2 := by ring
        _ <= (K * x / zetaPerronHeight c x) *
            (24 / zetaPerronDecay c ^ 4 *
              Real.exp (zetaPerronDecay c * Real.sqrt (Real.log x))) := hScaled
    calc
      |Chebyshev.psi x - x| <=
          (K * x / zetaPerronHeight c x) *
            (24 / zetaPerronDecay c ^ 4 *
              Real.exp (zetaPerronDecay c * Real.sqrt (Real.log x))) := hAbsScaled
      _ = (24576 * K / c ^ 2) * x /
          Real.exp ((Real.sqrt (c / 8) / 2) *
            Real.sqrt (Real.log x)) := by
        rw [hHeight, hDecayFourth]
        have hExpNe : Real.exp
            (zetaPerronDecay c * Real.sqrt (Real.log x)) ≠ 0 :=
          (Real.exp_ne_zero _)
        field_simp [hExpNe, hc.1.ne']
        have hExpCombine :
            Real.exp (zetaPerronDecay c * Real.sqrt (Real.log x)) *
                Real.exp (Real.sqrt (Real.log x) * Real.sqrt (c / 8) / 2) =
              Real.exp (2 * zetaPerronDecay c * Real.sqrt (Real.log x)) := by
          rw [← Real.exp_add]
          congr 1
          dsimp [zetaPerronDecay]
          ring
        calc
          24 * 1024 * Real.exp (zetaPerronDecay c * Real.sqrt (Real.log x)) *
              Real.exp (Real.sqrt (Real.log x) * Real.sqrt (c / 8) / 2) =
            24576 *
              (Real.exp (zetaPerronDecay c * Real.sqrt (Real.log x)) *
                Real.exp (Real.sqrt (Real.log x) * Real.sqrt (c / 8) / 2)) := by ring
          _ = 24576 * Real.exp
              (2 * zetaPerronDecay c * Real.sqrt (Real.log x)) := by
            rw [hExpCombine]
          _ = Real.exp (2 * zetaPerronDecay c * Real.sqrt (Real.log x)) *
              24576 := by ring

end PrimesRestrictedDigits
