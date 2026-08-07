import BoundedGaps.BombieriVinogradov.Analytic.VaughanFourthTermDyadic

/-!
# Scale count for Vaughan's fourth term

This file proves the dyadic scale count used in Akbary--Hambrook's treatment
of the fourth Vaughan term.  The source logarithm is totalized by taking its
maximum with zero; this is necessary when `V >= 2 * x`.

Source: `AkbaryHambrook2013v2`, Section 6, pp. 22--23. Semantic review:
`SEM-458`.
-/

namespace BoundedGaps.Maynard

noncomputable section

/-- The nonnegative totalization of the source's fourth-term scale logarithm
`log (2x / V)`. -/
noncomputable def vaughanFourthScaleLog (V : ℝ) (x : ℕ) : ℝ :=
  max 0 (Real.log (2 * (x : ℝ) / V))

theorem vaughanFourthScaleLog_nonneg (V : ℝ) (x : ℕ) :
    0 ≤ vaughanFourthScaleLog V x :=
  le_max_left _ _

/-- The number of active fourth-term scales is at most the totalized source
scale logarithm divided by `log 2`. -/
theorem card_vaughanFourthDyadicExponents_le_scaleLog
    {U V : ℝ} (hV : 1 ≤ V) (x : ℕ) :
    ((vaughanFourthDyadicExponents U V x).card : ℝ) ≤
      vaughanFourthScaleLog V x / Real.log 2 := by
  have hVpos : 0 < V := zero_lt_one.trans_le hV
  have hquotNonneg : 0 ≤ (x : ℝ) / V :=
    div_nonneg (Nat.cast_nonneg x) hVpos.le
  by_cases hfloorZero : ⌊(x : ℝ) / V⌋₊ = 0
  · have hempty : vaughanFourthDyadicExponents U V x = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro alpha halpha
      rcases Finset.mem_filter.mp halpha with ⟨_halphaRange, halphaBounds⟩
      dsimp only at halphaBounds
      have hMfloor : 2 ^ alpha ≤ ⌊(x : ℝ) / V⌋₊ :=
        Nat.le_floor halphaBounds.2.le
      rw [hfloorZero] at hMfloor
      have hMpos : 0 < 2 ^ alpha := by positivity
      omega
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (vaughanFourthScaleLog_nonneg V x)
      (Real.log_pos (by norm_num)).le
  · have hfloorPos : 0 < ⌊(x : ℝ) / V⌋₊ :=
      Nat.pos_of_ne_zero hfloorZero
    have hfloorLe : ((⌊(x : ℝ) / V⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) / V :=
      Nat.floor_le hquotNonneg
    have htwiceFloorLe :
        2 * ((⌊(x : ℝ) / V⌋₊ : ℕ) : ℝ) ≤ 2 * (x : ℝ) / V := by
      calc
        2 * ((⌊(x : ℝ) / V⌋₊ : ℕ) : ℝ) ≤
            2 * ((x : ℝ) / V) :=
          mul_le_mul_of_nonneg_left hfloorLe (by norm_num)
        _ = 2 * (x : ℝ) / V := by ring
    calc
      ((vaughanFourthDyadicExponents U V x).card : ℝ) ≤
          ((dyadicExponentRange ⌊(x : ℝ) / V⌋₊).card : ℝ) := by
        rw [vaughanFourthDyadicExponents]
        exact_mod_cast Finset.card_filter_le
          (dyadicExponentRange ⌊(x : ℝ) / V⌋₊) _
      _ ≤ Real.log (2 * ((⌊(x : ℝ) / V⌋₊ : ℕ) : ℝ)) /
          Real.log 2 :=
        card_dyadicExponentRange_le_log hfloorPos
      _ ≤ Real.log (2 * (x : ℝ) / V) / Real.log 2 := by
        apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
        exact Real.log_le_log (by positivity) htwiceFloorLe
      _ ≤ vaughanFourthScaleLog V x / Real.log 2 := by
        apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
        exact le_max_right _ _

end

end BoundedGaps.Maynard
