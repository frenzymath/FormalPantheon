import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceHighIntegral
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayLowerScaleErrorThreshold

/-!
# Source-cutoff epsilon-zero slope margin

The literal source cutoff is handled here without the incompatible old cap.
-/

open Set

namespace PrimesRestrictedDigits

theorem dimensionOneRosserSourceCutoffSlopeMargin
    {L s s0 t : Real} (hL : Real.exp 1 <= L)
    (hs : Real.exp 5000 + 1 <= s) (_hss0 : s < s0)
    (hcutoff : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L)
    (ht : t ∈ Icc s s0) :
    48 * dimensionOneRosserArtificialSlope L 0 t <=
      (1 - (dimensionOneRosserArtificialBase L 0 t)⁻¹) * Real.log t := by
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hL
  have hLlog : 1 <= Real.log L :=
    (Real.le_log_iff_exp_le hLPos).2 hL
  have hLlogPos : 0 < Real.log L := by linarith
  have hsPos : 0 < s := by nlinarith [Real.exp_pos (5000 : Real)]
  have htPos : 0 < t := hsPos.trans_le ht.1
  let a : Real := t ^ 50 / L
  have ha : 0 < a := div_pos (pow_pos htPos 50) hLPos
  have hbase : dimensionOneRosserArtificialBase L 0 t = 1 + a := by
    simp [dimensionOneRosserArtificialBase, a]
  have hpowRatio : a <= (Real.log L) ^ 3 := by
    calc
      a = t ^ 50 / L := rfl
      _ <= s0 ^ 50 / L :=
        (div_le_div_iff_of_pos_right hLPos).2
          (pow_le_pow_left₀ htPos.le ht.2 50)
      _ = (Real.log L) ^ 3 := by rw [hcutoff]; field_simp
  have hlogTwo : Real.log 2 <= 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
      using 1; norm_num
  have hlogtLarge : 5000 < Real.log t :=
    dimensionOneRosser_log_gt_fiveThousand hs ht.1
  have hbaseFrac : 1 - (dimensionOneRosserArtificialBase L 0 t)⁻¹ =
      a / (1 + a) := by
    rw [hbase]
    field_simp
    ring
  by_cases haOne : a <= 1
  · have hslope : dimensionOneRosserArtificialSlope L 0 t <= 51 * a :=
      dimensionOneRosserArtificialSlope_zero_le hLPos htPos
    have hfracLower : a / 2 <= a / (1 + a) := by
      have hOnePos : 0 < 1 + a := by linarith
      have hinv : 1 / (2 : Real) <= 1 / (1 + a) :=
        one_div_le_one_div_of_le hOnePos (by linarith [haOne])
      calc
        a / 2 = a * (1 / 2) := by ring
        _ <= a * (1 / (1 + a)) :=
          mul_le_mul_of_nonneg_left hinv ha.le
        _ = a / (1 + a) := by ring
    rw [hbaseFrac]
    have hleft : 48 * dimensionOneRosserArtificialSlope L 0 t <= 2448 * a := by
      calc
        48 * dimensionOneRosserArtificialSlope L 0 t <= 48 * (51 * a) :=
          mul_le_mul_of_nonneg_left hslope (by norm_num)
        _ = 2448 * a := by ring
    nlinarith
  · have haLower : 1 <= a := le_of_not_ge haOne
    have hLle : L <= t ^ 50 := by
      rw [le_div_iff₀ hLPos] at haLower
      simpa using haLower
    have hlogHigh : Real.log L / 50 <= Real.log t := by
      have h := Real.log_le_log hLPos hLle
      rw [Real.log_pow] at h
      norm_num at h ⊢
      linarith
    have hlogBase : Real.log (dimensionOneRosserArtificialBase L 0 t) <=
        Real.log 2 + 3 * Real.log (Real.log L) := by
      have hlogLpow : 1 <= (Real.log L) ^ 3 := one_le_pow₀ hLlog
      have hbaseUpper : dimensionOneRosserArtificialBase L 0 t <=
          2 * (Real.log L) ^ 3 := by
        rw [hbase]
        nlinarith [hpowRatio]
      calc
        Real.log (dimensionOneRosserArtificialBase L 0 t) <=
            Real.log (2 * (Real.log L) ^ 3) :=
          Real.log_le_log (dimensionOneRosserArtificialBase_pos hLPos)
            hbaseUpper
        _ = Real.log 2 + 3 * Real.log (Real.log L) := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
          norm_num
    have hlogA : Real.log (1 + a) <=
        Real.log 2 + 50 * Real.log t - Real.log L := by
      have hloga : Real.log a = 50 * Real.log t - Real.log L := by
        dsimp [a]
        rw [Real.log_div (pow_ne_zero 50 htPos.ne') hLPos.ne',
          Real.log_pow]
        norm_num
      have hlogBaseA : Real.log (1 + a) <= Real.log (2 * a) := by
        apply Real.log_le_log (by positivity)
        nlinarith [haLower]
      rw [Real.log_mul (by norm_num) ha.ne', hloga] at hlogBaseA
      convert hlogBaseA using 1; ring
    have hlogA_nonneg : 0 <= Real.log (1 + a) :=
      Real.log_nonneg (by linarith)
    have hfactor_le : (1 + a) / a <= 2 := by
      rw [div_le_iff₀ ha]
      nlinarith
    have htransBound : ((1 + a) / a) * Real.log (1 + a) <=
        2 * (Real.log 2 + 50 * Real.log t - Real.log L) := by
      calc
        ((1 + a) / a) * Real.log (1 + a) <=
            2 * Real.log (1 + a) :=
          mul_le_mul_of_nonneg_right hfactor_le hlogA_nonneg
        _ <= 2 * (Real.log 2 + 50 * Real.log t - Real.log L) :=
          mul_le_mul_of_nonneg_left hlogA (by norm_num)
    have hscaled : 48 * (50 + 2 * Real.log 2 + 100 * Real.log t -
        2 * Real.log L) <= Real.log t := by
      have hlogtUpper : Real.log t <=
          (Real.log L + 3 * Real.log (Real.log L)) / 50 := by
        have hlogtS0 : Real.log t <= Real.log s0 :=
          Real.log_le_log htPos ht.2
        have hlogCut := congrArg Real.log hcutoff
        rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
          Real.log_pow] at hlogCut
        norm_num at hlogCut
        nlinarith [hlogtS0, hlogCut]
      nlinarith [hgate, hlogtUpper]
    have htrans : 48 * (50 + ((1 + a) / a) * Real.log (1 + a)) <=
        Real.log t := by
      nlinarith [hscaled, htransBound]
    have hthetaPos : 0 < a / (1 + a) := div_pos ha (by linarith)
    have hmult := mul_le_mul_of_nonneg_left htrans hthetaPos.le
    have hslopeExact :
        dimensionOneRosserArtificialSlope L 0 t =
          Real.log (1 + a) + 50 * a / (1 + a) := by
      rw [dimensionOneRosserArtificialSlope_eq hLPos, hbase]
      have hterm :
          50 * t * (t + 0) ^ 49 / (L * (1 + a)) =
            50 * (a / (1 + a)) := by
        dsimp [a]
        field_simp
        ring
      rw [hterm]
      ring
    rw [hbaseFrac, hslopeExact]
    have hleftEq :
        a / (1 + a) * (48 * (50 + ((1 + a) / a) * Real.log (1 + a))) =
          48 * (Real.log (1 + a) + 50 * a / (1 + a)) := by
      field_simp [ha.ne', (by linarith : 1 + a ≠ 0)]
      ring
    rw [hleftEq] at hmult
    exact hmult

theorem exists_dimensionOneRosserSourceCutoffSlopeGate :
    ∃ L0 : Real, Real.exp 1 <= L0 ∧
      ∀ {L : Real}, L0 <= L ->
        124800 + 14400 * Real.log (Real.log L) <= Real.log L := by
  obtain ⟨S, _, hSgate⟩ :=
    exists_dimensionOneDelayLowerScale_error_threshold (C := (28800 : Real))
      (by norm_num)
  let L0 : Real := max (Real.exp 249600) (max (Real.exp 1) S)
  have hL0exp : Real.exp 1 <= L0 := by
    exact (le_max_left (Real.exp 1) S).trans
      (le_max_right (Real.exp 249600) (max (Real.exp 1) S))
  refine ⟨L0, hL0exp, ?_⟩
  intro L hL0L
  have hSle : S <= L :=
    (le_max_right (Real.exp 1) S).trans
      ((le_max_right (Real.exp 249600) (max (Real.exp 1) S)).trans hL0L)
  have hLPos : 0 < L := by
    exact (Real.exp_pos 1).trans_le (hL0exp.trans hL0L)
  have hLlogOne : 1 <= Real.log L :=
    (Real.le_log_iff_exp_le hLPos).2 (hL0exp.trans hL0L)
  have hLlogPos : 0 < Real.log L := by linarith
  have hlogGate : (28800 : Real) * Real.log (Real.log (2 * L)) <=
      Real.log L := hSgate hSle
  have hlogArg : Real.log L <= Real.log (2 * L) := by
    rw [Real.log_mul (by norm_num) hLPos.ne']
    linarith [Real.log_pos (by norm_num : (1 : Real) < 2)]
  have hloglog : Real.log (Real.log L) <=
      Real.log (Real.log (2 * L)) :=
    Real.log_le_log hLlogPos hlogArg
  have hhalf : 14400 * Real.log (Real.log L) <= Real.log L / 2 := by
    calc
      14400 * Real.log (Real.log L) <=
          14400 * Real.log (Real.log (2 * L)) :=
        mul_le_mul_of_nonneg_left hloglog (by norm_num)
      _ <= Real.log L / 2 := by nlinarith [hlogGate]
  have hconstant : (124800 : Real) <= Real.log L / 2 := by
    have hLlarge : (249600 : Real) <= Real.log L := by
      have h := (Real.le_log_iff_exp_le hLPos).2
        ((le_max_left (Real.exp 249600) (max (Real.exp 1) S)).trans hL0L)
      exact h
    linarith
  linarith

theorem exists_dimensionOneRosserSourceCutoffSlopeMargin :
    ∃ L0 : Real, Real.exp 1 <= L0 ∧
      ∀ {L s s0 t : Real}, L0 <= L ->
        Real.exp 5000 + 1 <= s -> s < s0 ->
        s0 ^ 50 = L * (Real.log L) ^ 3 -> t ∈ Icc s s0 ->
        48 * dimensionOneRosserArtificialSlope L 0 t <=
          (1 - (dimensionOneRosserArtificialBase L 0 t)⁻¹) * Real.log t := by
  obtain ⟨L0, hL0, hgate⟩ := exists_dimensionOneRosserSourceCutoffSlopeGate
  refine ⟨L0, hL0, ?_⟩
  intro L s s0 t hL0L hs hss0 hcutoff ht
  exact dimensionOneRosserSourceCutoffSlopeMargin
    (hL0.trans hL0L) hs hss0 hcutoff (hgate hL0L) ht

end PrimesRestrictedDigits
