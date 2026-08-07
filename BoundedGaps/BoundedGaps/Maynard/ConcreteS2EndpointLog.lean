import BoundedGaps.Maynard.MaynardS2CoordinateFiberAbel

noncomputable section

namespace BoundedGaps.Maynard

open Real

set_option maxRecDepth 4000 in
theorem abs_maynardS2CoordinateFiberEndpoint_log_ratio_sub_complement_log_ratio_le
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) r) (hR : 1 < R)
    (hQ : 1 < maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) :
    |Real.log (maynardS2CoordinateFiberEndpoint R
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) /
        Real.log R -
      (1 - Real.log (maynardS2OffCoordinateProduct
        BoundedGaps.engelsmaTuple m r) / Real.log R)| ≤
      Real.log 3 / Real.log R := by
  let P := maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r
  let Q := maynardS2CoordinateFiberEndpoint R P
  have hP : 0 < P := maynardS2OffCoordinateProduct_pos m r hr
  have hQnat : 1 < Q := by simpa [Q, P] using hQ
  have hQpos : 0 < Q := Nat.zero_lt_of_lt hQnat
  have hPone : 1 ≤ P := hP
  have hRpos : 0 < R := Nat.zero_lt_of_lt hR
  have hRlog : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hQP : Q * P ≤ R - 1 := by
    unfold Q maynardS2CoordinateFiberEndpoint
    simpa [Nat.mul_comm] using Nat.mul_div_le (R - 1) P
  have hRQP : R - 1 < (Q + 1) * P := by
    unfold Q maynardS2CoordinateFiberEndpoint
    exact (Nat.div_lt_iff_lt_mul hP).mp (Nat.lt_succ_self ((R - 1) / P))
  have hQone : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr hQpos.ne'
  have hupper : Q * P < R := lt_of_le_of_lt hQP (by omega)
  have htwice : Q + 1 ≤ 2 * Q := by omega
  have hRle : R ≤ 3 * Q * P := by
    have hQPP : 2 ≤ Q * P := by
      simpa using Nat.mul_le_mul hQnat hPone
    have hQPone : 1 ≤ Q * P := (by omega : 1 ≤ 2).trans hQPP
    have htwiceMul : (Q + 1) * P ≤ (2 * Q) * P := by
      exact Nat.mul_le_mul_right P htwice
    have hlt : R < 2 * Q * P + 1 := by
      calc
        R = (R - 1) + 1 := by omega
        _ < (Q + 1) * P + 1 := Nat.add_lt_add_right hRQP 1
        _ ≤ 2 * Q * P + 1 := by
          exact Nat.add_le_add_right (by simpa [Nat.mul_assoc] using htwiceMul) 1
    have hplus : 2 * Q * P + 1 ≤ 3 * Q * P := by
      calc
        2 * Q * P + 1 = 2 * (Q * P) + 1 := by ring
        _ ≤ 2 * (Q * P) + Q * P := Nat.add_le_add_left hQPone _
        _ = 3 * Q * P := by ring
    exact le_of_lt (hlt.trans_le hplus)
  have hQPreal : (0 : ℝ) < Q * P := by exact_mod_cast Nat.mul_pos hQpos hP
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hRpos
  have hupperLog : Real.log (Q : ℝ) + Real.log (P : ℝ) ≤
      Real.log R := by
    rw [← Real.log_mul (by exact_mod_cast hQpos.ne') (by exact_mod_cast hP.ne')]
    exact Real.strictMonoOn_log.monotoneOn hQPreal hRreal
      (by exact_mod_cast hupper.le)
  have hlowerLog : Real.log R ≤
      Real.log 3 + Real.log (Q : ℝ) + Real.log (P : ℝ) := by
    have h3QP : (0 : ℝ) < 3 * Q * P := by positivity
    have hRleReal : (R : ℝ) ≤ 3 * Q * P := by exact_mod_cast hRle
    have hmono := Real.strictMonoOn_log.monotoneOn hRreal h3QP hRleReal
    rw [show (3 : ℝ) * Q * P = 3 * ((Q : ℝ) * P) by ring] at hmono
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
      (by exact_mod_cast (Nat.mul_pos hQpos hP).ne')] at hmono
    rw [Real.log_mul (by exact_mod_cast hQpos.ne')
      (by exact_mod_cast hP.ne')] at hmono
    linarith
  have hdiffLower : 0 ≤
      (1 - Real.log P / Real.log R) - Real.log Q / Real.log R := by
    have hdiffLower' : 0 ≤ Real.log R - Real.log P - Real.log Q := by
      linarith [hupperLog]
    calc
      0 ≤ (Real.log R - Real.log P - Real.log Q) / Real.log R :=
        div_nonneg hdiffLower' hRlog.le
      _ = (1 - Real.log P / Real.log R) - Real.log Q / Real.log R := by
        field_simp [hRlog.ne']
  have hdiffUpper :
      (1 - Real.log P / Real.log R) - Real.log Q / Real.log R ≤
      Real.log 3 / Real.log R := by
    have hdiffUpper' : Real.log R - Real.log P - Real.log Q ≤ Real.log 3 := by
      linarith [hlowerLog]
    calc
      (1 - Real.log P / Real.log R) - Real.log Q / Real.log R =
          (Real.log R - Real.log P - Real.log Q) / Real.log R := by
            field_simp [hRlog.ne']
      _ ≤ Real.log 3 / Real.log R :=
        div_le_div_of_nonneg_right hdiffUpper' hRlog.le
  rw [abs_of_nonpos]
  · linarith
  · linarith

end BoundedGaps.Maynard
