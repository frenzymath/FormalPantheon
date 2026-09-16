import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceCutoffSlope

/-!
# Source-cutoff shifted second-weight layer

This file proves the epsilon-one slope and cap-free shifted antitonicity needed by Eq. (8.11).
-/

open Set

namespace PrimesRestrictedDigits

private lemma sourceCutoffShiftedLogOneAddHigh
    {a : Real} (ha : 1 <= a) :
    Real.log (1 + a) <= 1 + Real.log a := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have h1 : 0 < 1 + a := by linarith
  have hle : 1 + a <= 2 * a := by nlinarith
  have hlog := Real.log_le_log h1 hle
  rw [Real.log_mul (by norm_num) ha0.ne'] at hlog
  have hlog2 := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
  norm_num at hlog2
  linarith

theorem dimensionOneRosserSourceCutoffSlopeOneShift
    {L s s0 t : Real} (hL : Real.exp 1 <= L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L)
    (ht : t ∈ Icc s s0) :
    dimensionOneRosserArtificialSlope L 1 (t - 1) <
      Real.log (t - 1) / 48 := by
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hL
  have hU : 1 <= Real.log L :=
    (Real.le_log_iff_exp_le hLPos).2 hL
  let U : Real := Real.log L
  let V : Real := Real.log U
  let a : Real := t ^ 50 / L
  have hUpos : 0 < U := by dsimp [U]; linarith
  have hsPos : 0 < s := by nlinarith [Real.exp_pos (5000 : Real)]
  have htPos : 0 < t := hsPos.trans_le ht.1
  have huExp : Real.exp 5000 <= t - 1 := by linarith [ht.1]
  have huPos : 0 < t - 1 := (Real.exp_pos 5000).trans_le huExp
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (pow_pos htPos 50) hLPos
  have hbase : dimensionOneRosserArtificialBase L 1 (t - 1) = 1 + a := by
    simp [dimensionOneRosserArtificialBase, a]
  have hlogu : Real.log t - 1 <= Real.log (t - 1) := by
    have ht2 : 2 <= t := by
      have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
      linarith [hs, ht.1]
    have htHalf : t / 2 <= t - 1 := by nlinarith
    have hlogHalf : Real.log (t / 2) = Real.log t - Real.log 2 := by
      rw [Real.log_div htPos.ne' (by norm_num)]
    have hmon : Real.log (t / 2) <= Real.log (t - 1) := by
      apply Real.log_le_log
      · positivity
      · exact htHalf
    have hlog2 := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
    norm_num at hlog2
    rw [hlogHalf] at hmon
    linarith
  have hcutlog : 50 * Real.log s0 = U + 3 * V := by
    have h := congrArg Real.log hcutoff
    rw [Real.log_pow, Real.log_mul hLPos.ne'
      (pow_ne_zero 3 hUpos.ne'), Real.log_pow] at h
    dsimp [U, V] at h ⊢
    linarith
  have hlogtUpper : Real.log t <= (U + 3 * V) / 50 := by
    have hs0Pos : 0 < s0 := hsPos.trans hss0
    have hlogle : Real.log t <= Real.log s0 :=
      Real.log_le_log htPos ht.2
    nlinarith [hcutlog]
  have hgate' : 124800 + 14400 * V <= U := by
    simpa [U, V] using hgate
  have hVnonneg : 0 <= V := by
    dsimp [V]
    exact Real.log_nonneg hU
  have hloga : Real.log a = 50 * Real.log t - U := by
    dsimp [a, U]
    rw [Real.log_div (pow_ne_zero 50 htPos.ne') hLPos.ne', Real.log_pow]
    norm_num
  rcases le_total a 1 with haLow | haHigh
  · have hslopeLow : dimensionOneRosserArtificialSlope L 1 (t - 1) < 51 := by
      have h := dimensionOneRosserArtificialSlope_one_lt hLPos huPos
      have h' : dimensionOneRosserArtificialSlope L 1 (t - 1) < 51 * a := by
        simpa [a] using h
      nlinarith
    have hloguLarge : 5000 <= Real.log (t - 1) :=
      (Real.le_log_iff_exp_le huPos).2 huExp
    nlinarith
  · have hlog1a : Real.log (1 + a) <= 1 + Real.log a :=
      sourceCutoffShiftedLogOneAddHigh haHigh
    have hslopeBound : dimensionOneRosserArtificialSlope L 1 (t - 1) <
        51 + 50 * Real.log t - U := by
      have hn : (t - 1) * t ^ 49 / L < a := by
        dsimp [a]
        apply (div_lt_div_iff_of_pos_right hLPos).2
        calc
          (t - 1) * t ^ 49 < t * t ^ 49 :=
            mul_lt_mul_of_pos_right (by linarith) (pow_pos htPos 49)
          _ = t ^ 50 := by ring
      have hn' : (t - 1) * t ^ 49 / (L * (1 + a)) < 1 := by
        rw [div_lt_one (by positivity)]
        have hna : (t - 1) * t ^ 49 / L < 1 + a :=
          hn.trans_le (by linarith)
        field_simp [hLPos.ne'] at hna ⊢
        nlinarith
      have hterm : 50 * (t - 1) * t ^ 49 /
            (L * (1 + a)) < 50 := by
        calc
          50 * (t - 1) * t ^ 49 / (L * (1 + a)) =
              50 * ((t - 1) * t ^ 49 / (L * (1 + a))) := by ring
          _ < 50 * 1 := mul_lt_mul_of_pos_left hn' (by norm_num)
          _ = 50 := by ring
      rw [dimensionOneRosserArtificialSlope_eq hLPos, hbase]
      simp only [sub_add_cancel]
      have hlogpart : Real.log (1 + a) <= 1 + 50 * Real.log t - U := by
        nlinarith [hlog1a, hloga]
      nlinarith
    have hgateWeak : 7197 * V + 122450 <= U := by
      nlinarith [hgate', hVnonneg]
    have htarget : 2399 * Real.log t + 2449 <= 48 * U := by
      nlinarith [hgateWeak, hlogtUpper]
    have hbound : 48 * dimensionOneRosserArtificialSlope L 1 (t - 1) <
        Real.log (t - 1) := by
      nlinarith [hslopeBound, hlogu, htarget]
    linarith

theorem dimensionOneRosserSourcePlusArtificialAux_one_strictAntiOn
    {L s s0 : Real} (hL : Real.exp 1 <= L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L) :
    StrictAntiOn (dimensionOneRosserPlusArtificialAux L 1)
      (Icc (s - 1) (s0 - 1)) := by
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hL
  apply dimensionOneRosserPlusArtificialAux_strictAntiOn_of_slope
    (epsilon := (1 : Real)) (a := s - 1) (b := s0 - 1) hLPos (by
      have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
      linarith) (by linarith)
  intro u hu
  have ht : u + 1 ∈ Icc s s0 := by
    constructor <;> linarith [hu.1, hu.2]
  have h := dimensionOneRosserSourceCutoffSlopeOneShift
    hL hs hss0 hcutoff hgate ht
  have h' : dimensionOneRosserArtificialSlope L 1 u <
      Real.log u / 48 := by simpa using h
  nlinarith [h']

theorem dimensionOneRosserSourceMinusArtificialAux_one_strictAntiOn
    {L s s0 : Real} (hL : Real.exp 1 <= L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L) :
    StrictAntiOn (dimensionOneRosserMinusArtificialAux L 1)
      (Icc (s - 1) (s0 - 1)) := by
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hL
  apply dimensionOneRosserMinusArtificialAux_strictAntiOn_of_slope
    (epsilon := (1 : Real)) (a := s - 1) (b := s0 - 1) hLPos (by
      have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
      linarith) (by linarith)
  intro u hu
  have ht : u + 1 ∈ Icc s s0 := by
    constructor <;> linarith [hu.1, hu.2]
  have h := dimensionOneRosserSourceCutoffSlopeOneShift
    hL hs hss0 hcutoff hgate ht
  have h' : dimensionOneRosserArtificialSlope L 1 u <
      Real.log u / 48 := by simpa using h
  nlinarith [h']

theorem dimensionOneRosserSourcePlusSecondKernel_antitoneOn
    {L s s0 : Real} (hL : Real.exp 1 <= L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L) :
    AntitoneOn (dimensionOneRosserPlusSecondKernel L) (Icc s s0) := by
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hL
  apply dimensionOneRosserPlusSecondKernel_antitoneOn_of_aux hLPos (by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith)
  exact (dimensionOneRosserSourceMinusArtificialAux_one_strictAntiOn
    hL hs hss0 hcutoff hgate).antitoneOn

theorem dimensionOneRosserSourceMinusSecondKernel_antitoneOn
    {L s s0 : Real} (hL : Real.exp 1 <= L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L) :
    AntitoneOn (dimensionOneRosserMinusSecondKernel L) (Icc s s0) := by
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hL
  apply dimensionOneRosserMinusSecondKernel_antitoneOn_of_aux hLPos (by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith)
  exact (dimensionOneRosserSourcePlusArtificialAux_one_strictAntiOn
    hL hs hss0 hcutoff hgate).antitoneOn

end PrimesRestrictedDigits
