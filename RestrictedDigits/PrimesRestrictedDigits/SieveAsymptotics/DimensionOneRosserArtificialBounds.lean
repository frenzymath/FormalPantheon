import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserArtificialFactor
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Explicit bounds for the artificial Rosser factor

The deliberately large threshold here closes the source's qualitative "sufficiently large"
derivative conditions in the restricted Maynard range.
-/

open Set

namespace PrimesRestrictedDigits

theorem dimensionOneRosserPowerRatio_mem
    {L s s0 t : Real} (hL : 0 < L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcap : s0 ^ 50 <= L) (ht : t ∈ Icc s s0) :
    0 < t ^ 50 / L ∧ t ^ 50 / L <= 1 := by
  have hsPos : 0 < s := by nlinarith [Real.exp_pos (5000 : Real)]
  have htPos : 0 < t := hsPos.trans_le ht.1
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hpow : t ^ 50 <= s0 ^ 50 :=
    pow_le_pow_left₀ htPos.le ht.2 50
  constructor
  · exact div_pos (pow_pos htPos 50) hL
  · exact (div_le_one hL).2 (hpow.trans hcap)

theorem dimensionOneRosser_log_gt_fiveThousand
    {s t : Real} (hs : Real.exp 5000 + 1 <= s) (hst : s <= t) :
    5000 < Real.log t := by
  have htPos : 0 < t := by
    nlinarith [Real.exp_pos (5000 : Real)]
  apply (Real.lt_log_iff_exp_lt htPos).2
  exact (lt_add_one (Real.exp 5000)).trans_le (hs.trans hst)

theorem dimensionOneRosserArtificialSlope_zero_le
    {L t : Real} (hL : 0 < L) (ht : 0 < t) :
    dimensionOneRosserArtificialSlope L 0 t <=
      51 * (t ^ 50 / L) := by
  let a : Real := t ^ 50 / L
  have ha : 0 < a := div_pos (pow_pos ht 50) hL
  have hbase : dimensionOneRosserArtificialBase L 0 t = 1 + a := by
    simp [dimensionOneRosserArtificialBase, a]
  have hlog : Real.log (dimensionOneRosserArtificialBase L 0 t) <= a := by
    rw [hbase]
    simpa using Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + a)
  have hterm :
      50 * t * (t + 0) ^ 49 /
          (L * dimensionOneRosserArtificialBase L 0 t) =
        50 * a / (1 + a) := by
    rw [hbase]
    dsimp [a]
    field_simp
    ring
  have hfrac : a / (1 + a) <= a := by
    rw [div_le_iff₀ (by linarith : 0 < 1 + a)]
    nlinarith [sq_nonneg a]
  have htermLe : 50 * a / (1 + a) <= 50 * a := by
    calc
      50 * a / (1 + a) = 50 * (a / (1 + a)) := by ring
      _ <= 50 * a := mul_le_mul_of_nonneg_left hfrac (by norm_num)
  rw [dimensionOneRosserArtificialSlope_eq hL, hterm]
  dsimp [a]
  linarith

theorem dimensionOneRosserArtificialSlope_zero_margin
    {L s s0 t : Real} (hL : 0 < L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcap : s0 ^ 50 <= L) (ht : t ∈ Icc s s0) :
    48 * dimensionOneRosserArtificialSlope L 0 t <=
      (1 - (dimensionOneRosserArtificialBase L 0 t)⁻¹) *
        Real.log t := by
  let a : Real := t ^ 50 / L
  have haData := dimensionOneRosserPowerRatio_mem hL hs hss0 hcap ht
  have ha : 0 < a := haData.1
  have haOne : a <= 1 := haData.2
  have hbase : dimensionOneRosserArtificialBase L 0 t = 1 + a := by
    simp [dimensionOneRosserArtificialBase, a]
  have hslope : dimensionOneRosserArtificialSlope L 0 t <= 51 * a := by
    apply dimensionOneRosserArtificialSlope_zero_le hL
    have hsPos : 0 < s := by
      nlinarith [Real.exp_pos (5000 : Real)]
    exact hsPos.trans_le ht.1
  have hlog : 5000 < Real.log t :=
    dimensionOneRosser_log_gt_fiveThousand hs ht.1
  have hfracEq :
      1 - (dimensionOneRosserArtificialBase L 0 t)⁻¹ =
        a / (1 + a) := by
    rw [hbase]
    field_simp
    ring
  have hfracLower : a / 2 <= a / (1 + a) := by
    have hinv : 1 / (2 : Real) <= 1 / (1 + a) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    calc
      a / 2 = a * (1 / 2) := by ring
      _ <= a * (1 / (1 + a)) :=
        mul_le_mul_of_nonneg_left hinv ha.le
      _ = a / (1 + a) := by ring
  have hright : 2500 * a <
      (1 - (dimensionOneRosserArtificialBase L 0 t)⁻¹) *
        Real.log t := by
    rw [hfracEq]
    calc
      2500 * a = (a / 2) * 5000 := by ring
      _ < (a / 2) * Real.log t :=
        mul_lt_mul_of_pos_left hlog (div_pos ha (by norm_num))
      _ <= (a / (1 + a)) * Real.log t :=
        mul_le_mul_of_nonneg_right hfracLower (by linarith)
  have hleft :
      48 * dimensionOneRosserArtificialSlope L 0 t <= 2448 * a := by
    calc
      48 * dimensionOneRosserArtificialSlope L 0 t <= 48 * (51 * a) :=
        mul_le_mul_of_nonneg_left hslope (by norm_num)
      _ = 2448 * a := by ring
  exact hleft.trans (by nlinarith)

theorem dimensionOneRosserArtificialSlope_one_lt
    {L u : Real} (hL : 0 < L) (hu : 0 < u) :
    dimensionOneRosserArtificialSlope L 1 u <
      51 * ((u + 1) ^ 50 / L) := by
  let a : Real := (u + 1) ^ 50 / L
  let n : Real := u * (u + 1) ^ 49 / L
  have huOne : 0 < u + 1 := by linarith
  have ha : 0 < a := div_pos (pow_pos huOne 50) hL
  have hbase : dimensionOneRosserArtificialBase L 1 u = 1 + a := by
    simp [dimensionOneRosserArtificialBase, a]
  have hlog : Real.log (dimensionOneRosserArtificialBase L 1 u) < a := by
    rw [hbase]
    simpa using Real.log_lt_sub_one_of_pos (by linarith : 0 < 1 + a)
      (by linarith : 1 + a ≠ 1)
  have hnumer : n < a := by
    apply (div_lt_div_iff_of_pos_right hL).2
    calc
      u * (u + 1) ^ 49 < (u + 1) * (u + 1) ^ 49 :=
        mul_lt_mul_of_pos_right (by linarith) (pow_pos huOne 49)
      _ = (u + 1) ^ 50 := by ring
  have hfracLe : a / (1 + a) <= a := by
    rw [div_le_iff₀ (by linarith : 0 < 1 + a)]
    nlinarith [sq_nonneg a]
  have hnfrac : n / (1 + a) < a :=
    ((div_lt_div_iff_of_pos_right (by linarith : 0 < 1 + a)).2
      hnumer).trans_le hfracLe
  have htermEq :
      50 * u * (u + 1) ^ 49 /
          (L * dimensionOneRosserArtificialBase L 1 u) =
        50 * (n / (1 + a)) := by
    rw [hbase]
    dsimp [n]
    field_simp
  have hterm :
      50 * u * (u + 1) ^ 49 /
          (L * dimensionOneRosserArtificialBase L 1 u) < 50 * a := by
    rw [htermEq]
    exact mul_lt_mul_of_pos_left hnfrac (by norm_num)
  rw [dimensionOneRosserArtificialSlope_eq hL]
  linarith

theorem dimensionOneRosserArtificialSlope_one_shift_lt
    {L s s0 t : Real} (hL : 0 < L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcap : s0 ^ 50 <= L) (ht : t ∈ Icc s s0) :
    dimensionOneRosserArtificialSlope L 1 (t - 1) <
      Real.log (t - 1) / 48 := by
  let a : Real := t ^ 50 / L
  have haData := dimensionOneRosserPowerRatio_mem hL hs hss0 hcap ht
  have haOne : a <= 1 := haData.2
  have huExp : Real.exp 5000 <= t - 1 := by linarith [ht.1]
  have huPos : 0 < t - 1 := (Real.exp_pos 5000).trans_le huExp
  have hlog : 5000 <= Real.log (t - 1) :=
    (Real.le_log_iff_exp_le huPos).2 huExp
  have hslope : dimensionOneRosserArtificialSlope L 1 (t - 1) <
      51 * a := by
    have h := dimensionOneRosserArtificialSlope_one_lt hL huPos
    simpa [a] using h
  calc
    dimensionOneRosserArtificialSlope L 1 (t - 1) < 51 * a := hslope
    _ <= 51 := by nlinarith
    _ < 5000 / 48 := by norm_num
    _ <= Real.log (t - 1) / 48 := by linarith

theorem dimensionOneRosserPlusArtificialAux_strictAntiOn_of_slope
    {L epsilon a b : Real} (hL : 0 < L) (ha : 3 <= a)
    (_hab : a <= b)
    (hSlope : ∀ t ∈ Ioo a b,
      48 * dimensionOneRosserArtificialSlope L epsilon t <= Real.log t) :
    StrictAntiOn (dimensionOneRosserPlusArtificialAux L epsilon)
      (Icc a b) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg
    (D := Icc a b)
    (f' := fun t => dimensionOneRosserArtificialFactor L epsilon t *
      (dimensionOneRosserArtificialSlope L epsilon t *
          dimensionOneDelayScaledPlus t -
        t * dimensionOneDelayQMinus (t - 1)))
    (convex_Icc a b) ?_ ?_ ?_
  · exact (dimensionOneRosserPlusArtificialAux_continuous hL).continuousOn
  · intro t ht
    rw [interior_Icc] at ht
    exact (dimensionOneRosserPlusArtificialAux_hasDerivAt hL
      (by linarith [ht.1])).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact mul_neg_of_pos_of_neg (Real.exp_pos _)
      (dimensionOneRosserPlusArtificial_derivCore_neg_of_slope
        (by linarith [ht.1]) (hSlope t ht))

theorem dimensionOneRosserMinusArtificialAux_strictAntiOn_of_slope
    {L epsilon a b : Real} (hL : 0 < L) (ha : 2 <= a)
    (_hab : a <= b)
    (hSlope : ∀ t ∈ Ioo a b,
      48 * dimensionOneRosserArtificialSlope L epsilon t <= Real.log t) :
    StrictAntiOn (dimensionOneRosserMinusArtificialAux L epsilon)
      (Icc a b) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg
    (D := Icc a b)
    (f' := fun t => dimensionOneRosserArtificialFactor L epsilon t *
      (dimensionOneRosserArtificialSlope L epsilon t *
          dimensionOneDelayScaledMinus t -
        t * dimensionOneDelayQPlus (t - 1)))
    (convex_Icc a b) ?_ ?_ ?_
  · exact (dimensionOneRosserMinusArtificialAux_continuous hL).continuousOn
  · intro t ht
    rw [interior_Icc] at ht
    exact (dimensionOneRosserMinusArtificialAux_hasDerivAt hL
      (by linarith [ht.1])).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact mul_neg_of_pos_of_neg (Real.exp_pos _)
      (dimensionOneRosserMinusArtificial_derivCore_neg_of_slope
        (by linarith [ht.1]) (hSlope t ht))

theorem dimensionOneRosserPlusArtificialAux_one_strictAntiOn
    {L s s0 : Real} (hL : 0 < L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcap : s0 ^ 50 <= L) :
    StrictAntiOn (dimensionOneRosserPlusArtificialAux L 1)
      (Icc (s - 1) (s0 - 1)) := by
  apply dimensionOneRosserPlusArtificialAux_strictAntiOn_of_slope
    (epsilon := (1 : Real)) (a := s - 1) (b := s0 - 1) hL (by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith) (by linarith)
  intro u hu
  have ht : u + 1 ∈ Icc s s0 := by
    constructor <;> linarith [hu.1, hu.2]
  have h := dimensionOneRosserArtificialSlope_one_shift_lt
    hL hs hss0 hcap ht
  have h' : dimensionOneRosserArtificialSlope L 1 u <
      Real.log u / 48 := by simpa using h
  nlinarith [h']

theorem dimensionOneRosserMinusArtificialAux_one_strictAntiOn
    {L s s0 : Real} (hL : 0 < L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcap : s0 ^ 50 <= L) :
    StrictAntiOn (dimensionOneRosserMinusArtificialAux L 1)
      (Icc (s - 1) (s0 - 1)) := by
  apply dimensionOneRosserMinusArtificialAux_strictAntiOn_of_slope
    (epsilon := (1 : Real)) (a := s - 1) (b := s0 - 1) hL (by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith) (by linarith)
  intro u hu
  have ht : u + 1 ∈ Icc s s0 := by
    constructor <;> linarith [hu.1, hu.2]
  have h := dimensionOneRosserArtificialSlope_one_shift_lt
    hL hs hss0 hcap ht
  have h' : dimensionOneRosserArtificialSlope L 1 u <
      Real.log u / 48 := by simpa using h
  nlinarith [h']

end PrimesRestrictedDigits
