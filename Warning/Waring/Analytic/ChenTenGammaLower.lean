import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# The gamma constant in Chen's Lemma 10

This file proves the elementary lower bound for the correctly normalized
fifteen-variable volume constant in Chen's Lemma 10 [CHEN1964-EN, pp. 1561,
1565].  The Chinese edition's denominator `Gamma(3)` is inconsistent with its
cubic cumulative count; the English denominator `Gamma(4)` is used here.
-/

namespace Waring.Analytic

/-- The correctly normalized volume constant for fifteen fifth powers. -/
noncomputable def chenTenT15 : Real :=
  Real.Gamma (6 / 5) ^ 15 / Real.Gamma 4

/-- A rational lower bound for the only nonintegral gamma value in `T₁₅`. -/
theorem five_sixths_le_Gamma_six_fifths :
    (5 / 6 : Real) ≤ Real.Gamma (6 / 5) := by
  have hmono : Real.Gamma 2 ≤ Real.Gamma (11 / 5) :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn
      (by norm_num) (by norm_num) (by norm_num)
  have hrec : Real.Gamma (11 / 5) =
      (6 / 5 : Real) * Real.Gamma (6 / 5) := by
    convert Real.Gamma_add_one (s := (6 / 5 : Real)) (by norm_num) using 1
    all_goals norm_num
  rw [Real.Gamma_two, hrec] at hmono
  linarith

/-- Chen's fifteen-variable volume constant is at least `1/100`. -/
theorem one_hundredth_le_chenTenT15 :
    (1 / 100 : Real) ≤ chenTenT15 := by
  have hpow : (5 / 6 : Real) ^ 15 ≤ Real.Gamma (6 / 5) ^ 15 := by
    gcongr
    exact five_sixths_le_Gamma_six_fifths
  have hGammaFour : Real.Gamma 4 = 6 := by norm_num
  rw [chenTenT15, hGammaFour]
  calc
    (1 / 100 : Real) ≤ (5 / 6 : Real) ^ 15 / 6 := by norm_num
    _ ≤ Real.Gamma (6 / 5) ^ 15 / 6 := by gcongr

/-- The exact rational margin used after weakening Chen's singular-integral
coefficient to `2999/1000`. -/
theorem chenTen_downstream_coefficient :
    (1 / 2000 : Real) <
      (2999 / 1000 : Real) * (1 / 100) * (1 / 4) * (999 / 10000) -
        1 / 10000 := by
  norm_num

end Waring.Analytic
