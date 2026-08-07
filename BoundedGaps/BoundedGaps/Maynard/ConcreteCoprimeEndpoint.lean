import BoundedGaps.Maynard.ConcreteS1CrossGrowth
import BoundedGaps.Maynard.PrimorialCoprimeHarmonic

noncomputable section

/-! The concrete Engelsma/Maynard radius satisfies the primorial endpoint condition. -/

namespace BoundedGaps.Maynard

open Filter

theorem eventually_engelsmaMaynardModulus_le_radius
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      engelsmaMaynardModulus N ≤ engelsmaMaynardRadius alpha N := by
  have hmod := eventually_engelsmaMaynardModulus_le_logRadius halpha
  have hlog := eventually_log_engelsmaMaynardRadius_ge_half halpha
  filter_upwards [hmod, hlog, eventually_ge_atTop 3] with N hmod hlog hN
  have hlogBase : 0 < Real.log ((N - 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N - 1 by omega)
  have hRlogPos : 0 < Real.log (engelsmaMaynardRadius alpha N) := by
    exact lt_of_lt_of_le (mul_pos (by positivity) hlogBase) hlog
  have hRpos : (0 : ℝ) < engelsmaMaynardRadius alpha N := by
    have hRone := (Real.log_pos_iff (by positivity)).mp hRlogPos
    linarith
  have hlogLe : Real.log (engelsmaMaynardRadius alpha N) ≤
      engelsmaMaynardRadius alpha N := by
    exact (Real.log_le_sub_one_of_pos hRpos).trans (by linarith)
  exact_mod_cast hmod.trans hlogLe

theorem eventually_abs_engelsmaPrimorialCoprimeHarmonic_error
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      |coprimeHarmonicSum (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) -
        primorialCoprimeHarmonicMainTerm
          (tripleLogCutoff (N - 1))
          (engelsmaMaynardRadius alpha N)| ≤
        engelsmaMaynardModulus N := by
  filter_upwards [eventually_engelsmaMaynardModulus_le_radius halpha] with N hN
  unfold engelsmaMaynardModulus at hN ⊢
  exact abs_coprimeHarmonicSum_sub_primorialMainTerm_le hN

end BoundedGaps.Maynard
