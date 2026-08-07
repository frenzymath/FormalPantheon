import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldCoefficient
import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldMellinInversion
import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldMellinPositiveLine

/-!
# Goldfeld's smoothed four-factor sum

This file specializes smooth Mellin inversion to the shifted four-factor
coefficient in the proof of Koukoulopoulos Theorem 12.9.  It
defines the source integral `I_alpha` with the continued Mellin transform and
proves the exact initial identity `S = I_2`.

Semantic review: `SEM-553`.
-/

noncomputable section

open Complex MeasureTheory

namespace BoundedGaps.Maynard

private instance goldfeldSmoothedLcmNeZero
    {q1 q : ℕ} [NeZero q1] [NeZero q] : NeZero (Nat.lcm q1 q) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩

/-- The four L-functions in Goldfeld's auxiliary Dirichlet series. -/
noncomputable def goldfeldFourFactorLFunction
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  riemannZeta s * DirichletCharacter.LFunction chi1 s *
    DirichletCharacter.LFunction chi s *
      DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) s

/-- The coefficient `f(n) / n^beta`, with the zero index explicitly
totalized as zero by `LSeries.term`. -/
noncomputable def goldfeldBetaCoefficient
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta : ℝ) (n : ℕ) : ℂ :=
  LSeries.term (goldfeldCoefficient chi1 chi) (beta : ℂ) n

private theorem goldfeldBetaCoefficient_term
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (goldfeldBetaCoefficient chi1 chi beta) s n =
      LSeries.term (goldfeldCoefficient chi1 chi)
        (s + (beta : ℂ)) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [goldfeldBetaCoefficient, LSeries.term_of_ne_zero hn]
    rw [Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
    field_simp

/-- The shifted coefficient series is the four-factor product wherever the
original series converges absolutely. -/
theorem goldfeldBetaCoefficient_LSeriesHasSum
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta : ℝ) {s : ℂ}
    (hs : 1 < (s + (beta : ℂ)).re) :
    LSeriesHasSum (goldfeldBetaCoefficient chi1 chi beta) s
      (goldfeldFourFactorLFunction chi1 chi (s + (beta : ℂ))) := by
  have h := goldfeldCoefficient_LSeriesHasSum chi1 chi hs
  change HasSum (LSeries.term (goldfeldBetaCoefficient chi1 chi beta) s) _
  simpa [goldfeldFourFactorLFunction] using
    h.congr_fun (goldfeldBetaCoefficient_term chi1 chi beta s)

/-- The source auxiliary sum `S`.  When `x > 0`, the `tsum` is finite in
effect because the plateau vanishes from `2` onward. -/
noncomputable def goldfeldSmoothedSum
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x : ℝ) : ℂ :=
  ∑' n : ℕ,
    goldfeldBetaCoefficient chi1 chi beta n *
      (goldfeldPlateau ((n : ℝ) / x) : ℂ)

/-- The continued integrand used before and after the Goldfeld contour
displacement. -/
noncomputable def goldfeldContourIntegrand
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x : ℝ) (s : ℂ) : ℂ :=
  goldfeldFourFactorLFunction chi1 chi (s + (beta : ℂ)) *
    goldfeldMellinContinuationData.Phi s * (x : ℂ) ^ s

/-- The source integral `I_alpha`, parameterized upward by the real line. -/
noncomputable def goldfeldVerticalIntegral
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x alpha : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ t : ℝ,
      goldfeldContourIntegrand chi1 chi beta x
        ((alpha : ℂ) + t * I)

/-- Exercise 7.2(d) specialized exactly as in Theorem 12.9: `S = I_2`. -/
theorem goldfeldSmoothedSum_eq_verticalIntegral_two
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ} (hbeta : -1 < beta) (hx : 1 ≤ x) :
    goldfeldSmoothedSum chi1 chi beta x =
      goldfeldVerticalIntegral chi1 chi beta x 2 := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hsum : LSeriesSummable
      (goldfeldBetaCoefficient chi1 chi beta) (2 : ℂ) := by
    apply (goldfeldBetaCoefficient_LSeriesHasSum
      chi1 chi beta (s := (2 : ℂ)) ?_).LSeriesSummable
    norm_num
    linarith
  have hinversion := smoothMellinLSeriesInversion
    (goldfeldBetaCoefficient chi1 chi beta) (by simp [goldfeldBetaCoefficient])
    (fun y : ℝ => (goldfeldPlateau y : ℂ))
    (alpha := 2) (x := x) (by norm_num) hxpos hsum
    (goldfeldRawMellin_convergent (by norm_num))
    (goldfeldRawMellin_verticalIntegrable (by norm_num))
    (Complex.continuous_ofReal.comp goldfeldPlateau_contDiff.continuous)
  rw [goldfeldSmoothedSum, goldfeldVerticalIntegral]
  calc
    (∑' n : ℕ,
        goldfeldBetaCoefficient chi1 chi beta n *
          (goldfeldPlateau ((n : ℝ) / x) : ℂ)) =
        (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
          ∫ t : ℝ,
            LSeries (goldfeldBetaCoefficient chi1 chi beta)
                ((2 : ℂ) + t * I) *
              goldfeldRawMellin ((2 : ℂ) + t * I) *
              (x : ℂ) ^ ((2 : ℂ) + t * I) := hinversion
    _ = (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
          ∫ t : ℝ,
            goldfeldContourIntegrand chi1 chi beta x
              ((2 : ℂ) + t * I) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      have hs : 1 < (((2 : ℂ) + t * I) + (beta : ℂ)).re := by
        norm_num
        linarith
      have hseries := (goldfeldBetaCoefficient_LSeriesHasSum
        chi1 chi beta (s := (2 : ℂ) + t * I) hs).LSeries_eq
      have hphi := goldfeldMellinContinuationData.agrees_on_right
        (s := (2 : ℂ) + t * I) (by norm_num)
      rw [hseries, ← hphi]
      rfl

end BoundedGaps.Maynard
