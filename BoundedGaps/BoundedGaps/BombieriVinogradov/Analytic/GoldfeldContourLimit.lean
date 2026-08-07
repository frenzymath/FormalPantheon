import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldContourRectangle
import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldHorizontalEdgeLimit
import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldLeftLineIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Goldfeld's complete contour displacement

The raw right line is proved genuinely Bochner integrable from absolute
Dirichlet-series convergence and the already established Mellin integrability.
Both finite vertical edges then converge to their complete lines, and SEM-557
sends the source-oriented horizontal edges to zero. This turns SEM-559's exact
finite rectangle into `I_2 = residue + I_(-1)`.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 73--74 and
125--126, especially (7.9) and Theorem 12.9. Semantic review: `SEM-559`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory Filter
open scoped Topology

noncomputable section

private theorem continuous_goldfeldRightLineMultiplier
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ} (hbeta : -1 < beta) (hx : 0 < x) :
    Continuous (fun t : ℝ =>
      goldfeldFourFactorLFunction chi1 chi
          (((2 : ℂ) + t * I) + (beta : ℂ)) *
        (x : ℂ) ^ ((2 : ℂ) + t * I)) := by
  let s : ℝ → ℂ := fun t => (2 : ℂ) + t * I
  have hs : Continuous s := by fun_prop
  have hshift : Continuous (fun t : ℝ => s t + (beta : ℂ)) :=
    hs.add continuous_const
  have hnotOne (t : ℝ) : s t + (beta : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    linarith
  have hzeta : Continuous (fun t : ℝ =>
      riemannZeta (s t + (beta : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t
    simpa [Function.comp_def] using
      (differentiableAt_riemannZeta (hnotOne t)).continuousAt.comp
        (f := fun u : ℝ => s u + (beta : ℂ)) hshift.continuousAt
  have hchi1 : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction chi1 (s t + (beta : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t
    simpa [Function.comp_def] using
      (DirichletCharacter.differentiableAt_LFunction chi1
        (s t + (beta : ℂ)) (.inl (hnotOne t))).continuousAt.comp
          (f := fun u : ℝ => s u + (beta : ℂ)) hshift.continuousAt
  have hchi : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction chi (s t + (beta : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t
    simpa [Function.comp_def] using
      (DirichletCharacter.differentiableAt_LFunction chi
        (s t + (beta : ℂ)) (.inl (hnotOne t))).continuousAt.comp
          (f := fun u : ℝ => s u + (beta : ℂ)) hshift.continuousAt
  have hcross : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi)
        (s t + (beta : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t
    simpa [Function.comp_def] using
      (DirichletCharacter.differentiableAt_LFunction
        (DirichletCharacter.mul chi1 chi)
        (s t + (beta : ℂ)) (.inl (hnotOne t))).continuousAt.comp
          (f := fun u : ℝ => s u + (beta : ℂ)) hshift.continuousAt
  have hxpow : Continuous (fun t : ℝ => (x : ℂ) ^ (s t)) :=
    continuous_const.cpow hs fun _ => Complex.ofReal_mem_slitPlane.mpr hx
  have hfour := (((hzeta.mul hchi1).mul hchi).mul hcross)
  change Continuous (fun t : ℝ =>
    (((riemannZeta (s t + (beta : ℂ)) *
      DirichletCharacter.LFunction chi1 (s t + (beta : ℂ))) *
      DirichletCharacter.LFunction chi (s t + (beta : ℂ))) *
      DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi)
        (s t + (beta : ℂ))) * (x : ℂ) ^ (s t))
  exact hfour.mul hxpow

/-- The complete raw right line `Re(s)=2` is genuinely Bochner integrable.
No nonprincipal-character premise is needed in the half-plane of absolute
Dirichlet-series convergence. -/
theorem goldfeldContourIntegrand_two_verticalIntegrable
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ} (hbeta : -1 < beta) (hx : 0 < x) :
    VerticalIntegrable
      (goldfeldContourIntegrand chi1 chi beta x) 2 := by
  let a : ℕ → ℂ := goldfeldBetaCoefficient chi1 chi beta
  let s : ℝ → ℂ := fun t => (2 : ℂ) + t * I
  let phiLine : ℝ → ℂ := fun t => goldfeldRawMellin (s t)
  let multiplier : ℝ → ℂ := fun t =>
    goldfeldFourFactorLFunction chi1 chi (s t + (beta : ℂ)) *
      (x : ℂ) ^ (s t)
  have hsum : LSeriesSummable a (2 : ℂ) := by
    apply (goldfeldBetaCoefficient_LSeriesHasSum
      chi1 chi beta (s := (2 : ℂ)) ?_).LSeriesSummable
    norm_num
    linarith
  let K : ℝ := ∑' n : ℕ, ‖LSeries.term a (2 : ℂ) n‖
  have hfactor (t : ℝ) :
      ‖goldfeldFourFactorLFunction chi1 chi
        (s t + (beta : ℂ))‖ ≤ K := by
    have hsReal : 1 < ((s t + (beta : ℂ))).re := by
      simp [s]
      linarith
    have hseries := goldfeldBetaCoefficient_LSeriesHasSum
      chi1 chi beta (s := s t) hsReal
    have hline : LSeriesSummable a (s t) := by
      simpa [a] using hseries.LSeriesSummable
    have hlineNorm : Summable fun n : ℕ => ‖LSeries.term a (s t) n‖ :=
      summable_norm_iff.mpr hline
    calc
      ‖goldfeldFourFactorLFunction chi1 chi
          (s t + (beta : ℂ))‖ = ‖LSeries a (s t)‖ := by
            rw [hseries.LSeries_eq]
      _ ≤ ∑' n : ℕ, ‖LSeries.term a (s t) n‖ :=
        norm_tsum_le_tsum_norm hlineNorm
      _ = K := by
        apply tsum_congr
        intro n
        simp only [LSeries.norm_term_eq]
        congr 2
        simp [s]
  have hmultiplierContinuous : Continuous multiplier := by
    simpa [multiplier, s] using
      continuous_goldfeldRightLineMultiplier chi1 chi hbeta hx
  have hmultiplierBound : ∀ᵐ t : ℝ, ‖multiplier t‖ ≤ K * x ^ 2 :=
    ae_of_all _ fun t => by
      simp only [multiplier, norm_mul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      have hxpow : x ^ (s t).re = x ^ 2 := by
        rw [show (s t).re = 2 by simp [s], Real.rpow_two]
      rw [hxpow]
      exact mul_le_mul_of_nonneg_right (hfactor t) (sq_nonneg x)
  have hphi : Integrable phiLine := by
    simpa [phiLine, s, VerticalIntegrable] using
      (goldfeldRawMellin_verticalIntegrable (alpha := 2) (by norm_num))
  have hproduct : Integrable fun t => phiLine t * multiplier t :=
    hphi.mul_bdd hmultiplierContinuous.aestronglyMeasurable
      hmultiplierBound
  rw [VerticalIntegrable]
  refine hproduct.congr (ae_of_all _ fun t => ?_)
  change phiLine t * multiplier t =
    goldfeldContourIntegrand chi1 chi beta x (s t)
  have hPhi := goldfeldMellinContinuationData.agrees_on_right
    (s := s t) (by simp [s])
  rw [goldfeldContourIntegrand, hPhi]
  simp only [phiLine, multiplier, s]
  ring

private theorem tendsto_goldfeldTruncatedVerticalIntegral_of_verticalIntegrable
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x alpha : ℝ)
    (hvertical : VerticalIntegrable
      (goldfeldContourIntegrand chi1 chi beta x) alpha) :
    Tendsto
      (goldfeldTruncatedVerticalIntegral chi1 chi beta x alpha)
      atTop
      (𝓝 (goldfeldVerticalIntegral chi1 chi beta x alpha)) := by
  let f : ℝ → ℂ := fun t =>
    goldfeldContourIntegrand chi1 chi beta x
      ((alpha : ℂ) + t * I)
  have hraw : Integrable f := by
    simpa [VerticalIntegrable, f] using hvertical
  have hlimit := MeasureTheory.intervalIntegral_tendsto_integral hraw
    tendsto_neg_atTop_atBot tendsto_id
  have hnormalized := hlimit.const_mul (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  change Tendsto
    (fun T : ℝ => (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
      ∫ t in (-T)..T, f t) atTop
    (𝓝 ((((2 * Real.pi : ℝ) : ℂ)⁻¹) * ∫ t : ℝ, f t))
  exact hnormalized

/-- The normalized truncated right edge converges to the complete `I_2`. -/
theorem tendsto_goldfeldContourIntegrand_truncated_vertical_two
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ} (hbeta : -1 < beta) (hx : 0 < x) :
    Tendsto
      (goldfeldTruncatedVerticalIntegral chi1 chi beta x 2)
      atTop
      (𝓝 (goldfeldVerticalIntegral chi1 chi beta x 2)) :=
  tendsto_goldfeldTruncatedVerticalIntegral_of_verticalIntegrable
    chi1 chi beta x 2
      (goldfeldContourIntegrand_two_verticalIntegrable
        chi1 chi hbeta hx)

/-- The normalized truncated left edge converges to the complete `I_(-1)`. -/
theorem tendsto_goldfeldContourIntegrand_truncated_vertical_neg_one
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (hq1 : 1 < q1) (hq1q : q1 ≤ q)
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ} (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (hx : 1 ≤ x) :
    Tendsto
      (goldfeldTruncatedVerticalIntegral chi1 chi beta x (-1))
      atTop
      (𝓝 (goldfeldVerticalIntegral chi1 chi beta x (-1))) :=
  tendsto_goldfeldTruncatedVerticalIntegral_of_verticalIntegrable
    chi1 chi beta x (-1)
      (goldfeldContourIntegrand_leftLine_verticalIntegrable
        hq1 hq1q chi1 chi hchi1 hchi hcross hbeta0 hbeta1 hx)

/-- Goldfeld's complete contour displacement: the right line is the exact
shifted-zeta residue plus the upward left line. -/
theorem goldfeldVerticalIntegral_two_eq_residue_add_neg_one
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (hq1 : 1 < q1) (hq1q : q1 ≤ q)
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hx : 1 ≤ x)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    goldfeldVerticalIntegral chi1 chi beta x 2 =
      goldfeldContourResidue chi1 chi beta x +
        goldfeldVerticalIntegral chi1 chi beta x (-1) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hright := tendsto_goldfeldContourIntegrand_truncated_vertical_two
    chi1 chi (show -1 < beta by linarith) hxpos
  have hleft := tendsto_goldfeldContourIntegrand_truncated_vertical_neg_one
    hq1 hq1q chi1 chi hchi1 hchi hcross hbeta0 hbeta1.le hx
  obtain ⟨_A, _hA, _C, _hC, hhorizontal⟩ :=
    exists_tendsto_goldfeldContourIntegrand_horizontal_integrals_zero
  have hedges := hhorizontal q1 q hq1 hq1q chi1 chi
    hchi1 hchi hcross beta x hbeta0 hbeta1.le hx hzero
  have hlower : Tendsto
      (goldfeldTruncatedLowerIntegral chi1 chi beta x)
      atTop (𝓝 0) := by
    have h := hedges.2.const_mul
      ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹)
    change Tendsto (fun T : ℝ =>
      ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) *
        (-(∫ sigma in (-1)..2,
          goldfeldContourIntegrand chi1 chi beta x
            ((sigma : ℂ) - T * I)))) atTop (𝓝 0)
    simpa only [mul_zero] using h
  have hupper : Tendsto
      (goldfeldTruncatedUpperIntegral chi1 chi beta x)
      atTop (𝓝 0) := by
    have h := hedges.1.const_mul
      ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹)
    change Tendsto (fun T : ℝ =>
      ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) *
        ∫ sigma in (-1)..2,
          goldfeldContourIntegrand chi1 chi beta x
            ((sigma : ℂ) + T * I)) atTop (𝓝 0)
    simpa only [mul_zero] using h
  let rhs : ℝ → ℂ := fun T =>
    goldfeldTruncatedLowerIntegral chi1 chi beta x T +
      goldfeldTruncatedVerticalIntegral chi1 chi beta x (-1) T +
      goldfeldTruncatedUpperIntegral chi1 chi beta x T +
      goldfeldContourResidue chi1 chi beta x
  have hrhs : Tendsto rhs atTop
      (𝓝 (goldfeldVerticalIntegral chi1 chi beta x (-1) +
        goldfeldContourResidue chi1 chi beta x)) := by
    have hconstant : Tendsto
        (fun _ : ℝ => goldfeldContourResidue chi1 chi beta x) atTop
        (𝓝 (goldfeldContourResidue chi1 chi beta x)) :=
      tendsto_const_nhds
    have h := ((hlower.add hleft).add hupper).add hconstant
    simpa [rhs] using h
  have heq :
      (goldfeldTruncatedVerticalIntegral chi1 chi beta x 2) =ᶠ[atTop]
        rhs := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact goldfeldContourIntegrand_truncated_rectangle_decomposition
      chi1 chi hchi1 hchi hcross hbeta0 hbeta1 hxpos hT hzero
  have hright' := hright.congr' heq
  have hresult := tendsto_nhds_unique hright' hrhs
  simpa [add_comm] using hresult

/-- Source-facing form of the contour displacement after the already verified
Mellin inversion identity `S=I_2`. -/
theorem goldfeldSmoothedSum_eq_residue_add_verticalIntegral_neg_one
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (hq1 : 1 < q1) (hq1q : q1 ≤ q)
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hx : 1 ≤ x)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    goldfeldSmoothedSum chi1 chi beta x =
      goldfeldContourResidue chi1 chi beta x +
        goldfeldVerticalIntegral chi1 chi beta x (-1) := by
  rw [goldfeldSmoothedSum_eq_verticalIntegral_two
    chi1 chi (show -1 < beta by linarith) hx]
  exact goldfeldVerticalIntegral_two_eq_residue_add_neg_one
    hq1 hq1q chi1 chi hchi1 hchi hcross hbeta0 hbeta1 hx hzero

end

end BoundedGaps.Maynard
