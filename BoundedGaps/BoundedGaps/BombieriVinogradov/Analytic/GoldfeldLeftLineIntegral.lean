import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldLeftLineBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Goldfeld's complete left-line integral

The raw contour integrand is continuous and absolutely integrable on the
complete line `Re(s) = -1`.  Its normalized upward vertical integral has the
source-scale bound `C * q^A / x`.

Source: Koukoulopoulos, printed p. 126, proof of Theorem 12.9.
Semantic review: `SEM-558`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory

noncomputable section

private instance goldfeldLeftLineIntegralLcmNeZero
    {q1 q : ℕ} [NeZero q1] [NeZero q] : NeZero (Nat.lcm q1 q) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩

private theorem continuous_goldfeldContourIntegrand_leftLine
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1}
    {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ} (hbeta1 : beta ≤ 1) (hx : 0 < x) :
    Continuous (fun t : ℝ =>
      goldfeldContourIntegrand chi1 chi beta x
        ((-1 : ℂ) + t * I)) := by
  let s : ℝ → ℂ := fun t => (-1 : ℂ) + t * I
  have hs : Continuous s := by fun_prop
  have hs0 (t : ℝ) : s t ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  have hshift : Continuous (fun t : ℝ => s t + (beta : ℂ)) :=
    hs.add continuous_const
  have hshiftOne (t : ℝ) : s t + (beta : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    linarith
  have hzeta : Continuous (fun t : ℝ =>
      riemannZeta (s t + (beta : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hcomp :=
      (differentiableAt_riemannZeta (hshiftOne t)).continuousAt.comp
        (f := fun u : ℝ => s u + (beta : ℂ)) hshift.continuousAt
    simpa [Function.comp_def] using hcomp
  have hLchi1 : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction chi1 (s t + (beta : ℂ))) :=
    (DirichletCharacter.differentiable_LFunction hchi1).continuous.comp
      hshift
  have hLchi : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction chi (s t + (beta : ℂ))) :=
    (DirichletCharacter.differentiable_LFunction hchi).continuous.comp
      hshift
  have hLcross : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi)
        (s t + (beta : ℂ))) :=
    (DirichletCharacter.differentiable_LFunction hcross).continuous.comp
      hshift
  have hPhi : Continuous (fun t : ℝ =>
      goldfeldMellinContinuationData.Phi (s t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    simpa [Function.comp_def] using
      (goldfeldMellinContinuationData.analytic_off_zero
        (hs0 t)).continuousAt.comp hs.continuousAt
  have hxpow : Continuous (fun t : ℝ => (x : ℂ) ^ s t) :=
    continuous_const.cpow hs fun _ => Complex.ofReal_mem_slitPlane.mpr hx
  have hproduct :=
    (((((hzeta.mul hLchi1).mul hLchi).mul hLcross).mul hPhi).mul hxpow)
  convert hproduct using 1
  ext t
  simp [s, goldfeldContourIntegrand, goldfeldFourFactorLFunction]

private lemma goldfeld_leftLine_source_envelope_le_cauchy
    {q A : ℕ} {C x t y : ℝ}
    (hC : 0 ≤ C) (hx : 0 < x)
    (hy : y ≤ C * (q : ℝ) ^ A / (x * (1 + |t|) ^ 2)) :
    y ≤ (C * (q : ℝ) ^ A / x) * (1 + t ^ 2)⁻¹ := by
  let K : ℝ := C * (q : ℝ) ^ A / x
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hden : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
    nlinarith [sq_abs t, abs_nonneg t]
  have hinv : ((1 + |t|) ^ 2)⁻¹ ≤ (1 + t ^ 2)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 hden
  calc
    y ≤ C * (q : ℝ) ^ A / (x * (1 + |t|) ^ 2) := hy
    _ = K * ((1 + |t|) ^ 2)⁻¹ := by
      dsimp [K]
      field_simp
    _ ≤ K * (1 + t ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv hK

/-- The raw Goldfeld integrand is genuinely Bochner integrable on the full
upward line `Re(s) = -1`. -/
theorem goldfeldContourIntegrand_leftLine_verticalIntegrable
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (hq1 : 1 < q1) (hq1q : q1 ≤ q)
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ} (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (hx : 1 ≤ x) :
    VerticalIntegrable
      (goldfeldContourIntegrand chi1 chi beta x) (-1) := by
  obtain ⟨A, _hA, C, hC, hpoint⟩ :=
    exists_norm_goldfeldContourIntegrand_leftLine_le
  let K : ℝ := C * (q : ℝ) ^ A / x
  have hmajor : Integrable (fun t : ℝ => K * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul K
  have hcontinuous := continuous_goldfeldContourIntegrand_leftLine
    hchi1 hchi hcross hbeta1 (zero_lt_one.trans_le hx)
  rw [VerticalIntegrable]
  refine hmajor.mono' ?_ ?_
  · simpa using hcontinuous.aestronglyMeasurable
  · filter_upwards [] with t
    have hp := hpoint q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
      beta x t hbeta0 hbeta1 hx
    have hcauchy := goldfeld_leftLine_source_envelope_le_cauchy
      hC.le (zero_lt_one.trans_le hx) hp
    simpa [K] using hcauchy

/-- The normalized complete left-line integral has Goldfeld's source scale
`O(q^A / x)`, with absolute witnesses chosen before all data. -/
theorem exists_norm_goldfeldVerticalIntegral_neg_one_le :
    ∃ A : ℕ, 57 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta x : ℝ),
            0 ≤ beta → beta ≤ 1 → 1 ≤ x →
            ‖goldfeldVerticalIntegral chi1 chi beta x (-1)‖ ≤
              C * (q : ℝ) ^ A / x := by
  obtain ⟨A, hA, C0, hC0, hpoint⟩ :=
    exists_norm_goldfeldContourIntegrand_leftLine_le
  let C : ℝ := C0 * Real.pi
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨A, hA, C, hC, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross
    beta x hbeta0 hbeta1 hx
  let f : ℝ → ℂ := fun t =>
    goldfeldContourIntegrand chi1 chi beta x
      (((-1 : ℝ) : ℂ) + t * I)
  let K : ℝ := C0 * (q : ℝ) ^ A / x
  have hvertical := goldfeldContourIntegrand_leftLine_verticalIntegrable
    hq1 hq1q chi1 chi hchi1 hchi hcross hbeta0 hbeta1 hx
  have hraw : Integrable f := by
    simpa [VerticalIntegrable, f] using hvertical
  have hmajor : Integrable (fun t : ℝ => K * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul K
  have hmajorPoint : ∀ t : ℝ, ‖f t‖ ≤ K * (1 + t ^ 2)⁻¹ := by
    intro t
    have hp := hpoint q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
      beta x t hbeta0 hbeta1 hx
    have hcauchy := goldfeld_leftLine_source_envelope_le_cauchy
      hC0.le (zero_lt_one.trans_le hx) hp
    simpa [f, K] using hcauchy
  have hnormIntegral : ‖∫ t : ℝ, f t‖ ≤ K * Real.pi := by
    calc
      ‖∫ t : ℝ, f t‖ ≤ ∫ t : ℝ, ‖f t‖ :=
        norm_integral_le_integral_norm f
      _ ≤ ∫ t : ℝ, K * (1 + t ^ 2)⁻¹ :=
        integral_mono_ae hraw.norm hmajor (ae_of_all _ hmajorPoint)
      _ = K * Real.pi := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq]
  have hcoefficient :
      ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    exact (inv_le_one₀ (by positivity : 0 < 2 * Real.pi)).2
      (by nlinarith [Real.two_le_pi])
  rw [goldfeldVerticalIntegral, norm_mul]
  calc
    ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ * ‖∫ t : ℝ, f t‖ ≤
        1 * (K * Real.pi) := by gcongr
    _ = C * (q : ℝ) ^ A / x := by
      dsimp [C, K]
      ring

end

end BoundedGaps.Maynard
