import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Goldfeld's smooth plateau and Mellin boundary

This file freezes the fixed smooth cutoff used in the proof of
Koukoulopoulos Theorem 12.9.  The cutoff is constructed independently with
Mathlib's smooth separation theorem.  Its restriction to the nonnegative
half-line is one on `[0, 1]`, takes values in `[0, 1]`, and vanishes from `2`
onwards.  The raw Mellin transform is only used on `Re(s) > 0`; continuation
and the vertical decay estimate are represented by the explicit contract below
and are kept separate from the later sum/integral interchange.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 73--74,
80, and 125--126.  Semantic review: `SEM-552`.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped ContDiff Topology

namespace BoundedGaps.Maynard

private noncomputable def goldfeldPlateauBump : ContDiffBump (1 / 2 : ℝ) :=
  ⟨1 / 2, 3 / 2, by norm_num, by norm_num⟩

/-- A fixed smooth extension of the plateau cutoff from Theorem 12.9. -/
noncomputable def goldfeldPlateau : ℝ → ℝ := goldfeldPlateauBump

theorem goldfeldPlateau_contDiff : ContDiff ℝ ∞ goldfeldPlateau := by
  simpa [goldfeldPlateau] using
    (goldfeldPlateauBump.contDiff : ContDiff ℝ ∞ (goldfeldPlateauBump : ℝ → ℝ))

theorem goldfeldPlateau_range : Set.range goldfeldPlateau ⊆ Icc 0 1 := by
  rintro _ ⟨y, rfl⟩
  exact ⟨goldfeldPlateauBump.nonneg, goldfeldPlateauBump.le_one⟩

theorem goldfeldPlateau_nonneg (y : ℝ) : 0 ≤ goldfeldPlateau y := by
  exact (goldfeldPlateau_range ⟨y, rfl⟩).1

theorem goldfeldPlateau_le_one (y : ℝ) : goldfeldPlateau y ≤ 1 := by
  exact (goldfeldPlateau_range ⟨y, rfl⟩).2

theorem goldfeldPlateau_eq_one {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    goldfeldPlateau y = 1 := by
  apply goldfeldPlateauBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  simp only [goldfeldPlateauBump]
  rw [abs_le]
  constructor <;> linarith

theorem goldfeldPlateau_eq_zero {y : ℝ} (hy : 2 ≤ y) :
    goldfeldPlateau y = 0 := by
  apply goldfeldPlateauBump.zero_of_le_dist
  rw [Real.dist_eq]
  simp only [goldfeldPlateauBump]
  rw [abs_of_nonneg (by linarith : 0 ≤ y - 1 / 2)]
  linarith

theorem goldfeldPlateau_hasCompactSupport :
    HasCompactSupport goldfeldPlateau := by
  simpa [goldfeldPlateau] using goldfeldPlateauBump.hasCompactSupport

private noncomputable def goldfeldPlateauComplex : ℝ → ℂ :=
  fun y => goldfeldPlateau y

/-- The raw Mellin transform, only used in its half-plane of convergence. -/
noncomputable def goldfeldRawMellin (s : ℂ) : ℂ :=
  mellin goldfeldPlateauComplex s

private lemma goldfeldPlateauComplex_locallyIntegrable :
    LocallyIntegrableOn goldfeldPlateauComplex (Ioi (0 : ℝ)) := by
  apply (Complex.continuous_ofReal.comp goldfeldPlateau_contDiff.continuous).continuousOn
    |>.locallyIntegrableOn measurableSet_Ioi

private lemma goldfeldPlateauComplex_isBigO_top :
    ∀ a : ℝ, goldfeldPlateauComplex =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  intro a
  refine Filter.Eventually.isBigO ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with y hy
  change ‖(goldfeldPlateau y : ℂ)‖ ≤ _
  rw [goldfeldPlateau_eq_zero hy.le]
  simp only [Complex.ofReal_zero, norm_zero]
  exact Real.rpow_nonneg (by linarith) _

private lemma goldfeldPlateauComplex_isBigO_zero :
    goldfeldPlateauComplex =O[nhdsWithin 0 (Ioi 0)] (fun _ : ℝ => (1 : ℝ)) := by
  refine Filter.Eventually.isBigO ?_
  filter_upwards [] with y
  change ‖(goldfeldPlateau y : ℂ)‖ ≤ 1
  calc
    ‖(goldfeldPlateau y : ℂ)‖ = |goldfeldPlateau y| := RCLike.norm_ofReal _
    _ = goldfeldPlateau y := abs_of_nonneg (goldfeldPlateau_nonneg y)
    _ ≤ 1 := goldfeldPlateau_le_one y

theorem goldfeldRawMellin_convergent {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent goldfeldPlateauComplex s := by
  refine mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := 0)
    goldfeldPlateauComplex_locallyIntegrable ?_ ?_ ?_ ?_
  · simpa using goldfeldPlateauComplex_isBigO_top (s.re + 1)
  · linarith
  · simpa using goldfeldPlateauComplex_isBigO_zero
  · linarith

theorem goldfeldRawMellin_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ goldfeldRawMellin s := by
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0)
    goldfeldPlateauComplex_locallyIntegrable ?_ ?_ ?_ ?_
  · simpa using goldfeldPlateauComplex_isBigO_top (s.re + 1)
  · linarith
  · simpa using goldfeldPlateauComplex_isBigO_zero
  · linarith

/-- The complex derivative of the real plateau. -/
noncomputable def goldfeldPlateauDerivativeComplex : ℝ → ℂ :=
  fun y => ((deriv goldfeldPlateau) y : ℂ)

/-- The derivative weight used after one Mellin integration by parts. -/
noncomputable def goldfeldMellinDerivativeWeight (y : ℝ) : ℂ :=
  (y : ℂ) * goldfeldPlateauDerivativeComplex y

theorem goldfeldPlateau_deriv_contDiff :
    ContDiff ℝ ∞ (deriv goldfeldPlateau) :=
  (contDiff_infty_iff_deriv.mp goldfeldPlateau_contDiff).2

private theorem goldfeldPlateau_deriv_hasCompactSupport :
    HasCompactSupport (deriv goldfeldPlateau) :=
  goldfeldPlateau_hasCompactSupport.deriv

theorem goldfeldPlateau_deriv_eq_zero_of_pos_of_lt_one
    {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    deriv goldfeldPlateau y = 0 := by
  have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 y := hasDerivAt_const y 1
  have h := hconst.congr_of_eventuallyEq
    (show (fun z : ℝ => goldfeldPlateau z) =ᶠ[𝓝 y] (fun _ => (1 : ℝ)) by
      filter_upwards [Ioo_mem_nhds hy0 hy1] with z hz
      exact goldfeldPlateau_eq_one hz.1.le hz.2.le)
  exact h.deriv

theorem goldfeldPlateau_deriv_eq_zero_of_two_lt
    {y : ℝ} (hy : 2 < y) : deriv goldfeldPlateau y = 0 := by
  have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 y := hasDerivAt_const y 0
  have h := hconst.congr_of_eventuallyEq
    (show (fun z : ℝ => goldfeldPlateau z) =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      exact goldfeldPlateau_eq_zero hz.le)
  exact h.deriv

private lemma goldfeldPlateauDerivativeComplex_locallyIntegrable :
    LocallyIntegrableOn goldfeldPlateauDerivativeComplex (Ioi (0 : ℝ)) := by
  have hcont : Continuous (deriv goldfeldPlateau) :=
    goldfeldPlateau_contDiff.continuous_deriv (by norm_num)
  exact (Complex.continuous_ofReal.comp hcont).continuousOn.locallyIntegrableOn
    (μ := volume) measurableSet_Ioi

private lemma goldfeldPlateauDerivativeComplex_isBigO_top :
    ∀ a : ℝ, goldfeldPlateauDerivativeComplex =O[atTop]
      (fun x : ℝ => x ^ (-a)) := by
  intro a
  refine Filter.Eventually.isBigO ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with y hy
  change ‖((deriv goldfeldPlateau) y : ℂ)‖ ≤ _
  rw [goldfeldPlateau_deriv_eq_zero_of_two_lt hy]
  simp only [Complex.ofReal_zero, norm_zero]
  exact Real.rpow_nonneg (by linarith) _

private lemma goldfeldPlateauDerivativeComplex_isBigO_zero :
    ∀ b : ℝ, goldfeldPlateauDerivativeComplex =O[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => x ^ (-b)) := by
  intro b
  refine Filter.Eventually.isBigO ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with y hy
  change ‖((deriv goldfeldPlateau) y : ℂ)‖ ≤ _
  rw [goldfeldPlateau_deriv_eq_zero_of_pos_of_lt_one hy.1 hy.2]
  simp only [Complex.ofReal_zero, norm_zero]
  exact Real.rpow_nonneg hy.1.le _

private theorem goldfeldPlateauDerivativeComplex_mellin_differentiableAt
    (s : ℂ) :
    DifferentiableAt ℂ (mellin goldfeldPlateauDerivativeComplex) s := by
  refine mellin_differentiableAt_of_isBigO_rpow
    (a := s.re + 1) (b := s.re - 1)
    goldfeldPlateauDerivativeComplex_locallyIntegrable ?_ ?_ ?_ ?_
  · simpa using goldfeldPlateauDerivativeComplex_isBigO_top (s.re + 1)
  · linarith
  · simpa using goldfeldPlateauDerivativeComplex_isBigO_zero (s.re - 1)
  · linarith

/-- Mellin transform of the derivative weight, shifted to expose the pole. -/
noncomputable def goldfeldDerivativeMellin (s : ℂ) : ℂ :=
  mellin goldfeldPlateauDerivativeComplex (s + 1)

theorem goldfeldDerivativeMellin_eq_weight (s : ℂ) :
    goldfeldDerivativeMellin s = mellin goldfeldMellinDerivativeWeight s := by
  unfold goldfeldDerivativeMellin goldfeldMellinDerivativeWeight
  rw [← mellin_cpow_smul]
  simp only [Complex.cpow_one, smul_eq_mul]

private theorem goldfeldDerivativeMellin_differentiableAt (s : ℂ) :
    DifferentiableAt ℂ goldfeldDerivativeMellin s := by
  exact (goldfeldPlateauDerivativeComplex_mellin_differentiableAt (s + 1)).comp s
    ((hasDerivAt_id' s).add_const 1).differentiableAt

/-- The derivative Mellin transform is entire. -/
theorem differentiable_goldfeldDerivativeMellin :
    Differentiable ℂ goldfeldDerivativeMellin :=
  fun s => goldfeldDerivativeMellin_differentiableAt s

/-- The integration-by-parts candidate for the continued Mellin transform.
Lean totalizes division, so its value at `s = 0` is an irrelevant representative;
the punctured-limit theorem below records the meromorphic pole. -/
noncomputable def goldfeldMellinCandidate (s : ℂ) : ℂ :=
  -goldfeldDerivativeMellin s / s

/-- On its initial half-plane, the integration-by-parts candidate is the raw
Mellin integral. -/
theorem goldfeldMellinCandidate_eq_raw {s : ℂ} (hs : 0 < s.re) :
    goldfeldMellinCandidate s = goldfeldRawMellin s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    simp at hs
  let u : ℝ → ℂ := fun x => (x : ℂ) ^ s
  let v : ℝ → ℂ := goldfeldPlateauComplex
  let uD : ℝ → ℂ := fun x => s * (x : ℂ) ^ (s - 1)
  let vD : ℝ → ℂ := fun x => Complex.ofReal ((deriv goldfeldPlateau) x)
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u (uD x) x := by
    intro x hx
    exact hasDerivAt_ofReal_cpow_const hx.ne' hs0
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v (vD x) x := by
    intro x hx
    exact (goldfeldPlateau_contDiff.differentiable (by simp)).differentiableAt
      |>.hasDerivAt.ofReal_comp
  have hvD_cont : Continuous vD := by
    exact Complex.continuous_ofReal.comp goldfeldPlateau_deriv_contDiff.continuous
  have hvD_compact : HasCompactSupport vD := by
    change HasCompactSupport (Complex.ofReal ∘ deriv goldfeldPlateau)
    exact goldfeldPlateau_deriv_hasCompactSupport.comp_left Complex.ofReal_zero
  have huvD : IntegrableOn (u * vD) (Ioi 0) := by
    apply Integrable.integrableOn
    exact ((Complex.continuous_ofReal_cpow_const hs).mul hvD_cont)
      |>.integrable_of_hasCompactSupport hvD_compact.mul_left
  have huDv : IntegrableOn (uD * v) (Ioi 0) := by
    have hm := goldfeldRawMellin_convergent hs
    rw [MellinConvergent] at hm
    change Integrable
      (fun x : ℝ => (s * (x : ℂ) ^ (s - 1)) * goldfeldPlateauComplex x)
      (volume.restrict (Ioi 0))
    simpa only [smul_eq_mul, mul_assoc] using hm.const_mul s
  have hzero : Tendsto (u * v) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hp : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc := (Complex.continuousAt_ofReal_cpow_const 0 s (Or.inl hs)).tendsto
      change Tendsto u (𝓝 0 ⊓ 𝓟 (Ioi 0)) (𝓝 0)
      simpa [u, Complex.zero_cpow hs0] using hc.mono_left inf_le_left
    have hv0 : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hphi0 : goldfeldPlateauComplex 0 = 1 := by
        change (goldfeldPlateau 0 : ℂ) = 1
        rw [goldfeldPlateau_eq_one (by norm_num) (by norm_num)]
        norm_num
      have hc : Tendsto goldfeldPlateauComplex (𝓝 (0 : ℝ))
          (𝓝 (goldfeldPlateauComplex 0)) :=
        (Complex.continuous_ofReal.comp goldfeldPlateau_contDiff.continuous)
          |>.continuousAt.tendsto
      change Tendsto v (𝓝 0 ⊓ 𝓟 (Ioi 0)) (𝓝 1)
      simpa [v, hphi0] using hc.mono_left inf_le_left
    change Tendsto (fun x => u x * v x) (𝓝[>] (0 : ℝ)) (𝓝 0)
    simpa using hp.mul hv0
  have hinfty : Tendsto (u * v) atTop (𝓝 0) := by
    have heq : u * v =ᶠ[atTop] 0 := by
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
      simp [Pi.mul_apply, v, goldfeldPlateauComplex, goldfeldPlateau_eq_zero hx]
    exact heq.tendsto
  have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := 0) hu hv huvD huDv hzero hinfty
  have hweight : mellin goldfeldMellinDerivativeWeight s =
      ∫ x : ℝ in Ioi 0, u x * vD x := by
    rw [mellin]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [goldfeldMellinDerivativeWeight, goldfeldPlateauDerivativeComplex,
      u, vD, smul_eq_mul]
    have hpow : (x : ℂ) ^ (s - 1) * (x : ℂ) = (x : ℂ) ^ s := by
      calc
        (x : ℂ) ^ (s - 1) * (x : ℂ) =
            (x : ℂ) ^ (s - 1) * (x : ℂ) ^ (1 : ℂ) := by
              rw [Complex.cpow_one]
        _ = (x : ℂ) ^ ((s - 1) + 1) :=
          (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')).symm
        _ = (x : ℂ) ^ s := by rw [sub_add_cancel]
    rw [← mul_assoc, hpow]
  have hraw : ∫ x : ℝ in Ioi 0, uD x * v x =
      s * ∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (s - 1) * goldfeldPlateauComplex x := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp [uD, v, mul_assoc]
  rw [hraw] at hibp
  rw [goldfeldMellinCandidate, goldfeldDerivativeMellin_eq_weight, hweight,
    goldfeldRawMellin, mellin]
  simp only [smul_eq_mul, zero_sub, sub_zero] at hibp ⊢
  rw [hibp]
  field_simp [hs0]

theorem goldfeldMellinCandidate_meromorphic :
    MeromorphicOn goldfeldMellinCandidate Set.univ := by
  have hJ : AnalyticOnNhd ℂ goldfeldDerivativeMellin Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (fun s => goldfeldDerivativeMellin_differentiableAt s)
  have hneg : AnalyticOnNhd ℂ (fun s : ℂ => -goldfeldDerivativeMellin s) Set.univ := by
    exact hJ.neg
  exact hneg.meromorphicOn.div analyticOnNhd_id.meromorphicOn

theorem goldfeldMellinCandidate_analyticAt {s : ℂ} (hs : s ≠ 0) :
    AnalyticAt ℂ goldfeldMellinCandidate s := by
  have hJ : AnalyticOnNhd ℂ goldfeldDerivativeMellin Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (fun z => goldfeldDerivativeMellin_differentiableAt z)
  have hneg : AnalyticOnNhd ℂ (fun z : ℂ => -goldfeldDerivativeMellin z) {0}ᶜ :=
    hJ.neg.mono (by intro z hz; exact Set.mem_univ z)
  have hdiv : AnalyticOnNhd ℂ goldfeldMellinCandidate {0}ᶜ := by
    change AnalyticOnNhd ℂ (fun z : ℂ => -goldfeldDerivativeMellin z / z) {0}ᶜ
    exact hneg.div (analyticOnNhd_id.mono (by intro z hz; exact Set.mem_univ z))
      (fun z hz => hz)
  exact hdiv s (by simp [hs])

private theorem goldfeldDerivativeMellin_zero :
    goldfeldDerivativeMellin 0 = -1 := by
  unfold goldfeldDerivativeMellin
  rw [show (0 : ℂ) + 1 = 1 by norm_num]
  rw [mellin]
  simp only [sub_self, cpow_zero, one_smul]
  have h := goldfeldPlateau_hasCompactSupport.integral_Ioi_deriv_eq
    (goldfeldPlateau_contDiff.of_le (by norm_num)) (0 : ℝ)
  unfold goldfeldPlateauDerivativeComplex
  change (∫ t : ℝ in Ioi 0, ((deriv goldfeldPlateau t : ℝ) : ℂ)) = -1
  have hcast := (integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun t : ℝ => (deriv goldfeldPlateau) t))
  calc
    (∫ t : ℝ in Ioi 0, (((deriv goldfeldPlateau) t : ℝ) : ℂ)) =
        Complex.ofReal (∫ t : ℝ in Ioi 0, (deriv goldfeldPlateau) t) := by
          exact hcast
    _ = -Complex.ofReal (goldfeldPlateau 0) := by
      simpa using congrArg Complex.ofReal h
    _ = -1 := by
      rw [goldfeldPlateau_eq_one (by norm_num) (by norm_num)]
      norm_num

theorem goldfeldMellinCandidate_residue :
    Tendsto (fun s => s * goldfeldMellinCandidate s) (𝓝[≠] 0) (𝓝 1) := by
  have hcont : Tendsto goldfeldDerivativeMellin (𝓝 0) (𝓝 (-(1 : ℂ))) := by
    have hc := (goldfeldDerivativeMellin_differentiableAt 0).continuousAt
    change Tendsto goldfeldDerivativeMellin (𝓝 0)
      (𝓝 (goldfeldDerivativeMellin 0)) at hc
    simpa only [goldfeldDerivativeMellin_zero] using hc
  have hpunct : Tendsto (fun s : ℂ => s * goldfeldMellinCandidate s)
      (𝓝[≠] 0) (𝓝 (1 : ℂ)) := by
    have heq : (fun s : ℂ => s * goldfeldMellinCandidate s) =ᶠ[𝓝[≠] 0]
        (fun s => -goldfeldDerivativeMellin s) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [goldfeldMellinCandidate]
      calc
        s * (-goldfeldDerivativeMellin s / s) =
            (-goldfeldDerivativeMellin s) * s / s := by ring
        _ = -goldfeldDerivativeMellin s := mul_div_cancel_right₀ _ hs
    have hneg : Tendsto (fun s : ℂ => -goldfeldDerivativeMellin s)
        (𝓝[≠] 0) (𝓝 (1 : ℂ)) := by
      simpa using ((hcont.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)).neg)
    exact hneg.congr' heq.symm
  exact hpunct

/-! The source-facing continuation is packaged as explicit data.  The companion
Schwartz/Fourier module supplies the fixed-line decay field. -/

/-- A total-function presentation of the meromorphic continuation.  The value
of `Phi` at zero is only Lean's totalized representative; `meromorphic`,
`analytic_off_zero`, and `residue_one` carry the source pole semantics. -/
structure GoldfeldMellinContinuationData where
  Phi : ℂ → ℂ
  agrees_on_right : ∀ {s : ℂ}, 0 < s.re → Phi s = goldfeldRawMellin s
  equals_candidate : ∀ s, Phi s = goldfeldMellinCandidate s
  meromorphic : MeromorphicOn Phi Set.univ
  analytic_off_zero : ∀ {s : ℂ}, s ≠ 0 → AnalyticAt ℂ Phi s
  residue_one : Tendsto (fun s => s * Phi s) (𝓝[≠] 0) (𝓝 1)
  decay_on_neg_one : ∀ (A : ℕ), 1 ≤ A →
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖Phi ((-1 : ℂ) + t * I)‖ ≤ C / (1 + |t|) ^ A

noncomputable def goldfeldMellinContinuationData_of_decay
    (hdecay : ∀ (A : ℕ), 1 ≤ A → ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖goldfeldMellinCandidate ((-1 : ℂ) + t * I)‖ ≤ C / (1 + |t|) ^ A) :
    GoldfeldMellinContinuationData := by
  exact
    { Phi := goldfeldMellinCandidate
      agrees_on_right := fun hs => goldfeldMellinCandidate_eq_raw hs
      equals_candidate := fun _ => rfl
      meromorphic := goldfeldMellinCandidate_meromorphic
      analytic_off_zero := fun hs => goldfeldMellinCandidate_analyticAt hs
      residue_one := goldfeldMellinCandidate_residue
      decay_on_neg_one := hdecay }

end BoundedGaps.Maynard
