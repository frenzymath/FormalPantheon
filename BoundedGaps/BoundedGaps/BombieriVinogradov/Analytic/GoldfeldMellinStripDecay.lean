import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldPlateauMellinDecay
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Uniform Mellin decay on Goldfeld's contour strip

The logarithmic Mellin kernel has one fixed compact support for every real
part in `[-1,2]`.  Leibniz bounds its derivatives uniformly in that parameter,
and the Fourier derivative identity gives arbitrary high-ordinate decay.

Source: Koukoulopoulos, printed pp. 73--74, equations (7.6)--(7.7), and
printed p. 80, Exercise 7.2(c). Semantic review: `SEM-556`.
-/

noncomputable section

open Complex Set MeasureTheory Filter Real
open scoped ContDiff Topology SchwartzMap FourierTransform RealInnerProductSpace

namespace BoundedGaps.Maynard

private theorem iteratedDeriv_real_smul
    (n : ℕ) (f : ℝ → ℝ) (g : ℝ → ℂ) (u : ℝ)
    (hf : ContDiffAt ℝ n f u) (hg : ContDiffAt ℝ n g u) :
    iteratedDeriv n (f • g) u = ∑ i ∈ Finset.range (n + 1),
      n.choose i • iteratedDeriv i f u • iteratedDeriv (n - i) g u := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_smul (Set.mem_univ u) uniqueDiffOn_univ
      hf.contDiffWithinAt hg.contDiffWithinAt

private noncomputable def baseKernel (u : ℝ) : ℂ :=
  goldfeldMellinDerivativeWeight (Real.exp (-u))

private noncomputable def stripKernel (sigma u : ℝ) : ℂ :=
  Real.exp (-sigma * u) • baseKernel u

private theorem weight_contDiff :
    ContDiff ℝ ∞ goldfeldMellinDerivativeWeight := by
  have hd : ContDiff ℝ ∞ goldfeldPlateauDerivativeComplex :=
    Complex.ofRealCLM.contDiff.comp goldfeldPlateau_deriv_contDiff
  unfold goldfeldMellinDerivativeWeight
  exact (Complex.ofRealCLM.contDiff.comp contDiff_id).mul hd

private theorem base_contDiff : ContDiff ℝ ∞ baseKernel := by
  unfold baseKernel
  exact weight_contDiff.comp (contDiff_id.neg.exp)

private theorem strip_contDiff (sigma : ℝ) :
    ContDiff ℝ ∞ (stripKernel sigma) := by
  unfold stripKernel
  exact (contDiff_const.mul contDiff_id).exp.smul base_contDiff

private theorem base_eq_zero_of_pos {u : ℝ} (hu : 0 < u) :
    baseKernel u = 0 := by
  have harg : 0 < Real.exp (-u) := Real.exp_pos _
  have hlt : Real.exp (-u) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hd := goldfeldPlateau_deriv_eq_zero_of_pos_of_lt_one harg hlt
  simp [baseKernel, goldfeldMellinDerivativeWeight,
    goldfeldPlateauDerivativeComplex, hd]

private theorem base_eq_zero_of_lt_neg_log_two
    {u : ℝ} (hu : u < -Real.log 2) : baseKernel u = 0 := by
  have harg : 0 < Real.exp (-u) := Real.exp_pos _
  have hlog : Real.log 2 < -u := by linarith
  have hgt : 2 < Real.exp (-u) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact (Real.exp_lt_exp).2 hlog
  have hd := goldfeldPlateau_deriv_eq_zero_of_two_lt hgt
  simp [baseKernel, goldfeldMellinDerivativeWeight,
    goldfeldPlateauDerivativeComplex, hd]

private theorem base_support_subset :
    Function.support baseKernel ⊆ Icc (-Real.log 2) 0 := by
  intro u hu
  by_contra hnot
  have hcases : u < -Real.log 2 ∨ 0 < u := by
    by_cases hleft : u < -Real.log 2
    · exact Or.inl hleft
    · have hleft' : -Real.log 2 ≤ u := le_of_not_gt hleft
      by_cases hright : 0 < u
      · exact Or.inr hright
      · exact False.elim (hnot ⟨hleft', le_of_not_gt hright⟩)
  rcases hcases with hleft | hright
  · exact hu (base_eq_zero_of_lt_neg_log_two hleft)
  · exact hu (base_eq_zero_of_pos hright)

private theorem base_hasCompactSupport : HasCompactSupport baseKernel := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Icc (-Real.log 2) 0) isCompact_Icc
  exact base_support_subset

private noncomputable def baseSchwartz : 𝓢(ℝ, ℂ) :=
  base_hasCompactSupport.toSchwartzMap base_contDiff

private theorem stripKernel_fourier (sigma t : ℝ) :
    goldfeldDerivativeMellin ((sigma : ℂ) + t * I) =
      𝓕 (stripKernel sigma) (t / (2 * π)) := by
  calc
    goldfeldDerivativeMellin ((sigma : ℂ) + t * I) =
        mellin goldfeldMellinDerivativeWeight ((sigma : ℂ) + t * I) :=
      goldfeldDerivativeMellin_eq_weight _
    _ = 𝓕 (fun u : ℝ =>
        Real.exp (-((sigma : ℂ) + t * I).re * u) •
          goldfeldMellinDerivativeWeight (Real.exp (-u)))
        (((sigma : ℂ) + t * I).im / (2 * π)) :=
      mellin_eq_fourier goldfeldMellinDerivativeWeight
    _ = 𝓕 (stripKernel sigma) (t / (2 * π)) := by
      norm_num
      apply congrArg (fun f : ℝ → ℂ => 𝓕 f (t / (2 * π)))
      funext u
      simp [stripKernel, baseKernel]

private theorem iteratedDeriv_base_eq_zero_of_not_mem
    (n : ℕ) {u : ℝ} (hu : u ∉ Icc (-Real.log 2) 0) :
    iteratedDeriv n baseKernel u = 0 := by
  have hcases : u < -Real.log 2 ∨ 0 < u := by
    by_cases hleft : u < -Real.log 2
    · exact Or.inl hleft
    · right
      have hleft' : -Real.log 2 ≤ u := le_of_not_gt hleft
      by_contra hnot
      exact hu ⟨hleft', le_of_not_gt hnot⟩
  rcases hcases with hleft | hright
  · have heq : Set.EqOn baseKernel 0 (Iio (-Real.log 2)) := by
      intro v hv
      exact base_eq_zero_of_lt_neg_log_two hv
    have h := heq.iteratedDeriv_of_isOpen isOpen_Iio n hleft
    simpa using h
  · have heq : Set.EqOn baseKernel 0 (Ioi 0) := by
      intro v hv
      exact base_eq_zero_of_pos hv
    have h := heq.iteratedDeriv_of_isOpen isOpen_Ioi n hright
    simpa using h

private theorem norm_iteratedDeriv_base_le_seminorm (n : ℕ) (u : ℝ) :
    ‖iteratedDeriv n baseKernel u‖ ≤
      SchwartzMap.seminorm ℝ 0 n baseSchwartz := by
  have h := SchwartzMap.le_seminorm' ℝ 0 n baseSchwartz u
  change ‖iteratedDeriv n (baseSchwartz : ℝ → ℂ) u‖ ≤
    SchwartzMap.seminorm ℝ 0 n baseSchwartz
  simpa using h

private theorem expFactor_iteratedDeriv (sigma : ℝ) (n : ℕ) :
    iteratedDeriv n (fun u : ℝ => Real.exp (-sigma * u)) =
      fun u => (-sigma) ^ n * Real.exp (-sigma * u) := by
  simpa only [neg_mul] using iteratedDeriv_exp_const_mul n (-sigma)

private theorem expFactor_le_four
    {sigma u : ℝ} (hsigma : sigma ∈ Icc (-(1 : ℝ)) 2)
    (hu : u ∈ Icc (-Real.log 2) 0) :
    Real.exp (-sigma * u) ≤ 4 := by
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsigmaAbs : |sigma| ≤ 2 :=
    (abs_le).2 ⟨by linarith [hsigma.1], hsigma.2⟩
  have huAbs : |u| ≤ Real.log 2 := by
    rw [abs_of_nonpos hu.2]
    linarith [hu.1]
  have hprod : |sigma * u| ≤ 2 * Real.log 2 := by
    rw [abs_mul]
    exact mul_le_mul hsigmaAbs huAbs (abs_nonneg u) (by norm_num)
  have harg : -sigma * u ≤ 2 * Real.log 2 := by
    calc
      -sigma * u = -(sigma * u) := by ring
      _ ≤ |sigma * u| := neg_le_abs _
      _ ≤ 2 * Real.log 2 := hprod
  calc
    Real.exp (-sigma * u) ≤ Real.exp (2 * Real.log 2) :=
      Real.exp_le_exp.mpr harg
    _ = 4 := by
      rw [show (2 : ℝ) * Real.log 2 = Real.log 2 + Real.log 2 by ring,
        Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num

private theorem norm_iteratedDeriv_stripKernel_le
    (n : ℕ) {sigma : ℝ} (hsigma : sigma ∈ Icc (-(1 : ℝ)) 2)
    (u : ℝ) :
    ‖iteratedDeriv n (stripKernel sigma) u‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * 2 ^ i * 4 *
          SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz := by
  by_cases hu : u ∈ Icc (-Real.log 2) 0
  · rw [show stripKernel sigma =
        (fun u : ℝ => Real.exp (-sigma * u)) • baseKernel by rfl]
    have hExp : ContDiffAt ℝ n (fun u : ℝ => Real.exp (-sigma * u)) u :=
      (contDiff_const.mul contDiff_id).exp.contDiffAt.of_le (by
        exact_mod_cast le_top)
    have hBase : ContDiffAt ℝ n baseKernel u :=
      base_contDiff.contDiffAt.of_le (by exact_mod_cast le_top)
    rw [iteratedDeriv_real_smul n _ _ u hExp hBase]
    calc
      ‖∑ i ∈ Finset.range (n + 1),
          n.choose i •
            iteratedDeriv i (fun u : ℝ => Real.exp (-sigma * u)) u •
              iteratedDeriv (n - i) baseKernel u‖ ≤
          ∑ i ∈ Finset.range (n + 1),
            ‖n.choose i •
              iteratedDeriv i (fun u : ℝ => Real.exp (-sigma * u)) u •
                iteratedDeriv (n - i) baseKernel u‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * 2 ^ i * 4 *
            SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz := by
        apply Finset.sum_le_sum
        intro i hi
        rw [expFactor_iteratedDeriv]
        rw [RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul,
          norm_smul, Real.norm_eq_abs]
        have hsigmaPow : |(-sigma) ^ i| ≤ (2 : ℝ) ^ i := by
          rw [abs_pow, abs_neg]
          exact pow_le_pow_left₀ (abs_nonneg sigma) (by
            exact (abs_le).2 ⟨by linarith [hsigma.1], hsigma.2⟩) i
        have hexp := expFactor_le_four hsigma hu
        have hbase := norm_iteratedDeriv_base_le_seminorm (n - i) u
        have hchoose : 0 ≤ (n.choose i : ℝ) := by positivity
        have hpow : 0 ≤ (2 : ℝ) ^ i := by positivity
        have hseminorm : 0 ≤ SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz :=
          by positivity
        rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
        change (n.choose i : ℝ) *
            (|(-sigma) ^ i| * Real.exp (-sigma * u) *
              ‖iteratedDeriv (n - i) baseKernel u‖) ≤ _
        calc
          (n.choose i : ℝ) *
                (|(-sigma) ^ i| * Real.exp (-sigma * u) *
                  ‖iteratedDeriv (n - i) baseKernel u‖) ≤
              (n.choose i : ℝ) *
                ((2 : ℝ) ^ i * 4 *
                  SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz) := by
            gcongr
          _ = (n.choose i : ℝ) * 2 ^ i * 4 *
              SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz := by ring
  · have hzero : iteratedDeriv n (stripKernel sigma) u = 0 := by
      rw [show stripKernel sigma =
        (fun u : ℝ => Real.exp (-sigma * u)) • baseKernel by rfl]
      have hExp : ContDiffAt ℝ n (fun u : ℝ => Real.exp (-sigma * u)) u :=
        (contDiff_const.mul contDiff_id).exp.contDiffAt.of_le (by
          exact_mod_cast le_top)
      have hBase : ContDiffAt ℝ n baseKernel u :=
        base_contDiff.contDiffAt.of_le (by exact_mod_cast le_top)
      rw [iteratedDeriv_real_smul n _ _ u hExp hBase]
      apply Finset.sum_eq_zero
      intro i hi
      rw [iteratedDeriv_base_eq_zero_of_not_mem (n - i) hu]
      simp
    rw [hzero, norm_zero]
    positivity

private theorem strip_hasCompactSupport (sigma : ℝ) :
    HasCompactSupport (stripKernel sigma) := by
  change HasCompactSupport
    ((fun u : ℝ => Real.exp (-sigma * u)) • baseKernel)
  exact base_hasCompactSupport.smul_left

private theorem hasCompactSupport_iteratedDeriv
    {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∀ n : ℕ, HasCompactSupport (iteratedDeriv n f)
  | 0 => by simpa using hf
  | n + 1 => by
      rw [iteratedDeriv_succ]
      exact (hasCompactSupport_iteratedDeriv hf n).deriv

private theorem integrable_iteratedDeriv_stripKernel
    (sigma : ℝ) (n : ℕ) :
    Integrable (iteratedDeriv n (stripKernel sigma)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (strip_contDiff sigma).continuous_iteratedDeriv n (by
      exact_mod_cast le_top)
  · exact hasCompactSupport_iteratedDeriv (strip_hasCompactSupport sigma) n

private theorem iteratedDeriv_stripKernel_eq_zero_of_not_mem
    (n : ℕ) (sigma : ℝ) {u : ℝ}
    (hu : u ∉ Icc (-Real.log 2) 0) :
    iteratedDeriv n (stripKernel sigma) u = 0 := by
  rw [show stripKernel sigma =
    (fun u : ℝ => Real.exp (-sigma * u)) • baseKernel by rfl]
  have hExp : ContDiffAt ℝ n (fun u : ℝ => Real.exp (-sigma * u)) u :=
    (contDiff_const.mul contDiff_id).exp.contDiffAt.of_le (by
      exact_mod_cast le_top)
  have hBase : ContDiffAt ℝ n baseKernel u :=
    base_contDiff.contDiffAt.of_le (by exact_mod_cast le_top)
  rw [iteratedDeriv_real_smul n _ _ u hExp hBase]
  apply Finset.sum_eq_zero
  intro i hi
  rw [iteratedDeriv_base_eq_zero_of_not_mem (n - i) hu]
  simp

private theorem integral_norm_iteratedDeriv_stripKernel_le
    (n : ℕ) {sigma : ℝ} (hsigma : sigma ∈ Icc (-(1 : ℝ)) 2) :
    ∫ u : ℝ, ‖iteratedDeriv n (stripKernel sigma) u‖ ≤
      (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * 2 ^ i * 4 *
          SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz) * Real.log 2 := by
  let M : ℝ := ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * 2 ^ i * 4 *
      SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hsupport : (fun u : ℝ => ‖iteratedDeriv n (stripKernel sigma) u‖) =
      (Icc (-Real.log 2) 0).indicator
        (fun u : ℝ => ‖iteratedDeriv n (stripKernel sigma) u‖) := by
    funext u
    by_cases hu : u ∈ Icc (-Real.log 2) 0
    · simp [hu]
    · rw [iteratedDeriv_stripKernel_eq_zero_of_not_mem n sigma hu]
      simp [hu]
  rw [hsupport, integral_indicator measurableSet_Icc]
  calc
    (∫ u : ℝ in Icc (-Real.log 2) 0,
        ‖iteratedDeriv n (stripKernel sigma) u‖) ≤
        ∫ _u : ℝ in Icc (-Real.log 2) 0, M := by
      apply setIntegral_mono_on
      · exact (integrable_iteratedDeriv_stripKernel sigma n).norm.integrableOn
      · apply integrableOn_const
        · exact ne_of_lt isCompact_Icc.measure_lt_top
        · finiteness
      · exact measurableSet_Icc
      · intro u hu
        simpa [M] using norm_iteratedDeriv_stripKernel_le n hsigma u
    _ = M * Real.log 2 := by
      rw [setIntegral_const, Measure.real, Real.volume_Icc]
      rw [show 0 - -Real.log 2 = Real.log 2 by ring]
      rw [ENNReal.toReal_ofReal (Real.log_nonneg (by norm_num))]
      simp [smul_eq_mul, mul_comm]
    _ = (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * 2 ^ i * 4 *
          SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz) * Real.log 2 := rfl

private theorem abs_pow_mul_norm_fourier_stripKernel_le
    (n : ℕ) {sigma : ℝ} (hsigma : sigma ∈ Icc (-(1 : ℝ)) 2)
    (t : ℝ) :
    |t| ^ n * ‖𝓕 (stripKernel sigma) (t / (2 * π))‖ ≤
      (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * 2 ^ i * 4 *
          SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz) * Real.log 2 := by
  let xi : ℝ := t / (2 * π)
  have hFourier := congrFun
    (Real.fourier_iteratedDeriv (N := n)
      ((strip_contDiff sigma).of_le (by exact_mod_cast le_top))
      (fun m _hm => integrable_iteratedDeriv_stripKernel sigma m)
      (n := n) (by rfl)) xi
  have hfreq : ‖(2 * (π : ℂ) * I * (xi : ℂ))‖ = |t| := by
    have hcoeff : 2 * (π : ℂ) * I * (xi : ℂ) = (t : ℂ) * I := by
      dsimp [xi]
      push_cast
      field_simp [Real.pi_ne_zero]
    rw [hcoeff, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
  calc
    |t| ^ n * ‖𝓕 (stripKernel sigma) (t / (2 * π))‖ =
        ‖(2 * (π : ℂ) * I * (xi : ℂ)) ^ n •
          𝓕 (stripKernel sigma) xi‖ := by
      rw [norm_smul, norm_pow, hfreq]
    _ = ‖𝓕 (iteratedDeriv n (stripKernel sigma)) xi‖ := by
      rw [hFourier]
    _ ≤ ∫ u : ℝ, ‖iteratedDeriv n (stripKernel sigma) u‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm
        𝐞 volume (innerₗ ℝ) (iteratedDeriv n (stripKernel sigma)) xi
    _ ≤ (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * 2 ^ i * 4 *
          SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz) * Real.log 2 :=
      integral_norm_iteratedDeriv_stripKernel_le n hsigma

/-- The continued Mellin candidate decays to every prescribed natural order,
with one constant uniform over the complete closed contour strip. -/
theorem goldfeldMellinCandidate_decay_on_closedStrip
    (A : ℕ) (_hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ sigma t : ℝ, sigma ∈ Icc (-(1 : ℝ)) 2 →
        1 ≤ |t| →
          ‖goldfeldMellinCandidate ((sigma : ℂ) + t * I)‖ ≤
            C / (1 + |t|) ^ A := by
  let M : ℝ := (∑ i ∈ Finset.range (A + 1),
    (A.choose i : ℝ) * 2 ^ i * 4 *
      SchwartzMap.seminorm ℝ 0 (A - i) baseSchwartz) * Real.log 2
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  let C : ℝ := (M + 1) * 2 ^ A
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro sigma t hsigma ht
  let s : ℂ := (sigma : ℂ) + t * I
  have htpos : 0 < |t| := zero_lt_one.trans_le ht
  have hsNorm : (1 : ℝ) ≤ ‖s‖ := by
    have him := Complex.abs_im_le_norm s
    have him' : |t| ≤ ‖s‖ := by simpa [s] using him
    exact ht.trans him'
  have hcandidate :
      ‖goldfeldMellinCandidate s‖ ≤ ‖goldfeldDerivativeMellin s‖ := by
    rw [goldfeldMellinCandidate, norm_div, norm_neg]
    exact div_le_self (norm_nonneg _) hsNorm
  have hfourier :
      ‖goldfeldDerivativeMellin s‖ =
        ‖𝓕 (stripKernel sigma) (t / (2 * π))‖ := by
    rw [stripKernel_fourier]
  have hpow := abs_pow_mul_norm_fourier_stripKernel_le A hsigma t
  have hfourierDecay :
      ‖𝓕 (stripKernel sigma) (t / (2 * π))‖ ≤ M / |t| ^ A := by
    apply (le_div_iff₀ (pow_pos htpos A)).2
    simpa [M, mul_comm] using hpow
  have hscale : 1 + |t| ≤ 2 * |t| := by linarith
  have hpowscale : (1 + |t|) ^ A ≤ (2 * |t|) ^ A :=
    pow_le_pow_left₀ (by positivity) hscale A
  have hconvert : M / |t| ^ A ≤ C / (1 + |t|) ^ A := by
    apply (div_le_div_iff₀ (pow_pos htpos A) (by positivity)).2
    calc
      M * (1 + |t|) ^ A ≤ M * (2 * |t|) ^ A :=
        mul_le_mul_of_nonneg_left hpowscale hM
      _ ≤ (M + 1) * (2 * |t|) ^ A := by
        gcongr
        linarith
      _ = C * |t| ^ A := by
        dsimp [C]
        rw [mul_pow]
        ring
  calc
    ‖goldfeldMellinCandidate s‖ ≤ ‖goldfeldDerivativeMellin s‖ := hcandidate
    _ = ‖𝓕 (stripKernel sigma) (t / (2 * π))‖ := hfourier
    _ ≤ M / |t| ^ A := hfourierDecay
    _ ≤ C / (1 + |t|) ^ A := hconvert

/-- The source-facing continuation package inherits the uniform closed-strip
decay of its explicit candidate. -/
theorem goldfeldMellinContinuation_decay_on_closedStrip
    (A : ℕ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ sigma t : ℝ, sigma ∈ Icc (-(1 : ℝ)) 2 →
        1 ≤ |t| →
          ‖goldfeldMellinContinuationData.Phi
              ((sigma : ℂ) + t * I)‖ ≤
            C / (1 + |t|) ^ A := by
  obtain ⟨C, hC, hbound⟩ :=
    goldfeldMellinCandidate_decay_on_closedStrip A hA
  refine ⟨C, hC, ?_⟩
  intro sigma t hsigma ht
  rw [goldfeldMellinContinuationData.equals_candidate]
  exact hbound sigma t hsigma ht

end BoundedGaps.Maynard
