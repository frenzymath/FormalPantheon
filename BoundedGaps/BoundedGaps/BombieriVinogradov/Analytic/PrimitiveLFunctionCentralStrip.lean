import BoundedGaps.BombieriVinogradov.Analytic.DirichletLFunctionAbelContinuation
import BoundedGaps.BombieriVinogradov.Analytic.VaughanSecondTermPolyaVinogradov

/-!
# Primitive Dirichlet L-functions in the central strip

For a primitive character of level greater than one, this file continues the
Abel integral for its Dirichlet series to the positive half-plane and derives
a coarse explicit bound on `1 / 2 ≤ re s ≤ 2`.

Sources: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 110 for
conditional convergence, printed p. 113 for Lemma 11.2 and its proof, printed
p. 13 for partial summation (1.8)--(1.9), and printed pp. 106--107 for the
Polya--Vinogradov inequality, Theorem 10.6. Semantic review: `SEM-474`.
-/

open Asymptotics Complex Filter MeasureTheory Set
open scoped BigOperators Real Topology

namespace BoundedGaps.Maynard

private lemma polyaVinogradovScale_pos {q : ℕ} (hq : 1 < q) :
    0 < Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  exact mul_pos
    (Real.sqrt_pos.2 (by exact_mod_cast Nat.zero_lt_of_lt hq))
    (Real.log_pos (by exact_mod_cast hq))

/-- A primitive character of modulus greater than one is nonprincipal. -/
theorem character_ne_one_of_isPrimitive
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive) : chi ≠ 1 := by
  intro heq
  have hc : chi.conductor = 1 :=
    DirichletCharacter.eq_one_iff_conductor_eq_one.mp heq
  have hp : chi.conductor = q := hchi
  omega

/-- The conditionally convergent character series represented by its Abel
integral throughout the positive half-plane. The equality is first obtained
in the half-plane of absolute convergence and then continued analytically.
See printed p. 110, partial summation (1.8)--(1.9) on p. 13, and Theorem 10.6
on pp. 106--107, whose project implementation is reviewed in `SEM-438`. -/
theorem LFunction_eq_abelIntegral_of_isPrimitive
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (s : ℂ) (hs : 0 < s.re) :
    DirichletCharacter.LFunction chi s =
      s * ∫ y in Set.Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1)) := by
  simpa [dirichletCharacterIntervalSum] using
    LFunction_eq_abelIntegral_of_prefixBound chi
      (character_ne_one_of_isPrimitive hq chi hchi)
      (Real.sqrt (q : ℝ) * Real.log (q : ℝ))
      (fun n ↦ by
        simpa [dirichletCharacterIntervalSum] using
          (norm_dirichletCharacterIntervalSum_lt_sqrt_mul_log
            hq chi hchi 1 n).le)
      s hs

private lemma norm_characterAbelIntegral_le
    {q : ℕ} (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {s : ℂ} (hs : 0 < s.re) :
    ‖∫ y in Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))‖ ≤
      (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) / s.re := by
  have hPower : IntegrableOn
      (fun y : ℝ ↦ y ^ (-(s.re + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hScale : 0 ≤ Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
    (polyaVinogradovScale_pos hq).le
  have hDom : IntegrableOn
      (fun y : ℝ ↦
        (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
          y ^ (-(s.re + 1))) (Ioi 1) :=
    hPower.const_mul _
  have hActualMeasurable : AEStronglyMeasurable
      (fun y : ℝ ↦
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))) (volume.restrict (Ioi 1)) := by
    have hPrefix : Measurable
        (fun y : ℝ ↦ dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi) :=
      (measurable_of_countable
        (fun n : ℕ ↦ dirichletCharacterIntervalSum 1 n q chi)).comp
        Nat.measurable_floor
    have hCpow : ContinuousOn
        (fun y : ℝ ↦ (y : ℂ) ^ (-(s + 1))) (Ioi 1) :=
      continuousOn_of_forall_continuousAt fun y hy ↦
        continuousAt_ofReal_cpow_const y (-(s + 1))
          (Or.inr (zero_lt_one.trans hy).ne')
    exact hPrefix.aestronglyMeasurable.mul
      (hCpow.aestronglyMeasurable measurableSet_Ioi)
  have hBound : ∀ᵐ (y : ℝ) ∂volume.restrict (Ioi 1),
      ‖dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))‖ ≤
        (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
          y ^ (-(s.re + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hy)]
    simp only [neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_right
      (norm_dirichletCharacterIntervalSum_lt_sqrt_mul_log
        hq chi hchi 1 ⌊y⌋₊).le
      (Real.rpow_nonneg (zero_lt_one.trans hy).le _)
  have hActual : IntegrableOn
      (fun y : ℝ ↦
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))) (Ioi 1) :=
    hDom.mono' hActualMeasurable hBound
  calc
    ‖∫ y in Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))‖ ≤
        ∫ y in Ioi (1 : ℝ),
          ‖dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
            (y : ℂ) ^ (-(s + 1))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioi (1 : ℝ),
          (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
            y ^ (-(s.re + 1)) :=
      setIntegral_mono_ae_restrict hActual.norm hDom hBound
    _ = (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
        ∫ y in Ioi (1 : ℝ), y ^ (-(s.re + 1)) := by
      rw [integral_const_mul]
    _ = (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) / s.re := by
      rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
      field_simp [hs.ne']
      ring

/-- A coarse explicit `j = 0` central-strip consequence of Lemma 11.2. The
source states a sharper bound with an implied constant; the literal factor
`2` here is derived from the global Polya--Vinogradov bound and strip limits. -/
theorem norm_LFunction_centralStrip_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {sigma t : ℝ} (hsigma_lower : (1 / 2 : ℝ) ≤ sigma)
    (hsigma_upper : sigma ≤ 2) :
    ‖DirichletCharacter.LFunction chi ((sigma : ℂ) + t * I)‖ ≤
      2 * (|t| + 2) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  let s : ℂ := (sigma : ℂ) + t * I
  have hsigma_pos : 0 < sigma := by linarith
  have hsre : s.re = sigma := by simp [s]
  have hspos : 0 < s.re := hsre.symm ▸ hsigma_pos
  have hscale : 0 ≤ Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
    (polyaVinogradovScale_pos hq).le
  have hnormS : ‖s‖ ≤ |t| + 2 := by
    calc
      ‖s‖ ≤ ‖(sigma : ℂ)‖ + ‖(t : ℂ) * I‖ := by
        simpa only [s] using norm_add_le (sigma : ℂ) ((t : ℂ) * I)
      _ = |sigma| + |t| := by simp [Real.norm_eq_abs]
      _ = sigma + |t| := by rw [abs_of_nonneg hsigma_pos.le]
      _ ≤ |t| + 2 := by linarith
  have hinv : 1 / sigma ≤ 2 := by
    apply (div_le_iff₀ hsigma_pos).2
    linarith
  have hquot :
      (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) / sigma ≤
        2 * (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) := by
    calc
      (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) / sigma =
          (1 / sigma) *
            (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) := by ring
      _ ≤ 2 * (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) :=
        mul_le_mul_of_nonneg_right hinv hscale
  have hIntegral := norm_characterAbelIntegral_le hq chi hchi hspos
  rw [hsre] at hIntegral
  change ‖DirichletCharacter.LFunction chi s‖ ≤ _
  calc
    ‖DirichletCharacter.LFunction chi s‖ =
        ‖s‖ *
          ‖∫ y in Ioi (1 : ℝ),
            dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
              (y : ℂ) ^ (-(s + 1))‖ := by
      rw [LFunction_eq_abelIntegral_of_isPrimitive hq chi hchi s hspos,
        norm_mul]
    _ ≤ ‖s‖ *
        ((Real.sqrt (q : ℝ) * Real.log (q : ℝ)) / sigma) :=
      mul_le_mul_of_nonneg_left hIntegral (norm_nonneg s)
    _ ≤ (|t| + 2) *
        ((Real.sqrt (q : ℝ) * Real.log (q : ℝ)) / sigma) :=
      mul_le_mul_of_nonneg_right hnormS
        (div_nonneg hscale hsigma_pos.le)
    _ ≤ (|t| + 2) *
        (2 * (Real.sqrt (q : ℝ) * Real.log (q : ℝ))) :=
      mul_le_mul_of_nonneg_left hquot (by positivity)
    _ = 2 * (|t| + 2) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      ring

end BoundedGaps.Maynard
