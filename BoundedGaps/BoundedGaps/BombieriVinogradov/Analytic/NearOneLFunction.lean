import BoundedGaps.BombieriVinogradov.Analytic.NonprincipalLFunctionAbel
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Liouville
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Nonprincipal Dirichlet L-functions near one

The all-character Polya--Vinogradov prefix bound controls the Abel integral
after splitting it at the modulus.  A Cauchy circle then gives the explicit
real-axis derivative estimate needed for the weak real-zero gap.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 113,
Lemma 11.2, and printed p. 124, equation (12.11).  Semantic review:
`SEM-548`.
-/

noncomputable section

open Complex MeasureTheory Metric Set
open scoped BigOperators Real Topology

namespace BoundedGaps.Maynard

private lemma three_le_modulus_of_character_ne_one
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    3 ≤ q := by
  by_contra hq
  have hqPos : 0 < q := NeZero.pos q
  have hqNeOne : q ≠ 1 := fun h ↦ hchi (chi.level_one' h)
  have hqTwo : q = 2 := by omega
  subst q
  have hcard : Nat.card (DirichletCharacter ℂ 2) = 1 := by
    rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    norm_num
  exact hchi ((Nat.card_eq_one_iff_unique.mp hcard).1.elim chi 1)

private lemma one_lt_log_modulus
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    1 < Real.log (q : ℝ) := by
  have hqThree : (3 : ℝ) ≤ q := by
    exact_mod_cast three_le_modulus_of_character_ne_one chi hchi
  exact (by norm_num : (1 : ℝ) < 1.0986122885).trans
    (Real.log_three_gt_d9.trans_le
      (Real.log_le_log (by norm_num) hqThree))

private lemma norm_characterIntervalSum_floor_le
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {y : ℝ} (hy : 1 < y) :
    ‖dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi‖ ≤ y := by
  have hfloorPos : 0 < ⌊y⌋₊ := Nat.floor_pos.mpr hy.le
  calc
    ‖dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi‖ ≤
        ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ‖chi (n : ZMod q)‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊y⌋₊, (1 : ℝ) := by
      exact Finset.sum_le_sum fun n _ ↦ chi.norm_le_one (n : ZMod q)
    _ = (⌊y⌋₊ : ℝ) := by
      simp [Nat.card_Icc]
    _ ≤ y := Nat.floor_le (zero_lt_one.trans hy).le

private lemma measurable_characterAbelIntegrand
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : ℂ) :
    AEStronglyMeasurable
      (fun y : ℝ ↦
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1)))
      (volume.restrict (Ioi 1)) := by
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

private lemma integrableOn_characterAbelIntegrand
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun y : ℝ ↦
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1)))
      (Ioi 1) := by
  let C := 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
  have hPower : IntegrableOn
      (fun y : ℝ ↦ y ^ (-(s.re + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hMajorant : IntegrableOn
      (fun y : ℝ ↦ C * y ^ (-(s.re + 1))) (Ioi 1) :=
    hPower.const_mul C
  have hBound : ∀ᵐ (y : ℝ) ∂volume.restrict (Ioi 1),
      ‖dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))‖ ≤
        C * y ^ (-(s.re + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hyPos : 0 < y := zero_lt_one.trans hy
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hyPos]
    simp only [neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_right
      (by
        simpa [C] using
          norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
            hq chi hchi ⌊y⌋₊)
      (Real.rpow_nonneg hyPos.le _)
  exact hMajorant.mono' (measurable_characterAbelIntegrand chi s) hBound

private lemma initial_characterAbelIntegral_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {s : ℂ}
    (hsRe : 1 - 5 / (16 * Real.log (q : ℝ)) ≤ s.re) :
    ‖∫ y in Ioc (1 : ℝ) q,
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))‖ ≤
      3 * Real.log (q : ℝ) := by
  let L := Real.log (q : ℝ)
  let f : ℝ → ℂ := fun y ↦
    dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
      (y : ℂ) ^ (-(s + 1))
  let g : ℝ → ℝ := fun y ↦ 3 * y ^ (-1 : ℝ)
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hqPos : (0 : ℝ) < q := zero_lt_one.trans_le hqOne
  have hLpos : 0 < L := by
    exact Real.log_pos (by exact_mod_cast hq)
  have hLone : 1 < L := one_lt_log_modulus chi hchi
  have hMajorant : IntegrableOn g (Ioc (1 : ℝ) q) := by
    apply (continuousOn_const.mul ?_).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    exact continuousOn_of_forall_continuousAt fun y hy ↦
      Real.continuousAt_rpow_const _ _
        (Or.inl (zero_lt_one.trans_le hy.1).ne')
  have hPoint : ∀ y ∈ Ioc (1 : ℝ) q, ‖f y‖ ≤ g y := by
    intro y hy
    have hyPos : 0 < y := zero_lt_one.trans hy.1
    have hyOne : 1 ≤ y := hy.1.le
    have hdelta : 1 - s.re ≤ 5 / (16 * L) := by
      dsimp [L]
      linarith
    have hpow : y ^ (1 - s.re) ≤ 3 := by
      by_cases hdeltaNonpos : 1 - s.re ≤ 0
      · exact (Real.rpow_le_one_of_one_le_of_nonpos hyOne hdeltaNonpos).trans
          (by norm_num)
      · have hdeltaNonneg : 0 ≤ 1 - s.re := le_of_not_ge hdeltaNonpos
        have hbase : y ^ (1 - s.re) ≤ (q : ℝ) ^ (1 - s.re) :=
          Real.rpow_le_rpow hyPos.le hy.2 hdeltaNonneg
        have hexponent :
            (q : ℝ) ^ (1 - s.re) ≤ (q : ℝ) ^ (5 / (16 * L)) :=
          Real.rpow_le_rpow_of_exponent_le hqOne hdelta
        have heval : (q : ℝ) ^ (5 / (16 * L)) = Real.exp (5 / 16) := by
          rw [Real.rpow_def_of_pos hqPos]
          congr 1
          dsimp [L]
          have hlogNe : Real.log (q : ℝ) ≠ 0 :=
            (Real.log_pos (by exact_mod_cast hq)).ne'
          field_simp [hlogNe]
        calc
          y ^ (1 - s.re) ≤ (q : ℝ) ^ (1 - s.re) := hbase
          _ ≤ (q : ℝ) ^ (5 / (16 * L)) := hexponent
          _ = Real.exp (5 / 16) := heval
          _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
          _ ≤ 3 := Real.exp_one_lt_three.le
    dsimp [f, g]
    rw [norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hyPos]
    simp only [neg_re, add_re, one_re]
    calc
      ‖dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi‖ *
          y ^ (-(s.re + 1)) ≤
          y * y ^ (-(s.re + 1)) :=
        mul_le_mul_of_nonneg_right
          (norm_characterIntervalSum_floor_le chi hy.1)
          (Real.rpow_nonneg hyPos.le _)
      _ = y ^ (-s.re) := by
        rw [mul_comm, ← Real.rpow_add_one hyPos.ne']
        congr 1
        ring
      _ = y ^ (-1 : ℝ) * y ^ (1 - s.re) := by
        rw [← Real.rpow_add hyPos]
        congr 1
        ring
      _ ≤ y ^ (-1 : ℝ) * 3 :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hyPos.le _)
      _ = 3 * y ^ (-1 : ℝ) := by ring
  have hsPos : 0 < s.re := by
    have hfrac : 5 / (16 * L) ≤ 5 / 16 := by
      rw [div_le_iff₀ (by positivity : 0 < 16 * L)]
      nlinarith
    linarith
  have hActual : IntegrableOn f (Ioc (1 : ℝ) q) :=
    (integrableOn_characterAbelIntegrand hq chi hchi hsPos).mono_set
      Ioc_subset_Ioi_self
  calc
    ‖∫ y in Ioc (1 : ℝ) q, f y‖ ≤
        ∫ y in Ioc (1 : ℝ) q, ‖f y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioc (1 : ℝ) q, g y :=
      setIntegral_mono_on hActual.norm hMajorant measurableSet_Ioc hPoint
    _ = 3 * Real.log (q : ℝ) := by
      rw [integral_const_mul]
      rw [← intervalIntegral.integral_of_le hqOne]
      simp_rw [Real.rpow_neg_one]
      rw [integral_inv_of_pos zero_lt_one hqPos]
      simp

private lemma tail_characterAbelIntegral_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {s : ℂ} (hsRe : 1 - 5 / (16 * Real.log (q : ℝ)) ≤ s.re) :
    ‖∫ y in Ioi (q : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))‖ ≤
      4 * Real.log (q : ℝ) := by
  let L := Real.log (q : ℝ)
  let C := 2 * Real.sqrt (q : ℝ) * L
  let f : ℝ → ℂ := fun y ↦
    dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
      (y : ℂ) ^ (-(s + 1))
  let g : ℝ → ℝ := fun y ↦ C * y ^ (-(s.re + 1))
  have hqThree := three_le_modulus_of_character_ne_one chi hchi
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hqThree.trans' (by norm_num)
  have hqPos : (0 : ℝ) < q := zero_lt_one.trans_le hqOne
  have hLone : 1 < L := one_lt_log_modulus chi hchi
  have hLpos : 0 < L := zero_lt_one.trans hLone
  have hfrac : 5 / (16 * L) ≤ 5 / 16 := by
    rw [div_le_iff₀ (by positivity : 0 < 16 * L)]
    nlinarith
  have hsLower : (11 / 16 : ℝ) ≤ s.re := by
    dsimp [L] at hfrac
    linarith
  have hsPos : 0 < s.re := by linarith
  have hCnonneg : 0 ≤ C := by positivity
  have hPower : IntegrableOn (fun y : ℝ ↦ y ^ (-(s.re + 1))) (Ioi q) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hqPos
  have hMajorant : IntegrableOn g (Ioi (q : ℝ)) := hPower.const_mul C
  have hPoint : ∀ y ∈ Ioi (q : ℝ), ‖f y‖ ≤ g y := by
    intro y hy
    have hyPos : 0 < y := hqPos.trans hy
    dsimp [f, g, C]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hyPos]
    simp only [neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_right
      (norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
        hq chi hchi ⌊y⌋₊)
      (Real.rpow_nonneg hyPos.le _)
  have hActual : IntegrableOn f (Ioi (q : ℝ)) :=
    (integrableOn_characterAbelIntegrand hq chi hchi hsPos).mono_set
      (Ioi_subset_Ioi hqOne)
  have hnormIntegral :
      ‖∫ y in Ioi (q : ℝ), f y‖ ≤
        C * ((q : ℝ) ^ (-s.re) / s.re) := by
    calc
      ‖∫ y in Ioi (q : ℝ), f y‖ ≤
          ∫ y in Ioi (q : ℝ), ‖f y‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ y in Ioi (q : ℝ), g y :=
        setIntegral_mono_on hActual.norm hMajorant measurableSet_Ioi hPoint
      _ = C * ∫ y in Ioi (q : ℝ), y ^ (-(s.re + 1)) := by
        rw [integral_const_mul]
      _ = C * ((q : ℝ) ^ (-s.re) / s.re) := by
        rw [integral_Ioi_rpow_of_lt (by linarith) hqPos]
        congr 1
        field_simp [hsPos.ne']
        ring_nf
  have hsHalf : (1 / 2 : ℝ) ≤ s.re := by linarith
  have hpowProduct :
      Real.sqrt (q : ℝ) * (q : ℝ) ^ (-s.re) ≤ 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hqPos]
    exact Real.rpow_le_one_of_one_le_of_nonpos hqOne (by linarith)
  have hinv : 1 / s.re ≤ 2 := by
    exact (div_le_iff₀ hsPos).2 (by linarith)
  calc
    ‖∫ y in Ioi (q : ℝ), f y‖ ≤
        C * ((q : ℝ) ^ (-s.re) / s.re) := hnormIntegral
    _ = 2 * L *
        (Real.sqrt (q : ℝ) * (q : ℝ) ^ (-s.re)) * (1 / s.re) := by
      dsimp [C]
      ring
    _ ≤ 2 * L * 1 * 2 := by
      gcongr
    _ = 4 * Real.log (q : ℝ) := by
      dsimp [L]
      ring

/-- Explicit all-nonprincipal `j = 0` bound in the narrow complex region
used by the Cauchy circle. -/
theorem norm_LFunction_near_one_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {s : ℂ}
    (hsRe : 1 - 5 / (16 * Real.log (q : ℝ)) ≤ s.re)
    (hsNorm : ‖s‖ ≤ 2) :
    ‖DirichletCharacter.LFunction chi s‖ ≤
      32 * Real.log (q : ℝ) := by
  let f : ℝ → ℂ := fun y ↦
    dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
      (y : ℂ) ^ (-(s + 1))
  have hLone := one_lt_log_modulus chi hchi
  have hLpos : 0 < Real.log (q : ℝ) := zero_lt_one.trans hLone
  have hRePos : 0 < s.re := by
    have hfrac : 5 / (16 * Real.log (q : ℝ)) ≤ 5 / 16 := by
      rw [div_le_iff₀ (by positivity : 0 < 16 * Real.log (q : ℝ))]
      nlinarith
    linarith
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hInitial := initial_characterAbelIntegral_le hq chi hchi hsRe
  have hTail := tail_characterAbelIntegral_le hq chi hchi hsRe
  have hIntegrable := integrableOn_characterAbelIntegrand hq chi hchi hRePos
  have hSplit :
      (∫ y in Ioi (1 : ℝ), f y) =
        (∫ y in Ioc (1 : ℝ) q, f y) +
          (∫ y in Ioi (q : ℝ), f y) := by
    rw [← Ioc_union_Ioi_eq_Ioi hqOne,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hIntegrable.mono_set Ioc_subset_Ioi_self)
        (hIntegrable.mono_set (Ioi_subset_Ioi hqOne))]
  rw [LFunction_eq_abelIntegral_of_ne_one hq chi hchi s hRePos, norm_mul]
  change ‖s‖ * ‖∫ y in Ioi (1 : ℝ), f y‖ ≤ _
  rw [hSplit]
  calc
    ‖s‖ * ‖(∫ y in Ioc (1 : ℝ) q, f y) +
        (∫ y in Ioi (q : ℝ), f y)‖ ≤
      ‖s‖ * (‖∫ y in Ioc (1 : ℝ) q, f y‖ +
        ‖∫ y in Ioi (q : ℝ), f y‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg s)
    _ ≤ 2 * (3 * Real.log (q : ℝ) + 4 * Real.log (q : ℝ)) := by
      gcongr
    _ ≤ 32 * Real.log (q : ℝ) := by nlinarith

/-- Explicit `j = 1` real-axis consequence of Lemma 11.2 in the range
needed for the weak real-zero gap. -/
theorem norm_deriv_LFunction_ofReal_near_one_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {sigma : ℝ}
    (hsigmaNear :
      1 - 1 / (4 * Real.log (q : ℝ)) ≤ sigma)
    (hsigmaOne : sigma ≤ 1) :
    ‖deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
      512 * (Real.log (q : ℝ)) ^ 2 := by
  let L := Real.log (q : ℝ)
  let r := 1 / (16 * L)
  have hLone : 1 < L := one_lt_log_modulus chi hchi
  have hLpos : 0 < L := zero_lt_one.trans hLone
  have hrPos : 0 < r := by positivity
  have hrLe : r ≤ 1 / 16 := by
    dsimp [r]
    rw [div_le_iff₀ (by positivity : 0 < 16 * L)]
    nlinarith
  have hsigmaPos : 0 < sigma := by
    have hquarter : 1 / (4 * L) < 1 := by
      rw [div_lt_one (by positivity : 0 < 4 * L)]
      nlinarith
    change 1 - 1 / (4 * L) ≤ sigma at hsigmaNear
    linarith
  have hsphere : ∀ z ∈ sphere (sigma : ℂ) r,
      ‖DirichletCharacter.LFunction chi z‖ ≤ 32 * L := by
    intro z hz
    have hdist : ‖z - (sigma : ℂ)‖ = r := by
      simpa [dist_eq_norm] using mem_sphere.mp hz
    have hreDiff : |z.re - sigma| ≤ r := by
      calc
        |z.re - sigma| = |(z - (sigma : ℂ)).re| := by simp
        _ ≤ ‖z - (sigma : ℂ)‖ := Complex.abs_re_le_norm _
        _ = r := hdist
    have hzRe : 1 - 5 / (16 * L) ≤ z.re := by
      have hrad : r = 1 / (16 * L) := rfl
      rw [hrad] at hreDiff
      have hlower := (abs_le.mp hreDiff).1
      change 1 - 1 / (4 * L) ≤ sigma at hsigmaNear
      have hratio : 1 / (4 * L) = 4 * (1 / (16 * L)) := by
        field_simp [hLpos.ne']
        ring
      rw [hratio] at hsigmaNear
      have hfive : 5 / (16 * L) = 5 * (1 / (16 * L)) := by ring
      rw [hfive]
      linarith
    have hzNorm : ‖z‖ ≤ 2 := by
      calc
        ‖z‖ ≤ ‖(sigma : ℂ)‖ + ‖z - (sigma : ℂ)‖ := by
          simpa [add_comm] using norm_add_le (z - (sigma : ℂ)) (sigma : ℂ)
        _ = sigma + r := by simp [abs_of_pos hsigmaPos, hdist]
        _ ≤ 2 := by linarith
    simpa [L] using norm_LFunction_near_one_le hq chi hchi hzRe hzNorm
  have hCauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hrPos (DirichletCharacter.differentiable_LFunction hchi).diffContOnCl hsphere
  calc
    ‖deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
        (32 * L) / r := hCauchy
    _ = 512 * (Real.log (q : ℝ)) ^ 2 := by
      change (32 * L) / (1 / (16 * L)) = 512 * L ^ 2
      field_simp [hLpos.ne']
      ring

end BoundedGaps.Maynard
