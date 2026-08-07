import BoundedGaps.BombieriVinogradov.Analytic.QuadraticZetaDirectEulerRemainder
import BoundedGaps.BombieriVinogradov.Analytic.CharacterPartialSummation
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Swapping the fractional-part Euler remainder

The direct finite sum of integrals from SEM-545 is rewritten as one integral
over `(0,X]`.  The source cutoff is `min X floor(X/t)` for positive `t`; the
representative at zero is arbitrary because the integration set is `Ioc 0 X`.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 124--125.
Semantic review: `SEM-546`.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BoundedGaps.Maynard

/-- The source cutoff, with an arbitrary representative at the omitted zero. -/
noncomputable def quadraticEulerCutoff (X : ℕ) (t : ℝ) : ℕ :=
  if t = 0 then X else min X ⌊(X : ℝ) / t⌋₊

/-- The single-integral form of the direct Euler remainder. -/
noncomputable def quadraticZetaSwappedEulerRemainder
    {q : ℕ} (chi : DirichletCharacter ℂ q) (X : ℕ) : ℂ :=
  (1 / (X : ℂ)) *
    ∫ t : ℝ in Set.Ioc 0 (X : ℝ),
      ((Int.fract t : ℝ) : ℂ) *
        ∑ a ∈ Finset.Icc 1 (quadraticEulerCutoff X t),
          (a : ℂ) * chi (a : ZMod q)

private lemma mem_quadraticEulerCutoff_iff
    {X : ℕ} {t : ℝ} (ht : 0 < t) (a : ℕ) :
    a ∈ Finset.Icc 1 (quadraticEulerCutoff X t) ↔
      a ∈ Finset.Icc 1 X ∧ (a : ℝ) ≤ (X : ℝ) / t := by
  rw [quadraticEulerCutoff, if_neg ht.ne']
  rw [Finset.mem_Icc, Finset.mem_Icc, Nat.le_min]
  constructor
  · rintro ⟨ha1, haX, haf⟩
    refine ⟨⟨ha1, haX⟩, ?_⟩
    rw [Nat.le_floor_iff (div_nonneg (by positivity) ht.le)] at haf
    exact haf
  · rintro ⟨⟨ha1, haX⟩, har⟩
    refine ⟨ha1, haX, ?_⟩
    exact (Nat.le_floor_iff (div_nonneg (by positivity) ht.le)).mpr har

private lemma ratio_swap_iff
    {X a : ℕ} {t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    t ≤ (X : ℝ) / (a : ℝ) ↔ (a : ℝ) ≤ (X : ℝ) / t := by
  have haReal : (0 : ℝ) < a := by exact_mod_cast ha
  rw [le_div_iff₀ haReal, le_div_iff₀ ht]
  ring_nf

private lemma interval_inter_quadratic_cutoff
    {X a : ℕ} (hX : 0 < X) (ha : a ∈ Finset.Icc 1 X) :
    Set.Ioc 0 (X : ℝ) ∩ Set.Iic ((X : ℝ) / (a : ℝ)) =
      Set.Ioc 0 ((X : ℝ) / (a : ℝ)) := by
  have haPos : 0 < a := (Finset.mem_Icc.mp ha).1
  have haReal : (0 : ℝ) < a := by exact_mod_cast haPos
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hle : (X : ℝ) / (a : ℝ) ≤ (X : ℝ) := by
    rw [div_le_iff₀ haReal]
    nlinarith [show (1 : ℝ) ≤ a by exact_mod_cast (Finset.mem_Icc.mp ha).1]
  ext t
  constructor
  · rintro ⟨⟨ht0, htX⟩, hta⟩
    exact ⟨ht0, hta⟩
  · rintro ⟨ht0, hta⟩
    exact ⟨⟨ht0, hta.trans hle⟩, hta⟩

private lemma sum_integral_indicator
    {X : ℕ} (hX : 0 < X) (f : ℝ → ℂ)
    (hf : IntegrableOn f (Set.Ioc 0 (X : ℝ))) (g : ℕ → ℂ) :
    (∑ a ∈ Finset.Icc 1 X, g a *
      (∫ t : ℝ in Set.Ioc 0 ((X : ℝ) / (a : ℝ)), f t)) =
      ∫ t : ℝ in Set.Ioc 0 (X : ℝ),
        ∑ a ∈ Finset.Icc 1 X,
          g a * Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t := by
  have hmeas : ∀ a ∈ Finset.Icc 1 X,
      MeasurableSet (Set.Iic ((X : ℝ) / (a : ℝ))) := by
    intro a ha
    exact measurableSet_Iic
  have hIntIndicator : ∀ a ∈ Finset.Icc 1 X,
      IntegrableOn (Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f)
        (Set.Ioc 0 (X : ℝ)) := by
    intro a ha
    exact hf.indicator (hmeas a ha)
  calc
    (∑ a ∈ Finset.Icc 1 X, g a *
        (∫ t : ℝ in Set.Ioc 0 ((X : ℝ) / (a : ℝ)), f t)) =
        ∑ a ∈ Finset.Icc 1 X, g a *
          (∫ t : ℝ in Set.Ioc 0 (X : ℝ),
            Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [setIntegral_indicator (hmeas a ha)]
      rw [interval_inter_quadratic_cutoff hX ha]
    _ = ∑ a ∈ Finset.Icc 1 X,
          ∫ t : ℝ in Set.Ioc 0 (X : ℝ),
            g a * Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [integral_const_mul]
    _ = ∫ t : ℝ in Set.Ioc 0 (X : ℝ),
          ∑ a ∈ Finset.Icc 1 X,
            g a * Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t := by
      rw [integral_finsetSum]
      intro a ha
      exact (hIntIndicator a ha).const_mul _

private lemma indicator_sum_eq_cutoff
    {X : ℕ} {t : ℝ} (ht : 0 < t) (f : ℝ → ℂ) (g : ℕ → ℂ) :
    (∑ a ∈ Finset.Icc 1 X,
      g a * Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t) =
      f t * ∑ a ∈ Finset.Icc 1 (quadraticEulerCutoff X t), g a := by
  calc
    (∑ a ∈ Finset.Icc 1 X,
        g a * Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t) =
        f t * ∑ a ∈ (Finset.Icc 1 X).filter
          (fun a : ℕ ↦ t ≤ (X : ℝ) / (a : ℝ)), g a := by
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hmem : t ∈ Set.Iic ((X : ℝ) / (a : ℝ))
      · simp only [Set.mem_Iic] at hmem
        simp [Set.indicator, hmem, mul_comm]
      · simp only [Set.mem_Iic] at hmem
        simp [Set.indicator, hmem]
    _ = f t * ∑ a ∈ Finset.Icc 1 (quadraticEulerCutoff X t), g a := by
      apply congrArg (fun s : Finset ℕ => f t * ∑ a ∈ s, g a) ?_
      ext a
      rw [Finset.mem_filter, mem_quadraticEulerCutoff_iff ht]
      apply and_congr_right
      intro ha
      exact ratio_swap_iff (lt_of_lt_of_le Nat.zero_lt_one
        (Finset.mem_Icc.mp ha).1) ht

private lemma integrableOn_fractComplex {X : ℕ} :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ))
      (Set.Ioc 0 (X : ℝ)) := by
  apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
  · exact (Complex.continuous_ofReal.measurable.comp measurable_fract).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le

/-- The direct and swapped fractional-part remainders are equal. -/
theorem quadraticZetaDirectEulerRemainder_eq_swapped
    {q X : ℕ} (chi : DirichletCharacter ℂ q) (hX : 0 < X) :
    quadraticZetaDirectEulerRemainder chi X =
      quadraticZetaSwappedEulerRemainder chi X := by
  let f : ℝ → ℂ := fun t => ((Int.fract t : ℝ) : ℂ)
  let g : ℕ → ℂ := fun a => (a : ℂ) * chi (a : ZMod q)
  have hswap := sum_integral_indicator hX f
    (integrableOn_fractComplex (X := X)) g
  have hcut :
      ∫ t : ℝ in Set.Ioc 0 (X : ℝ),
          ∑ a ∈ Finset.Icc 1 X,
            g a * Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t =
        ∫ t : ℝ in Set.Ioc 0 (X : ℝ),
          f t * ∑ a ∈ Finset.Icc 1 (quadraticEulerCutoff X t), g a := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [indicator_sum_eq_cutoff ht.1]
  unfold quadraticZetaDirectEulerRemainder quadraticZetaSwappedEulerRemainder
  dsimp [f, g] at hswap hcut ⊢
  rw [hcut] at hswap
  simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg
    (fun z : ℂ => (1 / (X : ℂ)) * z) hswap

private lemma quadraticEulerCutoff_le (X : ℕ) (t : ℝ) :
    quadraticEulerCutoff X t ≤ X := by
  by_cases ht : t = 0
  · simp [quadraticEulerCutoff, ht]
  · simp [quadraticEulerCutoff, ht]

private lemma cast_quadraticEulerCutoff_le_div
    {X : ℕ} {t : ℝ} (ht : 0 < t) :
    (quadraticEulerCutoff X t : ℝ) ≤ (X : ℝ) / t := by
  rw [quadraticEulerCutoff, if_neg ht.ne']
  have hfloor : (min X ⌊(X : ℝ) / t⌋₊ : ℕ) ≤ ⌊(X : ℝ) / t⌋₊ :=
    min_le_right _ _
  have hfloor_le :
      (⌊(X : ℝ) / t⌋₊ : ℝ) ≤ (X : ℝ) / t :=
    Nat.floor_le (div_nonneg (by positivity) ht.le)
  have hcast : ((min X ⌊(X : ℝ) / t⌋₊ : ℕ) : ℝ) ≤
      (⌊(X : ℝ) / t⌋₊ : ℝ) := by exact_mod_cast hfloor
  exact hcast.trans hfloor_le

private lemma measurable_quadraticEulerCutoff (X : ℕ) :
    Measurable (quadraticEulerCutoff X) := by
  unfold quadraticEulerCutoff
  have hzero : MeasurableSet ({(0 : ℝ)} : Set ℝ) := measurableSet_singleton (0 : ℝ)
  apply Measurable.ite (by simpa only [Set.setOf_eq_eq_singleton] using hzero)
    measurable_const
  have hdiv : Measurable (fun t : ℝ ↦ (X : ℝ) / t) :=
    measurable_const.div measurable_id
  exact (measurable_of_countable (fun y : ℕ ↦ min X y)).comp hdiv.nat_floor

private lemma integrableOn_quadraticSwappedIntegrand
    {q X : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    IntegrableOn
      (fun t : ℝ ↦ ((Int.fract t : ℝ) : ℂ) *
        ∑ a ∈ Finset.Icc 1 (quadraticEulerCutoff X t),
          (a : ℂ) * chi (a : ZMod q))
      (Set.Ioc 0 (X : ℝ)) := by
  let charPrefix : ℕ → ℂ := fun y ↦
    ∑ a ∈ Finset.Icc 1 y, (a : ℂ) * chi (a : ZMod q)
  let F : ℝ → ℂ := fun t ↦ ((Int.fract t : ℝ) : ℂ) *
    charPrefix (quadraticEulerCutoff X t)
  have hprefixMeas : Measurable (fun t ↦
      charPrefix (quadraticEulerCutoff X t)) :=
    (measurable_of_countable charPrefix).comp
      (measurable_quadraticEulerCutoff X)
  have hFMeas : Measurable F :=
    (Complex.continuous_ofReal.measurable.comp measurable_fract).mul hprefixMeas
  apply IntegrableOn.of_bound measure_Ioc_lt_top hFMeas.aestronglyMeasurable
    (4 * (X : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  change ‖((Int.fract t : ℝ) : ℂ) *
      charPrefix (quadraticEulerCutoff X t)‖ ≤ _
  rw [norm_mul]
  have hfract : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le
  have hprefix := norm_dirichletCharacterWeightedPrefixSum_le
    hq chi hchi (quadraticEulerCutoff X t)
  change ‖charPrefix (quadraticEulerCutoff X t)‖ ≤ _ at hprefix
  calc
    ‖((Int.fract t : ℝ) : ℂ)‖ *
        ‖charPrefix (quadraticEulerCutoff X t)‖ ≤
        1 * (4 * (quadraticEulerCutoff X t : ℝ) *
          Real.sqrt (q : ℝ) * Real.log (q : ℝ)) :=
      mul_le_mul hfract hprefix (norm_nonneg _) zero_le_one
    _ ≤ 4 * (X : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      have hlog : 0 ≤ Real.log (q : ℝ) :=
        (Real.log_pos (by exact_mod_cast hq)).le
      have hscale : 0 ≤ Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
        mul_nonneg (Real.sqrt_nonneg _) hlog
      have hcut : (quadraticEulerCutoff X t : ℝ) ≤ (X : ℝ) := by
        exact_mod_cast quadraticEulerCutoff_le X t
      have hfour : (0 : ℝ) ≤ 4 := by norm_num
      have h4cut : 4 * (quadraticEulerCutoff X t : ℝ) ≤
          4 * (X : ℝ) := mul_le_mul_of_nonneg_left hcut hfour
      calc
        1 * (4 * (quadraticEulerCutoff X t : ℝ) * Real.sqrt (q : ℝ) *
            Real.log (q : ℝ)) =
            (4 * (quadraticEulerCutoff X t : ℝ)) *
              (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) := by
              ring
        _ ≤ (4 * (X : ℝ)) * (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) :=
          mul_le_mul_of_nonneg_right h4cut hscale
        _ = 4 * (X : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
          ring

/-- The swapped Euler remainder has the explicit source-scale logarithmic
bound. -/
theorem norm_quadraticZetaSwappedEulerRemainder_le
    {q X : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (hX : 0 < X) :
    ‖quadraticZetaSwappedEulerRemainder chi X‖ ≤
      4 * (1 + Real.log (X : ℝ)) * Real.sqrt (q : ℝ) *
        Real.log (q : ℝ) := by
  let charPrefix : ℕ → ℂ := fun y ↦
    ∑ a ∈ Finset.Icc 1 y, (a : ℂ) * chi (a : ZMod q)
  let F : ℝ → ℂ := fun t ↦ ((Int.fract t : ℝ) : ℂ) *
    charPrefix (quadraticEulerCutoff X t)
  let S : ℝ := Real.sqrt (q : ℝ) * Real.log (q : ℝ)
  have hXone : 1 ≤ X := hX
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hOneX : (1 : ℝ) ≤ X := by exact_mod_cast hXone
  have hS : 0 ≤ S := mul_nonneg (Real.sqrt_nonneg _)
    (Real.log_pos (by exact_mod_cast hq)).le
  have hFint : IntegrableOn F (Set.Ioc 0 (X : ℝ)) := by
    simpa [F, charPrefix] using
      integrableOn_quadraticSwappedIntegrand hq chi hchi (X := X)
  have hpointFirst : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ‖F t‖ ≤ 4 * (X : ℝ) * S := by
    intro t ht
    change ‖((Int.fract t : ℝ) : ℂ) *
      charPrefix (quadraticEulerCutoff X t)‖ ≤ _
    rw [norm_mul]
    have hfract : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le
    have hprefix :=
      norm_dirichletCharacterWeightedPrefixSum_le
        hq chi hchi (quadraticEulerCutoff X t)
    change ‖charPrefix (quadraticEulerCutoff X t)‖ ≤ _ at hprefix
    calc
      ‖((Int.fract t : ℝ) : ℂ)‖ *
          ‖charPrefix (quadraticEulerCutoff X t)‖ ≤
          1 * (4 * (quadraticEulerCutoff X t : ℝ) * S) := by
        simpa [S, mul_assoc] using
          mul_le_mul hfract hprefix (norm_nonneg _) zero_le_one
      _ ≤ 4 * (X : ℝ) * S := by
        have hcut : (quadraticEulerCutoff X t : ℝ) ≤ (X : ℝ) := by
          exact_mod_cast quadraticEulerCutoff_le X t
        have hfour : (0 : ℝ) ≤ 4 := by norm_num
        have h4cut : 4 * (quadraticEulerCutoff X t : ℝ) ≤
            4 * (X : ℝ) := mul_le_mul_of_nonneg_left hcut hfour
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right h4cut hS
  have hpointSecond : ∀ t ∈ Set.Ioc (1 : ℝ) X,
      ‖F t‖ ≤ (4 * (X : ℝ) * S) * t⁻¹ := by
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans ht.1
    change ‖((Int.fract t : ℝ) : ℂ) *
      charPrefix (quadraticEulerCutoff X t)‖ ≤ _
    rw [norm_mul]
    have hfract : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le
    have hprefix := norm_dirichletCharacterWeightedPrefixSum_le
      hq chi hchi (quadraticEulerCutoff X t)
    change ‖charPrefix (quadraticEulerCutoff X t)‖ ≤ _ at hprefix
    calc
      ‖((Int.fract t : ℝ) : ℂ)‖ *
          ‖charPrefix (quadraticEulerCutoff X t)‖ ≤
          1 * (4 * (quadraticEulerCutoff X t : ℝ) * S) := by
        simpa [S, mul_assoc] using
          mul_le_mul hfract hprefix (norm_nonneg _) zero_le_one
      _ ≤ 4 * ((X : ℝ) / t) * S := by
        have hcut : (quadraticEulerCutoff X t : ℝ) ≤ (X : ℝ) / t :=
          cast_quadraticEulerCutoff_le_div ht0
        have hfour : (0 : ℝ) ≤ 4 := by norm_num
        have h4cut : 4 * (quadraticEulerCutoff X t : ℝ) ≤
            4 * ((X : ℝ) / t) :=
          mul_le_mul_of_nonneg_left hcut hfour
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right h4cut hS
      _ = (4 * (X : ℝ) * S) * t⁻¹ := by ring
  have hFirstInt : IntegrableOn (fun t ↦ ‖F t‖) (Set.Ioc (0 : ℝ) 1) :=
    (hFint.mono_set (Set.Ioc_subset_Ioc_right hOneX)).norm
  have hSecondInt : IntegrableOn (fun t ↦ ‖F t‖) (Set.Ioc (1 : ℝ) X) :=
    (hFint.mono_set (Set.Ioc_subset_Ioc_left zero_le_one)).norm
  have hFirstMajor : IntegrableOn (fun _t : ℝ ↦ 4 * (X : ℝ) * S)
      (Set.Ioc (0 : ℝ) 1) := integrableOn_const measure_Ioc_lt_top.ne
  have hSecondMajor : IntegrableOn (fun t : ℝ ↦
      (4 * (X : ℝ) * S) * t⁻¹) (Set.Ioc (1 : ℝ) X) := by
    have hinv : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Icc 1 X) := by
      apply ContinuousOn.inv₀ continuousOn_id
      intro t ht
      exact (zero_lt_one.trans_le ht.1).ne'
    exact (hinv.const_mul (4 * (X : ℝ) * S)).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hFirst : (∫ t : ℝ in Set.Ioc 0 1, ‖F t‖) ≤
      4 * (X : ℝ) * S := by
    calc
      (∫ t : ℝ in Set.Ioc 0 1, ‖F t‖) ≤
          ∫ _t : ℝ in Set.Ioc 0 1, 4 * (X : ℝ) * S := by
        apply setIntegral_mono_ae_restrict hFirstInt hFirstMajor
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hpointFirst t ht
      _ = 4 * (X : ℝ) * S := by
        rw [setIntegral_const, Measure.real_def, Real.volume_Ioc]
        norm_num [smul_eq_mul]
  have hSecond : (∫ t : ℝ in Set.Ioc 1 (X : ℝ), ‖F t‖) ≤
      4 * (X : ℝ) * S * Real.log (X : ℝ) := by
    calc
      (∫ t : ℝ in Set.Ioc 1 (X : ℝ), ‖F t‖) ≤
          ∫ t : ℝ in Set.Ioc 1 (X : ℝ),
            (4 * (X : ℝ) * S) * t⁻¹ := by
        apply setIntegral_mono_ae_restrict hSecondInt hSecondMajor
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hpointSecond t ht
      _ = 4 * (X : ℝ) * S * Real.log (X : ℝ) := by
        rw [integral_const_mul]
        rw [← intervalIntegral.integral_of_le hOneX]
        rw [integral_inv_of_pos zero_lt_one hXreal]
        simp only [div_one]
  have hunion : Set.Ioc (0 : ℝ) (X : ℝ) =
      Set.Ioc (0 : ℝ) (1 : ℝ) ∪ Set.Ioc (1 : ℝ) (X : ℝ) := by
    ext t
    simp only [Set.mem_Ioc, Set.mem_union]
    constructor
    · intro ht
      by_cases ht1 : t ≤ 1
      · exact Or.inl ⟨ht.1, ht1⟩
      · exact Or.inr ⟨lt_of_not_ge ht1, ht.2⟩
    · rintro (ht | ht) <;> constructor
      · exact ht.1
      · exact ht.2.trans hOneX
      · exact zero_lt_one.trans ht.1
      · exact ht.2
  have hdis : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioc 1 X) := by
    rw [Set.disjoint_left]
    intro t ht1 ht2
    exact (not_lt_of_ge ht1.2) ht2.1
  have hnormIntegral : ‖∫ t : ℝ in Set.Ioc 0 (X : ℝ), F t‖ ≤
      4 * (X : ℝ) * (1 + Real.log (X : ℝ)) * S := by
    calc
      ‖∫ t : ℝ in Set.Ioc 0 (X : ℝ), F t‖ ≤
          ∫ t : ℝ in Set.Ioc 0 (X : ℝ), ‖F t‖ :=
        norm_integral_le_integral_norm _
      _ = (∫ t : ℝ in Set.Ioc 0 1, ‖F t‖) +
          ∫ t : ℝ in Set.Ioc 1 (X : ℝ), ‖F t‖ := by
        rw [hunion, setIntegral_union hdis measurableSet_Ioc
          hFirstInt hSecondInt]
      _ ≤ 4 * (X : ℝ) * S +
          4 * (X : ℝ) * S * Real.log (X : ℝ) := add_le_add hFirst hSecond
      _ = 4 * (X : ℝ) * (1 + Real.log (X : ℝ)) * S := by ring
  unfold quadraticZetaSwappedEulerRemainder
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  change (1 / (X : ℝ)) *
      ‖∫ t : ℝ in Set.Ioc 0 (X : ℝ), F t‖ ≤ _
  calc
    (1 / (X : ℝ)) * ‖∫ t : ℝ in Set.Ioc 0 (X : ℝ), F t‖ ≤
        (1 / (X : ℝ)) *
          (4 * (X : ℝ) * (1 + Real.log (X : ℝ)) * S) :=
      mul_le_mul_of_nonneg_left hnormIntegral (by positivity)
    _ = 4 * (1 + Real.log (X : ℝ)) * Real.sqrt (q : ℝ) *
        Real.log (q : ℝ) := by
      dsimp [S]
      field_simp [hXreal.ne']

end BoundedGaps.Maynard
