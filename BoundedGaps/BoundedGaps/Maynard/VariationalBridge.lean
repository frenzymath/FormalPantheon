import BoundedGaps.Maynard.Variational
import BoundedGaps.Maynard.SimplexCompositionMoments

/-!
# Conditional bridge from simplex pair moments to the small-k denominator

The finite certificate stores the rational monomial moments.  This module
proves the remaining finite algebra and support reduction once the corresponding
simplex pair integrals are supplied.  The pair-moment hypotheses are explicit:
they are the analytic obligations, not project axioms.
-/

namespace BoundedGaps.Maynard

open MeasureTheory Set
open scoped BigOperators

noncomputable section

def smallKRealMonomial (b c : ℕ) (t : Fin 105 → ℝ) : ℝ :=
  (1 - smallKRealP1 t) ^ b * (smallKRealP2 t) ^ c

def smallKRealTerm (i : Fin 42) (t : Fin 105 → ℝ) : ℝ :=
  smallKRealCoefficient i *
    smallKRealMonomial (smallKExponentB i) (smallKExponentC i) t

def smallKRealPairTerm (i j : Fin 42) (t : Fin 105 → ℝ) : ℝ :=
  smallKRealTerm i t * smallKRealTerm j t

theorem smallKRealPairTerm_eq_simplexQuadratic (i j : Fin 42)
    (t : Fin 105 → ℝ) :
    smallKRealPairTerm i j t =
      (smallKRealCoefficient i * smallKRealCoefficient j) *
        simplexQuadraticIntegrand 105
          (smallKExponentB i + smallKExponentB j)
          (smallKExponentC i + smallKExponentC j) t := by
  unfold smallKRealPairTerm smallKRealTerm smallKRealMonomial
    simplexQuadraticIntegrand smallKRealP1 smallKRealP2
  rw [pow_add, pow_add]
  ring

theorem smallKRealPairTerm_moment (i j : Fin 42) :
    (∫ t in maynardSimplex 105, smallKRealPairTerm i j t) =
      ((smallKCoefficient i * smallKCoefficient j *
          smallKSimplexMoment
            (smallKExponentB i + smallKExponentB j)
            (smallKExponentC i + smallKExponentC j) : ℚ) : ℝ) := by
  rw [show (fun t => smallKRealPairTerm i j t) =
      (fun t => (smallKRealCoefficient i * smallKRealCoefficient j) *
        simplexQuadraticIntegrand 105
          (smallKExponentB i + smallKExponentB j)
          (smallKExponentC i + smallKExponentC j) t) by
    funext t
    exact smallKRealPairTerm_eq_simplexQuadratic i j t]
  rw [integral_const_mul]
  have hi := smallK_exponent_bound i
  have hj := smallK_exponent_bound j
  have hc : smallKExponentC i + smallKExponentC j < 11 := by omega
  rw [simplexQuadratic_moment_105_smallKG
    (smallKExponentB i + smallKExponentB j) ⟨_, hc⟩]
  norm_num [smallKRealCoefficient, smallKSimplexMoment]

def smallKRealTermBound (i : Fin 42) : ℝ :=
  ‖smallKRealCoefficient i‖ * (106 : ℝ) ^ smallKExponentB i *
    (105 : ℝ) ^ smallKExponentC i

theorem smallKRealTermBound_nonneg (i : Fin 42) :
    0 ≤ smallKRealTermBound i := by
  unfold smallKRealTermBound
  positivity

theorem smallKRealTerm_norm_le (i : Fin 42) (t : Fin 105 → ℝ)
    (ht : t ∈ maynardCube 105) : ‖smallKRealTerm i t‖ ≤ smallKRealTermBound i := by
  unfold smallKRealTerm smallKRealMonomial smallKRealTermBound
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  have hsub : ‖1 - smallKRealP1 t‖ ≤ (106 : ℝ) := by
    calc
      ‖1 - smallKRealP1 t‖ ≤ ‖(1 : ℝ)‖ + ‖smallKRealP1 t‖ := norm_sub_le _ _
      _ = 1 + ‖smallKRealP1 t‖ := by norm_num
      _ ≤ 106 := by linarith [smallKRealP1_norm_le t ht]
  have hp2 : ‖smallKRealP2 t‖ ≤ (105 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (smallKRealP2_nonneg t)]
    exact smallKRealP2_le t ht
  have hb := pow_le_pow_left₀ (norm_nonneg (1 - smallKRealP1 t)) hsub
    (smallKExponentB i)
  have hc := pow_le_pow_left₀ (norm_nonneg (smallKRealP2 t)) hp2
    (smallKExponentC i)
  have hbc :
      ‖1 - smallKRealP1 t‖ ^ smallKExponentB i *
          ‖smallKRealP2 t‖ ^ smallKExponentC i ≤
        (106 : ℝ) ^ smallKExponentB i *
          (105 : ℝ) ^ smallKExponentC i :=
    mul_le_mul hb hc (pow_nonneg (norm_nonneg _) _) (by positivity)
  calc
    ‖smallKRealCoefficient i‖ *
        (‖1 - smallKRealP1 t‖ ^ smallKExponentB i *
          ‖smallKRealP2 t‖ ^ smallKExponentC i) ≤
      ‖smallKRealCoefficient i‖ *
        ((106 : ℝ) ^ smallKExponentB i * (105 : ℝ) ^ smallKExponentC i) :=
      mul_le_mul_of_nonneg_left hbc (norm_nonneg _)
    _ = ‖smallKRealCoefficient i‖ * (106 : ℝ) ^ smallKExponentB i *
        (105 : ℝ) ^ smallKExponentC i := by ring

theorem smallKRealTerm_measurable (i : Fin 42) :
    Measurable (smallKRealTerm i) := by
  unfold smallKRealTerm smallKRealMonomial smallKRealP1 smallKRealP2
  fun_prop

theorem smallKRealPairTerm_integrableOn (i j : Fin 42) :
    IntegrableOn (smallKRealPairTerm i j) (maynardSimplex 105) := by
  refine maynard_integrableOn_of_measurable_bounded
    (s := maynardSimplex 105) (hs := maynardSimplex_measurable (k := 105))
    (hsfinite := (measure_mono (show maynardSimplex 105 ⊆ maynardCube 105 from
      fun _ ht => ht.1)).trans_lt (maynardCube_measure_lt_top 105))
    (f := smallKRealPairTerm i j) ((smallKRealTerm_measurable i).mul
      (smallKRealTerm_measurable j))
    (smallKRealTermBound i * smallKRealTermBound j) ?_
  intro t ht
  unfold smallKRealPairTerm
  rw [norm_mul]
  exact mul_le_mul (smallKRealTerm_norm_le i t ht.1)
    (smallKRealTerm_norm_le j t ht.1) (norm_nonneg _)
    (smallKRealTermBound_nonneg i)

theorem smallKRealPolynomial_eq_sum_terms (t : Fin 105 → ℝ) :
    smallKRealPolynomial t = ∑ i : Fin 42, smallKRealTerm i t := by
  unfold smallKRealPolynomial smallKRealTerm smallKRealMonomial
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem maynardI_eq_simplex_polynomial_square :
    maynardI 105 smallKCandidate =
      ∫ t in maynardSimplex 105, smallKRealPolynomial t ^ 2 := by
  unfold maynardI
  calc
    (∫ t in maynardCube 105, smallKCandidate t ^ 2) =
        ∫ t in maynardSimplex 105, smallKCandidate t ^ 2 := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        (maynardCube_measurable 105) (fun t ht => ht.1)
      intro t ht
      rw [smallKCandidate_simplexSupported t ht.2]
      simp
    _ = ∫ t in maynardSimplex 105, smallKRealPolynomial t ^ 2 := by
      apply setIntegral_congr_fun (maynardSimplex_measurable (k := 105))
      intro t ht
      simp [smallKCandidate, ht]

theorem maynardI_eq_pair_integral_sum
    :
    maynardI 105 smallKCandidate =
      ∑ i : Fin 42, ∑ j : Fin 42,
        ∫ t in maynardSimplex 105, smallKRealPairTerm i j t := by
  rw [maynardI_eq_simplex_polynomial_square]
  simp only [pow_two]
  simp_rw [smallKRealPolynomial_eq_sum_terms]
  simp only [Finset.sum_mul_sum]
  change
    (∫ t, ∑ i : Fin 42, ∑ j : Fin 42,
      smallKRealPairTerm i j t ∂volume.restrict (maynardSimplex 105)) =
      ∑ i : Fin 42, ∑ j : Fin 42,
        (∫ t, smallKRealPairTerm i j t ∂volume.restrict (maynardSimplex 105))
  have hInt' : ∀ i j : Fin 42,
      Integrable (smallKRealPairTerm i j) (volume.restrict (maynardSimplex 105)) := by
    intro i j
    exact (smallKRealPairTerm_integrableOn i j).integrable
  have hInner : ∀ i : Fin 42,
      Integrable (fun t => ∑ j : Fin 42, smallKRealPairTerm i j t)
        (volume.restrict (maynardSimplex 105)) := by
    intro i
    exact integrable_finsetSum Finset.univ (fun j hj => hInt' i j)
  have hOuter :
      (∫ t, ∑ i : Fin 42, ∑ j : Fin 42,
        smallKRealPairTerm i j t ∂volume.restrict (maynardSimplex 105)) =
        ∑ i : Fin 42, ∫ t, ∑ j : Fin 42,
          smallKRealPairTerm i j t ∂volume.restrict (maynardSimplex 105) := by
    simpa using (integral_finsetSum (μ := volume.restrict (maynardSimplex 105))
      (s := Finset.univ) (f := fun i t => ∑ j : Fin 42, smallKRealPairTerm i j t)
      (fun i hi => hInner i))
  rw [hOuter]
  apply Finset.sum_congr rfl
  intro i hi
  simpa using (integral_finsetSum (μ := volume.restrict (maynardSimplex 105))
    (s := Finset.univ) (f := fun j t => smallKRealPairTerm i j t)
    (fun j hj => hInt' i j))

theorem maynardI_eq_smallKDenominator_of_pair_moments
    (hMoment : ∀ i j : Fin 42,
      (∫ t in maynardSimplex 105, smallKRealPairTerm i j t) =
        ((smallKCoefficient i * smallKCoefficient j *
          smallKSimplexMoment
            (smallKExponentB i + smallKExponentB j)
            (smallKExponentC i + smallKExponentC j) : ℚ) : ℝ)) :
    maynardI 105 smallKCandidate = (smallKDenominator : ℝ) := by
  rw [maynardI_eq_pair_integral_sum]
  simp_rw [hMoment]
  unfold smallKDenominator
  norm_num

theorem maynardI_eq_smallKDenominator :
    maynardI 105 smallKCandidate = (smallKDenominator : ℝ) := by
  exact maynardI_eq_smallKDenominator_of_pair_moments
    (fun i j => smallKRealPairTerm_moment i j)

end
end BoundedGaps.Maynard
