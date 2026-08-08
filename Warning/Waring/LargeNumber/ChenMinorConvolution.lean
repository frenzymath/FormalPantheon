import Waring.LargeNumber.ChenCircleMethod

/-!
# Chen's minor-arc convolution identity

This formalizes the unnumbered definition and rearrangement of `I(N)` in the
final theorem [CHEN1964-EN, p. 1568; CHEN1964-ZH, p. 734].
-/

set_option autoImplicit false

namespace Waring.LargeNumber

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The Fourier polynomial of Chen's finite family of eleven-power sums. -/
def chenElevenPhaseSum (N : Nat) (alpha : Real) : Complex :=
  ∑ u ∈ chenElevenSums N,
    Complex.exp
      (2 * Real.pi * Complex.I * (alpha * (u : Real)))

/-- The square of the family phase sum is its ordered pair expansion. -/
theorem chenElevenPhaseSum_sq_eq_pair_sum (N : Nat) (alpha : Real) :
    chenElevenPhaseSum N alpha ^ 2 =
      ∑ u ∈ chenElevenSums N, ∑ v ∈ chenElevenSums N,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (alpha * ((u + v : Nat) : Real))) := by
  unfold chenElevenPhaseSum
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The family phase sum has the trivial cardinality bound. -/
theorem norm_chenElevenPhaseSum_le (N : Nat) (alpha : Real) :
    ‖chenElevenPhaseSum N alpha‖ ≤ ((chenElevenSums N).card : Real) := by
  unfold chenElevenPhaseSum
  calc
    ‖∑ u ∈ chenElevenSums N,
        Complex.exp
          (2 * Real.pi * Complex.I * (alpha * (u : Real)))‖ ≤
        ∑ _u ∈ chenElevenSums N,
          ‖Complex.exp
            (2 * Real.pi * Complex.I * (alpha * (_u : Real)))‖ :=
      norm_sum_le _ _
    _ = ((chenElevenSums N).card : Real) := by
      simp only [Complex.norm_exp]
      simp

private theorem chenRepresentationIntegrand_sub_sub
    {P N u v : Nat} (huv : u + v ≤ N) (alpha : Real) :
    Analytic.chenTenRepresentationIntegrand P (N - u - v) alpha =
      Analytic.chenTenRepresentationIntegrand P N alpha *
        Complex.exp
          (2 * Real.pi * Complex.I * (alpha * (u : Real))) *
        Complex.exp
          (2 * Real.pi * Complex.I * (alpha * (v : Real))) := by
  unfold Analytic.chenTenRepresentationIntegrand
  have hphase :
      Complex.exp (-2 * Real.pi * Complex.I *
        (alpha * ((N - u - v : Nat) : Real))) =
        Complex.exp (-2 * Real.pi * Complex.I * (alpha * (N : Real))) *
          Complex.exp
            (2 * Real.pi * Complex.I * (alpha * (u : Real))) *
          Complex.exp
            (2 * Real.pi * Complex.I * (alpha * (v : Real))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    have hsub : N - u - v + u + v = N := by omega
    have hsubComplex :
        ((N - u - v : Nat) : Complex) + u + v = N := by
      exact_mod_cast hsub
    rw [← hsubComplex]
    ring
  rw [hphase]
  ring

/-- A finite double convolution of minor-arc contributions is one weighted
minor-arc integral whenever every pair of shifts can be subtracted from the
target. -/
theorem sum_chenMinorContribution_eq_integral
    (P N : Nat) (U : Finset Nat)
    (hU : ∀ u ∈ U, ∀ v ∈ U, u + v ≤ N) :
    (∑ u ∈ U, ∑ v ∈ U,
        chenMinorContribution P (N - u - v)) =
      ∫ alpha in Analytic.chenTenMinorArcs P,
        Analytic.chenTenRepresentationIntegrand P N alpha *
          (∑ u ∈ U,
            Complex.exp
              (2 * Real.pi * Complex.I * (alpha * (u : Real)))) ^ 2 := by
  unfold chenMinorContribution
  have hintegrable (u v : Nat) :
      IntegrableOn
        (Analytic.chenTenRepresentationIntegrand P (N - u - v))
        (Analytic.chenTenMinorArcs P) :=
    (Analytic.integrableOn_chenTenRepresentationIntegrand
      P (N - u - v)).mono_set Set.sdiff_subset
  calc
    (∑ u ∈ U, ∑ v ∈ U,
        ∫ alpha in Analytic.chenTenMinorArcs P,
          Analytic.chenTenRepresentationIntegrand P (N - u - v) alpha) =
        ∫ alpha in Analytic.chenTenMinorArcs P,
          ∑ u ∈ U, ∑ v ∈ U,
            Analytic.chenTenRepresentationIntegrand
              P (N - u - v) alpha := by
      symm
      rw [integral_finsetSum (s := U)
        (f := fun u => fun alpha : Real => ∑ v ∈ U,
          Analytic.chenTenRepresentationIntegrand
            P (N - u - v) alpha)
        (μ := volume.restrict (Analytic.chenTenMinorArcs P)) (by
          intro u hu
          have hsum :=
            integrable_finsetSum' U fun v hv => hintegrable u v
          have hfun :
              (fun alpha : Real => ∑ v ∈ U,
                Analytic.chenTenRepresentationIntegrand
                  P (N - u - v) alpha) =
                ∑ v ∈ U, fun alpha : Real =>
                  Analytic.chenTenRepresentationIntegrand
                    P (N - u - v) alpha := by
            funext alpha
            simp
          rw [hfun]
          exact hsum)]
      apply Finset.sum_congr rfl
      intro u hu
      rw [integral_finsetSum (s := U)
        (f := fun v => fun alpha : Real =>
          Analytic.chenTenRepresentationIntegrand P (N - u - v) alpha)
        (μ := volume.restrict (Analytic.chenTenMinorArcs P))
        (fun v hv => hintegrable u v)]
    _ = ∫ alpha in Analytic.chenTenMinorArcs P,
        Analytic.chenTenRepresentationIntegrand P N alpha *
          (∑ u ∈ U,
            Complex.exp
              (2 * Real.pi * Complex.I * (alpha * (u : Real)))) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with alpha
      rw [pow_two, Finset.sum_mul_sum]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      rw [chenRepresentationIntegrand_sub_sub (hU u hu v hv) alpha]
      ring

/-- At Chen's final threshold, the named minor convolution has the exact
single-integral form used in equation (32). -/
theorem chenMinorConvolution_eq_integral
    {N : Nat} (hN : 10 ^ 785 ≤ N) :
    chenMinorConvolution N =
      ∫ alpha in Analytic.chenTenMinorArcs (mainScale N),
        Analytic.chenTenRepresentationIntegrand (mainScale N) N alpha *
          chenElevenPhaseSum N alpha ^ 2 := by
  have hN780 : 10 ^ 780 ≤ N :=
    (pow_le_pow_right' (by norm_num) (by norm_num : 780 ≤ 785)).trans hN
  have hU : ∀ u ∈ chenElevenSums N, ∀ v ∈ chenElevenSums N,
      u + v ≤ N := by
    intro u hu v hv
    have huBound := mem_chenElevenSums_le_quarter hN780 hu
    have hvBound := mem_chenElevenSums_le_quarter hN780 hv
    omega
  simpa [chenMinorConvolution, chenElevenPhaseSum] using
    sum_chenMinorContribution_eq_integral
      (mainScale N) N (chenElevenSums N) hU

end

end Waring.LargeNumber
