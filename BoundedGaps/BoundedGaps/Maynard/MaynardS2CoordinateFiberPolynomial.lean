import BoundedGaps.Maynard.MaynardLogSimplex
import BoundedGaps.Maynard.MaynardS2CoordinateFiberAbel

noncomputable section

/-!
Polynomial test and calculus interface for the supported Engelsma S2 fiber.
Maynard2013v3, source lines 518--535, replaces the zero-extended candidate by
its polynomial on the supported logarithmic simplex before partial summation.
-/

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real
open scoped ArithmeticFunction.Moebius BigOperators

def engelsmaSmallKPolynomial (t : BoundedGaps.engelsmaTuple → ℝ) : ℝ :=
  smallKRealPolynomial (fun i => t (engelsmaIndexEquiv.symm i))

theorem contDiff_smallKRealPolynomial :
    ContDiff ℝ (⊤ : ℕ∞) smallKRealPolynomial := by
  unfold smallKRealPolynomial smallKRealP1 smallKRealP2
  fun_prop

noncomputable def engelsmaS2CoordinateFiberPolynomialTest
    (R : ℕ) (m : BoundedGaps.engelsmaTuple)
    (r : BoundedGaps.engelsmaTuple → ℕ) (x : ℝ) : ℝ :=
  maynardS2CoordinateFiberTest BoundedGaps.engelsmaTuple R m r
    engelsmaSmallKPolynomial x

set_option maxRecDepth 3000 in
theorem maynardS2CoordinateFiberSum_engelsmaSmallK_eq_polynomialWeightedSum
    {R W : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W r)
    (hrm : r m = 1) (hR : 1 < R) :
    maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R W
        (maynardYValue BoundedGaps.engelsmaTuple R W engelsmaSmallKCandidate)
        m r =
      ∑ u ∈ maynardS2CoordinateFiberSupport
          BoundedGaps.engelsmaTuple R W m r,
        ((ArithmeticFunction.moebius u : ℝ) ^ 2 / Nat.totient u) *
          engelsmaS2CoordinateFiberPolynomialTest R m r
            (Real.log u / Real.log R) := by
  rw [maynardS2CoordinateFiberSum_maynardYValue_eq_sourceSum
    m hr hrm]
  apply Finset.sum_congr rfl
  intro u hu
  have huSupport :=
    (update_mem_maynardDivisorTupleSupport_iff m hr hrm u).mpr hu
  have hpoly := engelsmaSmallKCandidate_eq_polynomial_of_mem_support
    hR huSupport
  have hpoint :
      (normalizedDivisorLogTuple BoundedGaps.engelsmaTuple R
          (Function.update r m u)) =
        Function.update
          (fun h => Real.log (r h) / Real.log R) m
          (Real.log u / Real.log R) := by
    funext h
    by_cases hh : h = m
    · subst h
      simp [normalizedDivisorLogTuple]
    · simp [normalizedDivisorLogTuple, hh]
  have hpoly' :
      engelsmaSmallKCandidate
          (Function.update
            (fun h => Real.log (r h) / Real.log R) m
            (Real.log u / Real.log R)) =
        smallKRealPolynomial (fun i =>
          Function.update
            (fun h => Real.log (r h) / Real.log R) m
            (Real.log u / Real.log R) (engelsmaIndexEquiv.symm i)) := by
    rw [← hpoint]
    exact hpoly
  rw [hpoly']
  rfl

theorem contDiff_engelsmaS2CoordinateFiberPolynomialTest
    (R : ℕ) (m : BoundedGaps.engelsmaTuple)
    (r : BoundedGaps.engelsmaTuple → ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (engelsmaS2CoordinateFiberPolynomialTest R m r) := by
  let f : ℝ → (Fin 105 → ℝ) := fun x =>
    fun i => Function.update (fun h => Real.log (r h) / Real.log R) m x
      (engelsmaIndexEquiv.symm i)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    apply contDiff_pi'
    intro i
    by_cases hi : engelsmaIndexEquiv.symm i = m
    · have heq : (fun x => f x i) = id := by
        funext x
        simp [f, Function.update, hi]
      rw [heq]
      exact contDiff_id
    · have heq : (fun x => f x i) = fun _ : ℝ =>
          Real.log (r (engelsmaIndexEquiv.symm i)) / Real.log R := by
        funext x
        simp [f, Function.update, hi]
      rw [heq]
      exact contDiff_const
  change ContDiff ℝ (⊤ : ℕ∞) (smallKRealPolynomial ∘ f)
  exact contDiff_smallKRealPolynomial.comp hf

set_option maxRecDepth 3000 in
theorem abs_maynardS2CoordinateFiberSum_engelsmaSmallK_sub_integral_le
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) r) (hrm : r m = 1) {S E : ℝ}
    (hQ : 1 < maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r))
    (hR : 1 < R) (hE : 0 ≤ E)
    (happrox : ∀ t ∈ Set.Icc (1 : ℝ)
        (maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)),
      |abelCumulative
          (maynardS2CoordinateFiberCoefficient BoundedGaps.engelsmaTuple
            (primorial D) m r) t - S * Real.log t| ≤ E) :
    |maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R (primorial D)
          (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
            engelsmaSmallKCandidate) m r -
        S * Real.log R *
          (∫ x in (0 : ℝ)..(
            Real.log (maynardS2CoordinateFiberEndpoint R
              (maynardS2OffCoordinateProduct
                BoundedGaps.engelsmaTuple m r)) /
            Real.log R),
            engelsmaS2CoordinateFiberPolynomialTest R m r x)| ≤
      E *
        (|engelsmaS2CoordinateFiberPolynomialTest R m r
            (Real.log (maynardS2CoordinateFiberEndpoint R
              (maynardS2OffCoordinateProduct
                BoundedGaps.engelsmaTuple m r)) / Real.log R)| +
          ∫ t in Set.Ioc (1 : ℝ)
              (maynardS2CoordinateFiberEndpoint R
                (maynardS2OffCoordinateProduct
                  BoundedGaps.engelsmaTuple m r)),
            |deriv (fun z =>
              engelsmaS2CoordinateFiberPolynomialTest R m r
                (Real.log z / Real.log R)) t|) := by
  let P := maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r
  let Q := maynardS2CoordinateFiberEndpoint R P
  let G := engelsmaS2CoordinateFiberPolynomialTest R m r
  let f : ℝ → ℝ := fun t => G (Real.log t / Real.log R)
  have hGsmooth : ContDiff ℝ (⊤ : ℕ∞) G :=
    contDiff_engelsmaS2CoordinateFiberPolynomialTest R m r
  have hG : Continuous G := hGsmooth.continuous
  have hfSmooth : ContDiffOn ℝ (⊤ : ℕ∞) f ({0}ᶜ : Set ℝ) := by
    exact hGsmooth.fun_comp_contDiffOn
      ((Real.contDiffOn_log (n := (⊤ : ℕ∞))).div_const (Real.log R))
  have hIccSub : Set.Icc (1 : ℝ) Q ⊆ ({0}ᶜ : Set ℝ) := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [ht.1]
  have hfDeriv : ∀ x ∈ Set.Icc (1 : ℝ) Q,
      HasDerivAt f (deriv f x) x := by
    intro x hx
    have hx0 : x ≠ 0 := hIccSub hx
    have hGDiff : Differentiable ℝ G :=
      hGsmooth.differentiable (by simp)
    exact (hGDiff.differentiableAt.comp x
      ((Real.differentiableAt_log hx0).div_const (Real.log R))).hasDerivAt
  have hderiv : ContinuousOn (deriv f) (Set.Icc (1 : ℝ) Q) := by
    exact (hfSmooth.continuousOn_deriv_of_isOpen
      isOpen_compl_singleton (by simp)).mono hIccSub
  have hfDerivInt : IntervalIntegrable (deriv f) volume 1 Q :=
    hderiv.intervalIntegrable_of_Icc (by exact_mod_cast hQ.le)
  have hfInt : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) Q) :=
    hderiv.integrableOn_Icc
  have hfNormInt : IntegrableOn (fun t => |deriv f t|)
      (Set.Ioc (1 : ℝ) Q) := by
    have hIcc : IntegrableOn (fun t => ‖deriv f t‖)
        (Set.Icc (1 : ℝ) Q) volume := hderiv.norm.integrableOn_Icc
    have h : IntegrableOn (fun t => ‖deriv f t‖)
        (Set.Ioc (1 : ℝ) Q) :=
      hIcc.mono_set Set.Ioc_subset_Icc_self
    simpa [Real.norm_eq_abs] using h
  have hlog : ContinuousOn (fun t : ℝ => S * Real.log t)
      (Set.Icc (1 : ℝ) Q) :=
    continuousOn_const.mul (Real.continuousOn_log.mono hIccSub)
  have hmainInt : IntegrableOn
      (fun t => deriv f t * (S * Real.log t)) (Set.Ioc (1 : ℝ) Q) :=
    (hderiv.mul hlog).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hsum :=
    maynardS2CoordinateFiberSum_engelsmaSmallK_eq_polynomialWeightedSum
      m hr hrm hR
  have hbound :=
    abs_maynardS2CoordinateFiberWeightedSum_sub_twoScaleNormalizedLogIntegral_le
      m hr hQ hR hE hG hfDeriv hfDerivInt hfInt hfNormInt hmainInt
      happrox le_rfl
  rw [hsum]
  simpa [P, Q, G, f] using hbound

end BoundedGaps.Maynard
