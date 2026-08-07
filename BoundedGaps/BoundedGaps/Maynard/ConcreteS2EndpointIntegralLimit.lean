import BoundedGaps.Maynard.ConcreteS2EndpointIntegral

noncomputable section

namespace BoundedGaps.Maynard

open Filter MeasureTheory

set_option maxRecDepth 5000 in
theorem tendsto_engelsmaS2CoordinateFiber_endpointIntegral_sub_complementIntegral_zero
    {R D : ℕ → ℕ}
    (m : ℕ → BoundedGaps.engelsmaTuple)
    (r : (N : ℕ) → BoundedGaps.engelsmaTuple → ℕ)
    (hr : ∀ N, IsMaynardDivisorTuple BoundedGaps.engelsmaTuple (R N)
      (primorial (D N)) (r N))
    (hR : Tendsto R atTop atTop)
    (hQ : ∀ᶠ N : ℕ in atTop,
      1 < maynardS2CoordinateFiberEndpoint (R N)
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple
          (m N) (r N))) :
    Tendsto (fun N : ℕ =>
      (∫ x in (0 : ℝ)..(
          Real.log (maynardS2CoordinateFiberEndpoint (R N)
            (maynardS2OffCoordinateProduct
              BoundedGaps.engelsmaTuple (m N) (r N))) / Real.log (R N)),
          engelsmaS2CoordinateFiberPolynomialTest (R N) (m N) (r N) x) -
        ∫ x in (0 : ℝ)..(
          1 - Real.log (maynardS2OffCoordinateProduct
            BoundedGaps.engelsmaTuple (m N) (r N)) / Real.log (R N)),
          engelsmaS2CoordinateFiberPolynomialTest (R N) (m N) (r N) x)
      atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (R N)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hR)
  have hdiv : Tendsto (fun N : ℕ => Real.log 3 / Real.log (R N))
      atTop (nhds 0) := hlog.const_div_atTop (Real.log 3)
  have hbound : Tendsto (fun N : ℕ =>
      smallKCandidateBound * (Real.log 3 / Real.log (R N)))
      atTop (nhds 0) := by
    simpa using hdiv.const_mul smallKCandidateBound
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun N => abs_nonneg _)) ?_ hbound
  have hRgt : ∀ᶠ N : ℕ in atTop, 1 < R N :=
    hR.eventually (eventually_gt_atTop 1)
  filter_upwards [hRgt, hQ] with N hRN hQN
  simpa using
    (abs_engelsmaS2CoordinateFiber_endpointIntegral_sub_complementIntegral_le
      (m := m N) (r := r N) (hr N) hRN hQN)

end BoundedGaps.Maynard
