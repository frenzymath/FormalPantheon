import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserBoundedScalars

/-!
# Common prefactor for the second dimension-one Rosser kernels

This file isolates the common factor in Iwaniec's Eq. (8.11) and proves its bounded-coordinate
monotonicity. See `IWANIEC-ROSSER-SIEVE-1980`, printed pp. 199--201.
-/

namespace PrimesRestrictedDigits

/-- The common elementary and artificial factor in the two second kernels. -/
noncomputable def dimensionOneRosserSecondPrefactor
    (L t : Real) : Real :=
  dimensionOneRosserSecondKernelFactor t *
    dimensionOneRosserArtificialFactor L 1 (t - 1)

/-- The common prefactor is positive whenever its artificial base is positive. -/
theorem dimensionOneRosserSecondPrefactor_pos
    {L t : Real} (hL : 0 < L) :
    0 < dimensionOneRosserSecondPrefactor L t := by
  unfold dimensionOneRosserSecondPrefactor
  rw [dimensionOneRosserArtificialFactor_eq_rpow hL]
  exact mul_pos (dimensionOneRosserSecondKernelFactor_pos t)
    (Real.rpow_pos_of_pos (dimensionOneRosserArtificialBase_pos hL) _)

/-- The common prefactor is continuous on its exact logarithmic domain. -/
theorem dimensionOneRosserSecondPrefactor_continuousOn
    {L : Real} (hL : 0 < L) :
    ContinuousOn (dimensionOneRosserSecondPrefactor L) (Set.Ioi 1) := by
  unfold dimensionOneRosserSecondPrefactor
  exact dimensionOneRosserSecondKernelFactor_continuousOn.mul
    ((dimensionOneRosserArtificialFactor_continuous
      (epsilon := (1 : Real)) hL).comp_continuousOn
        (continuous_id.sub continuous_const).continuousOn)

private theorem dimensionOneRosserSecondKernelFactor_hasDerivAt
    {t : Real} (ht : 1 < t) :
    HasDerivAt dimensionOneRosserSecondKernelFactor
      (dimensionOneRosserSecondKernelFactor t *
        (-4 / (3 * t * (t - 1)))) t := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have htNe : t ≠ 0 := ht0.ne'
  have hbasePos : 0 < 1 - 1 / t := by
    rw [sub_pos, div_lt_one ht0]
    exact ht
  have hbase : HasDerivAt (fun x : Real => 1 - 1 / x) (1 / t ^ 2) t := by
    have hraw := (hasDerivAt_const t (1 : Real)).sub
      ((hasDerivAt_id t).inv htNe)
    have hderiv := hraw.congr_deriv
      (show 0 - -1 / id t ^ 2 = 1 / t ^ 2 by
        simp only [id_eq, zero_sub]
        ring)
    apply hderiv.congr_of_eventuallyEq
    filter_upwards with x
    simp only [Pi.sub_apply, Pi.inv_apply, id_eq, one_div]
  have hlog := (Real.hasDerivAt_log hbasePos.ne').comp t hbase
  have hexponent := hlog.const_mul (-4 / 3 : Real)
  unfold dimensionOneRosserSecondKernelFactor
  apply ((Real.hasDerivAt_exp
    ((-4 / 3 : Real) * Real.log (1 - 1 / t))).comp t hexponent).congr_deriv
  field_simp [htNe, show t - 1 ≠ 0 by linarith]

/-- Logarithmic derivative formula for the common prefactor. -/
theorem dimensionOneRosserSecondPrefactor_hasDerivAt
    {L t : Real} (hL : 0 < L) (ht : 1 < t) :
    HasDerivAt (dimensionOneRosserSecondPrefactor L)
      (dimensionOneRosserSecondPrefactor L t *
        (dimensionOneRosserArtificialSlope L 1 (t - 1) -
          4 / (3 * t * (t - 1)))) t := by
  have hfactor := dimensionOneRosserSecondKernelFactor_hasDerivAt ht
  have hartificialRaw :=
    (dimensionOneRosserArtificialFactor_hasDerivAt
      (epsilon := (1 : Real)) (t := t - 1) hL).comp t
        ((hasDerivAt_id t).sub_const 1)
  have hartificial : HasDerivAt
      (fun x : Real => dimensionOneRosserArtificialFactor L 1 (x - 1))
      (dimensionOneRosserArtificialFactor L 1 (t - 1) *
        dimensionOneRosserArtificialSlope L 1 (t - 1)) t := by
    apply (hartificialRaw.congr_deriv (by ring)).congr_of_eventuallyEq
    filter_upwards with x
    rfl
  unfold dimensionOneRosserSecondPrefactor
  apply (hfactor.mul hartificial).congr_deriv
  ring

private theorem dimensionOneRosserSecondPrefactor_logDeriv_neg
    {L u t : Real} (hu : 2 <= u) (hgrowth : 9792 * u ^ 52 <= L)
    (ht : Set.Ioo 2 u t) :
    dimensionOneRosserArtificialSlope L 1 (t - 1) -
        4 / (3 * t * (t - 1)) < 0 := by
  have hu0 : 0 < u := by linarith
  have ht0 : 0 < t := by linarith [ht.1]
  have htSub0 : 0 < t - 1 := by linarith [ht.1]
  have hL : 0 < L :=
    (mul_pos (by norm_num) (pow_pos hu0 52)).trans_le hgrowth
  have htPow : t ^ 52 <= u ^ 52 :=
    pow_le_pow_left₀ ht0.le ht.2.le 52
  have hlevel : 9792 * t ^ 52 <= L :=
    (mul_le_mul_of_nonneg_left htPow (by norm_num)).trans hgrowth
  have hslope : dimensionOneRosserArtificialSlope L 1 (t - 1) <
      51 * (t ^ 50 / L) := by
    simpa only [sub_add_cancel] using
      dimensionOneRosserArtificialSlope_one_lt hL htSub0
  have hscaled : 51 * (t ^ 50 / L) <= 1 / (192 * t ^ 2) := by
    calc
      51 * (t ^ 50 / L) = (51 * t ^ 50) / L := by ring
      _ <= 1 / (192 * t ^ 2) := by
        rw [div_le_div_iff₀ hL
          (by positivity : 0 < (192 : Real) * t ^ 2)]
        nlinarith [hlevel]
  have hreciprocal : 1 / (192 * t ^ 2) < 4 / (3 * t * (t - 1)) := by
    rw [div_lt_div_iff₀ (by positivity : 0 < (192 : Real) * t ^ 2)
      (by positivity : 0 < (3 : Real) * t * (t - 1))]
    nlinarith [sq_pos_of_pos ht0]
  linarith

/-- The common prefactor is strictly decreasing throughout the bounded range. -/
theorem dimensionOneRosserSecondPrefactor_strictAntiOn
    {L u : Real} (hu : 2 <= u) (hgrowth : 9792 * u ^ 52 <= L) :
    StrictAntiOn (dimensionOneRosserSecondPrefactor L) (Set.Icc 2 u) := by
  have hu0 : 0 < u := by linarith
  have hL : 0 < L :=
    (mul_pos (by norm_num) (pow_pos hu0 52)).trans_le hgrowth
  refine strictAntiOn_of_hasDerivWithinAt_neg
    (D := Set.Icc (2 : Real) u)
    (f' := fun t => dimensionOneRosserSecondPrefactor L t *
      (dimensionOneRosserArtificialSlope L 1 (t - 1) -
        4 / (3 * t * (t - 1))))
    (convex_Icc 2 u) ?_ ?_ ?_
  · exact (dimensionOneRosserSecondPrefactor_continuousOn hL).mono
      (fun t ht => by change 1 < t; linarith [ht.1])
  · intro t ht
    rw [interior_Icc] at ht
    exact (dimensionOneRosserSecondPrefactor_hasDerivAt hL
      (by linarith [ht.1])).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact mul_neg_of_pos_of_neg
      (dimensionOneRosserSecondPrefactor_pos hL)
      (dimensionOneRosserSecondPrefactor_logDeriv_neg hu hgrowth ht)

/-- Factorization of the target-plus second kernel through the common factor. -/
theorem dimensionOneRosserPlusSecondKernel_eq_prefactor
    (L t : Real) :
    dimensionOneRosserPlusSecondKernel L t =
      dimensionOneRosserSecondPrefactor L t *
        dimensionOneDelayScaledMinus (t - 1) := by
  simp only [dimensionOneRosserPlusSecondKernel,
    dimensionOneRosserMinusArtificialAux,
    dimensionOneRosserSecondPrefactor]
  ring

/-- Factorization of the target-minus second kernel through the common factor. -/
theorem dimensionOneRosserMinusSecondKernel_eq_prefactor
    (L t : Real) :
    dimensionOneRosserMinusSecondKernel L t =
      dimensionOneRosserSecondPrefactor L t *
        dimensionOneDelayScaledPlus (t - 1) := by
  simp only [dimensionOneRosserMinusSecondKernel,
    dimensionOneRosserPlusArtificialAux,
    dimensionOneRosserSecondPrefactor]
  ring

end PrimesRestrictedDigits
