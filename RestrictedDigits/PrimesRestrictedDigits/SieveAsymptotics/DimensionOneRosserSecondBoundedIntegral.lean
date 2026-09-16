import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayTwoShift
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserBoundedScalars
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondIntegral

/-!
# Bounded continuation of the second Rosser integral

This makes Iwaniec's bounded-coordinate continuation after Eq. (8.10) explicit for both signs.
-/

open MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

theorem dimensionOneRosserIntegralSecondKernelDivLtBoundedOfHigh
    (kernel : Real -> Real -> Real) (Q scaled : Real -> Real)
    (hKernelDiv : ∀ {L t : Real}, 0 < L -> 1 < t ->
      kernel L t / t = dimensionOneRosserSecondEndpointFactor t *
        (dimensionOneRosserArtificialFactor L 0 t /
          dimensionOneRosserArtificialBase L 0 t * (t * Q (t - 1))))
    (hKernelCont : ∀ {L : Real}, 0 < L ->
      ContinuousOn (kernel L) (Ioi 1))
    (hQCont : ContinuousOn Q (Ioi 0))
    (hQPos : ∀ {t : Real}, 0 < t -> 0 < Q t)
    (hScaledPos : ∀ {t : Real}, 0 < t -> 0 < scaled t)
    {lower L s u s0 : Real} (hlower : 2 <= lower) (hs : lower <= s)
    (hu : Real.exp 5000 + 1 <= u) (hsu : s + 2 <= u)
    (hu0 : 2 * u <= s0) (hgrowth : 9792 * u ^ 52 <= L)
    (htail : (∫ t in s..u, t * Q (t - 1)) = scaled s - scaled u)
    (htwo : 625 * u ^ 2 * scaled u < 2 * scaled s)
    (hhigh : (∫ t in u..s0, kernel L t / t) <
      dimensionOneRosserSecondEndpointFactor s0 *
        dimensionOneRosserArtificialFactor L 0 u * scaled u) :
    (∫ t in s..s0, kernel L t / t) <
      dimensionOneRosserSecondEndpointFactor s0 *
        dimensionOneRosserArtificialFactor L 0 s * scaled s := by
  have huOne : 1 <= u := by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  have huStrict : 1 < u := by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  have huPos : 0 < u := zero_lt_one.trans_le huOne
  have hsTwo : 2 <= s := hlower.trans hs
  have hsPos : 0 < s := by linarith
  have hsuLe : s <= u := by linarith
  have huS0 : u <= s0 := by linarith
  have hs0One : 1 < s0 := by linarith
  have hL : 0 < L := by
    exact (mul_pos (by norm_num) (pow_pos huPos 52)).trans_le hgrowth
  have hkernelDivCont : ContinuousOn (fun t => kernel L t / t) (Ioi 1) := by
    apply (hKernelCont hL).div continuousOn_id
    intro t ht
    exact ne_of_gt (zero_lt_one.trans ht)
  have hIntLow : IntervalIntegrable (fun t => kernel L t / t)
      volume s u := by
    apply ContinuousOn.intervalIntegrable
    apply hkernelDivCont.mono
    intro t ht
    change 1 < t
    rw [uIcc_of_le hsuLe] at ht
    linarith [hsTwo, ht.1]
  have hIntHigh : IntervalIntegrable (fun t => kernel L t / t)
      volume u s0 := by
    apply ContinuousOn.intervalIntegrable
    apply hkernelDivCont.mono
    intro t ht
    change 1 < t
    rw [uIcc_of_le huS0] at ht
    linarith [huOne, ht.1]
  have hQShiftCont : ContinuousOn (fun t => t * Q (t - 1)) (Icc s u) := by
    apply continuousOn_id.mul
    apply hQCont.comp (continuousOn_id.sub continuousOn_const)
    intro t ht
    change 0 < t - 1
    linarith [hsTwo, ht.1]
  let lowCoefficient : Real :=
    (1 - 2 / (3 * u)) * (1 + 1 / (12 * u))
  have hlinearNonneg : 0 <= 1 - 2 / (3 * u) := by
    rw [sub_nonneg, div_le_one (by positivity : 0 < (3 : Real) * u)]
    nlinarith [huOne]
  have hlowCoefficientNonneg : 0 <= lowCoefficient :=
    mul_nonneg hlinearNonneg (by positivity)
  have hmajorantInt : IntervalIntegrable
      (fun t => lowCoefficient * (t * Q (t - 1))) volume s u :=
    hQShiftCont.const_mul lowCoefficient |>.intervalIntegrable_of_Icc hsuLe
  have hpoint : ∀ t ∈ Icc s u,
      kernel L t / t <= lowCoefficient * (t * Q (t - 1)) := by
    intro t ht
    have ht0 : 0 <= t := by linarith [hsTwo, ht.1]
    have htOne : 1 < t := by linarith [hsTwo, ht.1]
    have htu : t <= u := ht.2
    have hbaseOne : 1 <= dimensionOneRosserArtificialBase L 0 t := by
      unfold dimensionOneRosserArtificialBase
      have hratio : 0 <= t ^ 50 / L := by positivity
      simpa only [add_zero] using (show 1 <= 1 + t ^ 50 / L by linarith)
    have hquotPos : 0 <= dimensionOneRosserArtificialFactor L 0 t /
        dimensionOneRosserArtificialBase L 0 t :=
      (div_pos (Real.exp_pos _)
        (dimensionOneRosserArtificialBase_pos hL)).le
    have hquotLe : dimensionOneRosserArtificialFactor L 0 t /
          dimensionOneRosserArtificialBase L 0 t <= 1 + 1 / (12 * u) :=
      (div_le_self (Real.exp_pos _).le hbaseOne).trans
        (dimensionOneRosserArtificialFactor_zero_le_one_add
          huOne ht0 htu hgrowth)
    have hendLe : dimensionOneRosserSecondEndpointFactor t <=
        1 - 2 / (3 * u) :=
      (dimensionOneRosserSecondEndpointFactor_monotoneOn
        (show t ∈ Ioi (1 : Real) by exact htOne)
        (show u ∈ Ioi (1 : Real) by exact huStrict) htu).trans
          (dimensionOneRosserSecondEndpointFactor_le_linear huStrict)
    have hfactorLe : dimensionOneRosserSecondEndpointFactor t *
          (dimensionOneRosserArtificialFactor L 0 t /
            dimensionOneRosserArtificialBase L 0 t) <= lowCoefficient := by
      exact mul_le_mul hendLe hquotLe hquotPos hlinearNonneg
    have hshiftNonneg : 0 <= t * Q (t - 1) :=
      mul_nonneg ht0 (hQPos (by linarith [hsTwo, ht.1])).le
    rw [hKernelDiv hL htOne]
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_right hfactorLe hshiftNonneg)
  have hLowRaw : (∫ t in s..u, kernel L t / t) <=
      lowCoefficient * (scaled s - scaled u) := by
    calc
      (∫ t in s..u, kernel L t / t) <=
          ∫ t in s..u, lowCoefficient * (t * Q (t - 1)) :=
        intervalIntegral.integral_mono_on hsuLe hIntLow hmajorantInt hpoint
      _ = lowCoefficient * (∫ t in s..u, t * Q (t - 1)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = lowCoefficient * (scaled s - scaled u) := by rw [htail]
  have hLowDrop : (∫ t in s..u, kernel L t / t) <=
      lowCoefficient * scaled s := by
    exact hLowRaw.trans (mul_le_mul_of_nonneg_left
      (sub_le_self _ (hScaledPos huPos).le) hlowCoefficientNonneg)
  have hlowCoefficientLe : lowCoefficient <= 1 - 7 / (12 * u) := by
    have herror : 0 <= 1 / (18 * u ^ 2) := by positivity
    calc
      lowCoefficient = 1 - 7 / (12 * u) - 1 / (18 * u ^ 2) := by
        dsimp [lowCoefficient]
        field_simp
        ring
      _ <= 1 - 7 / (12 * u) := sub_le_self _ herror
  have hLow : (∫ t in s..u, kernel L t / t) <=
      (1 - 7 / (12 * u)) * scaled s := by
    exact hLowDrop.trans (mul_le_mul_of_nonneg_right hlowCoefficientLe
      (hScaledPos hsPos).le)
  have hendS0Nonneg : 0 <= dimensionOneRosserSecondEndpointFactor s0 :=
    (dimensionOneRosserSecondEndpointFactor_pos s0).le
  have hendS0Le : dimensionOneRosserSecondEndpointFactor s0 <= 1 := by
    exact (dimensionOneRosserSecondEndpointFactor_le_linear hs0One).trans
      (sub_le_self _ (by positivity : 0 <= 2 / (3 * s0)))
  have hartUle : dimensionOneRosserArtificialFactor L 0 u <=
      1 + 1 / (12 * u) :=
    dimensionOneRosserArtificialFactor_zero_le_one_add huOne huPos.le le_rfl hgrowth
  have hartUNonneg : 0 <= dimensionOneRosserArtificialFactor L 0 u :=
    (Real.exp_pos _).le
  have hscaledUPos := hScaledPos huPos
  have hden : 0 < 625 * u ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos huPos)
  have hscaledURatio : scaled u < 2 * scaled s / (625 * u ^ 2) := by
    apply (lt_div_iff₀ hden).2
    simpa only [mul_comm] using htwo
  have hratioScalar :
      (1 + 1 / (12 * u)) * (2 / (625 * u ^ 2)) < 1 / (24 * u) := by
    field_simp [huPos.ne']
    nlinarith [huOne, sq_nonneg (u - 1)]
  have hHighTerm : dimensionOneRosserSecondEndpointFactor s0 *
        dimensionOneRosserArtificialFactor L 0 u * scaled u <
      (1 / (24 * u)) * scaled s := by
    have hfactorHigh : dimensionOneRosserSecondEndpointFactor s0 *
        dimensionOneRosserArtificialFactor L 0 u <= 1 + 1 / (12 * u) := by
      calc
        dimensionOneRosserSecondEndpointFactor s0 *
            dimensionOneRosserArtificialFactor L 0 u <=
            1 * dimensionOneRosserArtificialFactor L 0 u :=
          mul_le_mul hendS0Le le_rfl hartUNonneg (by norm_num)
        _ <= 1 + 1 / (12 * u) := by simpa using hartUle
    calc
      dimensionOneRosserSecondEndpointFactor s0 *
          dimensionOneRosserArtificialFactor L 0 u * scaled u <=
          (1 + 1 / (12 * u)) * scaled u :=
        mul_le_mul_of_nonneg_right hfactorHigh hscaledUPos.le
      _ < (1 + 1 / (12 * u)) *
          (2 * scaled s / (625 * u ^ 2)) :=
        mul_lt_mul_of_pos_left hscaledURatio (by positivity)
      _ = ((1 + 1 / (12 * u)) * (2 / (625 * u ^ 2))) * scaled s := by ring
      _ < (1 / (24 * u)) * scaled s :=
        mul_lt_mul_of_pos_right hratioScalar (hScaledPos hsPos)
  have hHigh : (∫ t in u..s0, kernel L t / t) <
      (1 / (24 * u)) * scaled s := hhigh.trans hHighTerm
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hIntLow hIntHigh
  have hTotal : (∫ t in s..s0, kernel L t / t) <
      (1 - 13 / (24 * u)) * scaled s := by
    rw [<- hsplit]
    calc
      (∫ t in s..u, kernel L t / t) +
          ∫ t in u..s0, kernel L t / t <
          (1 - 7 / (12 * u)) * scaled s +
            (1 / (24 * u)) * scaled s :=
        add_lt_add_of_le_of_lt hLow hHigh
      _ = (1 - 13 / (24 * u)) * scaled s := by ring
  have hendLower : 1 - 1 / (2 * u) <=
      dimensionOneRosserSecondEndpointFactor s0 := by
    calc
      1 - 1 / (2 * u) <= 1 - 1 / s0 := by
        have hinv : 1 / s0 <= 1 / (2 * u) :=
          one_div_le_one_div_of_le (by positivity : 0 < (2 : Real) * u) hu0
        linarith
      _ <= dimensionOneRosserSecondEndpointFactor s0 :=
        linear_le_dimensionOneRosserSecondEndpointFactor hs0One
  have hartSOne : 1 <= dimensionOneRosserArtificialFactor L 0 s :=
    one_le_dimensionOneRosserArtificialFactor_zero hL hsPos.le
  have htargetCoefficient : 1 - 1 / (2 * u) <=
      dimensionOneRosserSecondEndpointFactor s0 *
        dimensionOneRosserArtificialFactor L 0 s := by
    calc
      1 - 1 / (2 * u) <= dimensionOneRosserSecondEndpointFactor s0 := hendLower
      _ = dimensionOneRosserSecondEndpointFactor s0 * 1 := by ring
      _ <= dimensionOneRosserSecondEndpointFactor s0 *
          dimensionOneRosserArtificialFactor L 0 s :=
        mul_le_mul_of_nonneg_left hartSOne hendS0Nonneg
  have hreserve : (1 - 13 / (24 * u)) * scaled s <
      (1 - 1 / (2 * u)) * scaled s := by
    have hgap : 1 - 13 / (24 * u) < 1 - 1 / (2 * u) := by
      rw [sub_lt_sub_iff_left]
      rw [div_lt_div_iff₀ (by positivity : 0 < (2 : Real) * u)
        (by positivity : 0 < (24 : Real) * u)]
      nlinarith
    exact mul_lt_mul_of_pos_right hgap (hScaledPos hsPos)
  exact hTotal.trans (hreserve.trans_le
    (mul_le_mul_of_nonneg_right htargetCoefficient (hScaledPos hsPos).le))

/-- Bounded-coordinate target-plus specialization of Iwaniec's Eq. (8.10). -/
theorem integral_dimensionOneRosserPlusSecondKernel_div_lt_bounded
    {L s u s0 : Real}
    (hs : 3 <= s) (hu : Real.exp 5000 + 1 <= u)
    (hsu : s + 2 <= u) (hu0 : 2 * u <= s0)
    (hcap : s0 ^ 50 <= L) (hgrowth : 9792 * u ^ 52 <= L) :
    (∫ t in s..s0, dimensionOneRosserPlusSecondKernel L t / t) <
      (1 - 1 / s0) ^ (2 / 3 : Real) *
        (1 + s ^ 50 / L) ^ s * dimensionOneDelayScaledPlus s := by
  have huPos : 0 < u := by nlinarith [Real.exp_pos (5000 : Real)]
  have hL : 0 < L :=
    (mul_pos (by norm_num) (pow_pos huPos 52)).trans_le hgrowth
  have huS0 : u < s0 := by linarith
  have hs0One : 1 < s0 := by linarith
  have hhighRaw := integral_dimensionOneRosserPlusSecondKernel_div_lt
    hL hu huS0 hcap
  have hhigh : (∫ t in u..s0, dimensionOneRosserPlusSecondKernel L t / t) <
      dimensionOneRosserSecondEndpointFactor s0 *
        dimensionOneRosserArtificialFactor L 0 u *
          dimensionOneDelayScaledPlus u := by
    rw [dimensionOneRosserSecondEndpointFactor_eq_rpow hs0One,
      dimensionOneRosserArtificialFactor_eq_rpow hL]
    unfold dimensionOneRosserArtificialBase
    simp only [add_zero]
    exact hhighRaw
  have h := dimensionOneRosserIntegralSecondKernelDivLtBoundedOfHigh
    dimensionOneRosserPlusSecondKernel dimensionOneDelayQMinus
    dimensionOneDelayScaledPlus
    dimensionOneRosserPlusSecondKernel_div_eq
    dimensionOneRosserPlusSecondKernel_continuousOn
    dimensionOneDelayQMinus_continuousOn dimensionOneDelayQMinus_pos
    dimensionOneDelayScaledPlus_pos (lower := (3 : Real)) (by norm_num) hs hu
    hsu hu0 hgrowth
    (integral_dimensionOneDelayPlusKernel_eq_sub hs (by linarith))
    (dimensionOneDelayScaledPlus_two_shift_lt hs hu hsu) hhigh
  rw [dimensionOneRosserSecondEndpointFactor_eq_rpow hs0One,
    dimensionOneRosserArtificialFactor_eq_rpow hL] at h
  simp only [dimensionOneRosserArtificialBase, add_zero] at h
  exact h

/-- Bounded-coordinate target-minus specialization of Iwaniec's Eq. (8.10). -/
theorem integral_dimensionOneRosserMinusSecondKernel_div_lt_bounded
    {L s u s0 : Real}
    (hs : 2 <= s) (hu : Real.exp 5000 + 1 <= u)
    (hsu : s + 2 <= u) (hu0 : 2 * u <= s0)
    (hcap : s0 ^ 50 <= L) (hgrowth : 9792 * u ^ 52 <= L) :
    (∫ t in s..s0, dimensionOneRosserMinusSecondKernel L t / t) <
      (1 - 1 / s0) ^ (2 / 3 : Real) *
        (1 + s ^ 50 / L) ^ s * dimensionOneDelayScaledMinus s := by
  have huPos : 0 < u := by nlinarith [Real.exp_pos (5000 : Real)]
  have hL : 0 < L :=
    (mul_pos (by norm_num) (pow_pos huPos 52)).trans_le hgrowth
  have huS0 : u < s0 := by linarith
  have hs0One : 1 < s0 := by linarith
  have hhighRaw := integral_dimensionOneRosserMinusSecondKernel_div_lt
    hL hu huS0 hcap
  have hhigh : (∫ t in u..s0, dimensionOneRosserMinusSecondKernel L t / t) <
      dimensionOneRosserSecondEndpointFactor s0 *
        dimensionOneRosserArtificialFactor L 0 u *
          dimensionOneDelayScaledMinus u := by
    rw [dimensionOneRosserSecondEndpointFactor_eq_rpow hs0One,
      dimensionOneRosserArtificialFactor_eq_rpow hL]
    unfold dimensionOneRosserArtificialBase
    simp only [add_zero]
    exact hhighRaw
  have h := dimensionOneRosserIntegralSecondKernelDivLtBoundedOfHigh
    dimensionOneRosserMinusSecondKernel dimensionOneDelayQPlus
    dimensionOneDelayScaledMinus
    dimensionOneRosserMinusSecondKernel_div_eq
    dimensionOneRosserMinusSecondKernel_continuousOn
    dimensionOneDelayQPlus_continuousOn dimensionOneDelayQPlus_pos
    dimensionOneDelayScaledMinus_pos (lower := (2 : Real)) (by norm_num) hs hu
    hsu hu0 hgrowth
    (integral_dimensionOneDelayMinusKernel_eq_sub hs (by linarith))
    (dimensionOneDelayScaledMinus_two_shift_lt hs hu hsu) hhigh
  rw [dimensionOneRosserSecondEndpointFactor_eq_rpow hs0One,
    dimensionOneRosserArtificialFactor_eq_rpow hL] at h
  simp only [dimensionOneRosserArtificialBase, add_zero] at h
  exact h

/-- Full source-domain target-plus form of Eq. (8.10). -/
theorem integral_dimensionOneRosserPlusSecondKernel_div_lt_sourceDomain
    {L s s0 : Real} (hs : 3 <= s) (hss0 : s < s0)
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcap : s0 ^ 50 <= L)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= L) :
    (∫ t in s..s0, dimensionOneRosserPlusSecondKernel L t / t) <
      (1 - 1 / s0) ^ (2 / 3 : Real) *
        (1 + s ^ 50 / L) ^ s * dimensionOneDelayScaledPlus s := by
  by_cases hlarge : Real.exp 5000 + 1 <= s
  · have hL : 0 < L := dimensionOneRosserSecondLevelThreshold_pos.trans_le hgrowth
    exact integral_dimensionOneRosserPlusSecondKernel_div_lt hL hlarge hss0 hcap
  · apply integral_dimensionOneRosserPlusSecondKernel_div_lt_bounded hs
      (u := dimensionOneRosserSecondSplice)
    · unfold dimensionOneRosserSecondSplice
      linarith
    · unfold dimensionOneRosserSecondSplice
      linarith
    · exact hsplice
    · exact hcap
    · simpa [dimensionOneRosserSecondLevelThreshold] using hgrowth

/-- Full source-domain target-minus form of Eq. (8.10). -/
theorem integral_dimensionOneRosserMinusSecondKernel_div_lt_sourceDomain
    {L s s0 : Real} (hs : 2 <= s) (hss0 : s < s0)
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcap : s0 ^ 50 <= L)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= L) :
    (∫ t in s..s0, dimensionOneRosserMinusSecondKernel L t / t) <
      (1 - 1 / s0) ^ (2 / 3 : Real) *
        (1 + s ^ 50 / L) ^ s * dimensionOneDelayScaledMinus s := by
  by_cases hlarge : Real.exp 5000 + 1 <= s
  · have hL : 0 < L := dimensionOneRosserSecondLevelThreshold_pos.trans_le hgrowth
    exact integral_dimensionOneRosserMinusSecondKernel_div_lt hL hlarge hss0 hcap
  · apply integral_dimensionOneRosserMinusSecondKernel_div_lt_bounded hs
      (u := dimensionOneRosserSecondSplice)
    · unfold dimensionOneRosserSecondSplice
      linarith
    · unfold dimensionOneRosserSecondSplice
      linarith
    · exact hsplice
    · exact hcap
    · simpa [dimensionOneRosserSecondLevelThreshold] using hgrowth

end PrimesRestrictedDigits
