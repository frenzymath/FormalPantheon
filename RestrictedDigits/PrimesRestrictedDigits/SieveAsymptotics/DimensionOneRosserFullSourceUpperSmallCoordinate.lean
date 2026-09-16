import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceSmallCoordinateScalar
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSmallCoordinateStep
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserRawFullSourceLedger
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceReadyData
import PrimesRestrictedDigits.SieveAsymptotics.RosserFailureLowBaseRawSourceShell
/-! # DimensionOneRosserFullSourceUpperSmallCoordinate -/

set_option maxHeartbeats 2000000

/-!
# Complete upper source target below coordinate three

This passes the finite scalar reserve to the raw model limit and combines low-base shell with
strict cubic-base ledger.
-/

open Filter

namespace PrimesRestrictedDigits

/-- The finite coordinate-three source reserve persists at the raw model
limit. -/
theorem dimensionOneRosserSourceUpperSmallCoordinateRawBudget_le
    {c D K L s s0 : Real}
    (hc : 0 <= c) (hD : 1 <= D) (hK : 0 <= K)
    (hs0Large : Real.exp 5000 + 1 <= s0)
    (hsNonneg : 0 <= s) (hsUpper : s <= 3)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L)
    (hsmall : 6 * (1 + 2304 * K) <= L ^ (1 / 24 : Real))
    (hDdom : 2 * (1 + K) + 2304 * c * K <= D)
    (hmodel : dimensionOneRosserModelPlusRaw 3 <=
      c * dimensionOneDelayScaledPlus 3) :
    9 * K / L + (1 + 3 * K / L) *
        (dimensionOneRosserModelPlusRaw 3 +
          D * dimensionOneRosserSourcePlusProfile L 3 -
          (dimensionOneRosserModelPlusRaw s0 +
            D * dimensionOneRosserSourcePlusProfile L 3 / (2 * s0))) <=
      dimensionOneRosserModelPlusRaw 3 +
        D * dimensionOneRosserSourcePlusProfile L s := by
  have hs0One : 1 <= s0 := by
    have hExpPos := Real.exp_pos (5000 : Real)
    linarith
  have hmodelFinite (R : Nat) :
      dimensionOneRosserModelPlusPartialSum (R + 1) 3 <=
        c * dimensionOneDelayScaledPlus 3 :=
    (dimensionOneRosserModelPlusPartialSum_le_raw (R + 1)
      (by norm_num)).trans hmodel
  have hfinite (R : Nat) :=
    dimensionOneRosserSourceUpperSmallCoordinateBudget_le R hc hD hK
      hs0Large hsNonneg hsUpper hsource hLExp hgate hsmall hDdom
      (hmodelFinite R)
  have hthree : Tendsto
      (fun R : Nat => dimensionOneRosserModelPlusPartialSum (R + 1) 3)
      atTop (nhds (dimensionOneRosserModelPlusRaw 3)) :=
    (dimensionOneRosserModelPlusPartialSum_tendsto_raw_of_one_le
      (s := (3 : Real)) (by norm_num)).comp (tendsto_add_atTop_nat 1)
  have hcutoff : Tendsto
      (fun R : Nat => dimensionOneRosserModelPlusPartialSum (R + 1) s0)
      atTop (nhds (dimensionOneRosserModelPlusRaw s0)) :=
    (dimensionOneRosserModelPlusPartialSum_tendsto_raw_of_one_le hs0One).comp
      (tendsto_add_atTop_nat 1)
  have hleft : Tendsto
      (fun R : Nat =>
        9 * K / L + (1 + 3 * K / L) *
          (dimensionOneRosserModelPlusPartialSum (R + 1) 3 +
            D * dimensionOneRosserSourcePlusProfile L 3 -
            (dimensionOneRosserModelPlusPartialSum (R + 1) s0 +
              D * dimensionOneRosserSourcePlusProfile L 3 / (2 * s0))))
      atTop
      (nhds (9 * K / L + (1 + 3 * K / L) *
        (dimensionOneRosserModelPlusRaw 3 +
          D * dimensionOneRosserSourcePlusProfile L 3 -
          (dimensionOneRosserModelPlusRaw s0 +
            D * dimensionOneRosserSourcePlusProfile L 3 / (2 * s0))))) := by
    exact tendsto_const_nhds.add (tendsto_const_nhds.mul
      ((hthree.add_const _).sub (hcutoff.add_const _)))
  have hright : Tendsto
      (fun R : Nat =>
        dimensionOneRosserModelPlusPartialSum (R + 1) 3 +
          D * dimensionOneRosserSourcePlusProfile L s)
      atTop
      (nhds (dimensionOneRosserModelPlusRaw 3 +
        D * dimensionOneRosserSourcePlusProfile L s)) :=
    hthree.add_const _
  exact le_of_tendsto_of_tendsto' hleft hright hfinite

private theorem fullSourceUpperSmallCoordinate_eight_le_level
    {level : Real} (hlevel : 2 <= level)
    (hLExp : Real.exp 1 <= Real.log level)
    (hgate : 124800 + 14400 *
      Real.log (Real.log (Real.log level)) <=
        Real.log (Real.log level)) :
    8 <= level := by
  have hlevelPos : 0 < level := by linarith
  have hLPos : 0 < Real.log level :=
    (Real.exp_pos 1).trans_le hLExp
  have hlogLOne : 1 <= Real.log (Real.log level) :=
    (Real.le_log_iff_exp_le hLPos).2 hLExp
  have hlogLogNonneg :
      0 <= Real.log (Real.log (Real.log level)) :=
    Real.log_nonneg hlogLOne
  have hlogLLarge : 124800 <= Real.log (Real.log level) := by
    nlinarith
  have hlogLLe := Real.log_le_sub_one_of_pos hLPos
  have hlevelLe := Real.log_le_sub_one_of_pos hlevelPos
  nlinarith

private theorem fullSourceUpperSmallCoordinate_bracket_pos
    {D L s0 : Real} (hD : 1 <= D)
    (hs0Large : Real.exp 5000 + 1 <= s0)
    (hLExp : Real.exp 1 <= L) :
    0 < dimensionOneRosserModelPlusRaw 3 +
        D * dimensionOneRosserSourcePlusProfile L 3 -
        (dimensionOneRosserModelPlusRaw s0 +
          D * dimensionOneRosserSourcePlusProfile L 3 / (2 * s0)) := by
  have hs0Three : 3 <= s0 := by
    have hExp := Real.add_one_le_exp (5000 : Real)
    linarith
  have hs0One : 1 <= s0 := by linarith
  have hmodel : dimensionOneRosserModelPlusRaw s0 <=
      dimensionOneRosserModelPlusRaw 3 :=
    dimensionOneRosserModelPlusRaw_antitoneOn_Ici_one
      (by norm_num) hs0One hs0Three
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hLExp
  have hprofile : 0 < dimensionOneRosserSourcePlusProfile L 3 := by
    unfold dimensionOneRosserSourcePlusProfile
    exact mul_pos (Real.rpow_pos_of_pos hLPos _)
      (dimensionOneRosserPlusArtificialAux_pos hLPos (by norm_num))
  have hs0Pos : 0 < s0 := by linarith
  have hcoeff : 0 < 1 - 1 / (2 * s0) := by
    have hdiv : 1 / (2 * s0) < (1 : Real) := by
      apply (div_lt_one (by positivity : 0 < (2 : Real) * s0)).2
      linarith
    linarith
  have hreserve : 0 < D * dimensionOneRosserSourcePlusProfile L 3 *
      (1 - 1 / (2 * s0)) :=
    mul_pos (mul_pos (by linarith : 0 < D) hprofile) hcoeff
  calc
    0 < (dimensionOneRosserModelPlusRaw 3 -
          dimensionOneRosserModelPlusRaw s0) +
        D * dimensionOneRosserSourcePlusProfile L 3 *
          (1 - 1 / (2 * s0)) :=
      add_pos_of_nonneg_of_pos (sub_nonneg.mpr hmodel) hreserve
    _ = _ := by ring

/-- One uniform raw-ledger threshold closes every complete upper source state
with logarithmic coordinate strictly between one and three. -/
theorem exists_dimensionOneRosserFullSourceUpperSmallCoordinateTarget :
    exists Ssmall : Real, Real.exp 5000 + 1 <= Ssmall /\
      forall (P : Finset Nat) {c D K Sdata level z s : Real}
          (data : DimensionOneRosserSourceCutoffData K Sdata level),
        0 < c -> 1 <= D ->
        2 * (1 + K) + 2304 * c * K <= D ->
        (forall {t : Real}, 1 <= t ->
          dimensionOneRosserModelPlusRaw t <=
            c * dimensionOneDelayScaledPlus t) ->
        (forall {t : Real}, 2 <= t ->
          dimensionOneRosserModelMinusRaw t <=
            c * dimensionOneDelayScaledMinus t) ->
        0 < K ->
        (forall p, p ∈ P -> p.Prime) ->
        (forall x y : Real, 2 <= x -> x < y ->
          sieveDensityBelow P (fun p => (p : Real)⁻¹) x /
              sieveDensityBelow P (fun p => (p : Real)⁻¹) y <
            (Real.log y / Real.log x) * (1 + K / Real.log x)) ->
        2 <= level -> 2 <= z ->
        s = Real.log level / Real.log z ->
        1 < s -> s < 3 ->
        Ssmall <= data.s0 ->
        (forall p : Nat, p ∈ P ->
          level ^ (1 / data.s0) <= (p : Real) ->
          (p : Real) < iwaniecBaseCutoff level ->
          dimensionOneRosserFullSourceLowerTarget P D
            (level / p) p (buchstabArgument level (p : Real))) ->
        dimensionOneRosserFullSourceUpperTarget P D level z s := by
  obtain ⟨Ssmall, hSsmall, hledgerAll⟩ :=
    dimensionOneRosserPlusRawFullSourceLedger
  refine ⟨Ssmall, hSsmall, ?_⟩
  intro P c D K Sdata level z s data hc hD hDdom hmodelPlus hmodelMinus
    hK hprime hStrict hlevel hz hs hsLower hsUpper hSsmallData hInner
  have hlevelEight : 8 <= level :=
    fullSourceUpperSmallCoordinate_eight_le_level hlevel data.hLExp data.hgate
  have hlevelPos : 0 < level := by linarith
  have hLPos : 0 < Real.log level := Real.log_pos (by linarith)
  have hsPos : 0 < s := by linarith
  have hs0Large : Real.exp 5000 + 1 <= data.s0 :=
    hSsmall.trans hSsmallData
  have hs0Three : 3 < data.s0 := by
    have hExp := Real.add_one_le_exp (5000 : Real)
    linarith
  have hbase : 2 <= iwaniecBaseCutoff level :=
    two_le_iwaniecBaseCutoff_of_eight_le hlevelEight
  have hbaseCoord : (3 : Real) = Real.log level /
      Real.log (iwaniecBaseCutoff level) := by
    rw [log_iwaniecBaseCutoff hlevelPos]
    field_simp [hLPos.ne']
  have hledgerRaw := hledgerAll P hc hD hDdom hmodelPlus hmodelMinus
    hK.le hprime hlevel hbase hbaseCoord (by norm_num) hs0Three
    data.hcutoff hSsmallData data.hsource data.hLExp data.hgate data.hgrowth
    data.hsmall (by
      intro u hu hub
      exact (hStrict u (iwaniecBaseCutoff level)
        (data.hcutoff.trans hu) hub).le)
  let B : Real :=
    dimensionOneRosserModelPlusRaw 3 +
      D * dimensionOneRosserSourcePlusProfile (Real.log level) 3 -
      (dimensionOneRosserModelPlusRaw data.s0 +
        D * dimensionOneRosserSourcePlusProfile (Real.log level) 3 /
          (2 * data.s0))
  have hledger :
      upperRosserFailureSum P (fun p => (p : Real)⁻¹) level
            (level ^ (1 / data.s0)) +
          dimensionOneRosserPlusRawFirstPrimeSum P level data.s0
            (iwaniecBaseCutoff level) +
          D * dimensionOneRosserPlusSecondRawPrimeSum P level data.s0
            (iwaniecBaseCutoff level) <
        sieveDensityBelow P (fun p => (p : Real)⁻¹)
            (iwaniecBaseCutoff level) / 3 * B := by
    calc
      _ < sieveDensityBelow P (fun p => (p : Real)⁻¹)
              (iwaniecBaseCutoff level) / 3 *
            (dimensionOneRosserModelPlusRaw 3 -
                dimensionOneRosserModelPlusRaw data.s0 +
              D * (1 - 1 / (2 * data.s0)) *
                dimensionOneRosserSourcePlusProfile
                  (Real.log level) 3) := hledgerRaw
      _ = _ := by dsimp only [B]; ring
  have hshellRaw :=
    upperRosserFailureSum_le_rankZero_add_baseRawSourceShell_with_tail
      P D (fun _ => 0) hprime hlevelEight hz hs hsLower hsUpper hs0Three
      data.hcutoff (by
        intro p hpP hpCutoff hpBase
        simpa using (hInner p hpP hpCutoff hpBase).le)
  have hshell :
      upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
        upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
            level z 0 +
          (upperRosserFailureSum P (fun p => (p : Real)⁻¹) level
              (level ^ (1 / data.s0)) +
            dimensionOneRosserPlusRawFirstPrimeSum P level data.s0
              (iwaniecBaseCutoff level) +
            D * dimensionOneRosserPlusSecondRawPrimeSum P level data.s0
              (iwaniecBaseCutoff level)) := by
    simpa [dimensionOneRosserRawFirstRemainderSum, add_assoc] using hshellRaw
  have hbracket : 0 < B := by
    dsimp only [B]
    exact fullSourceUpperSmallCoordinate_bracket_pos hD hs0Large data.hLExp
  let rho : Real := 1 + 3 * K / Real.log level
  have hscale :
      sieveDensityBelow P (fun p => (p : Real)⁻¹)
            (iwaniecBaseCutoff level) / 3 <
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s * rho := by
    simpa only [rho] using
      dimensionOneRosserBaseCutoffDensityScale_lt P hprime hlevelEight hz hs
        hsLower hsUpper hStrict
  have hledgerCurrent :
      upperRosserFailureSum P (fun p => (p : Real)⁻¹) level
            (level ^ (1 / data.s0)) +
          dimensionOneRosserPlusRawFirstPrimeSum P level data.s0
            (iwaniecBaseCutoff level) +
          D * dimensionOneRosserPlusSecondRawPrimeSum P level data.s0
            (iwaniecBaseCutoff level) <
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s * (rho * B) := by
    calc
      _ < sieveDensityBelow P (fun p => (p : Real)⁻¹)
            (iwaniecBaseCutoff level) / 3 * B := hledger
      _ < (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s * rho) * B :=
        mul_lt_mul_of_pos_right hscale hbracket
      _ = _ := by ring
  have hzeroRaw := dimensionOneRosserRankZero_lt_model_add_error_of_ratio P
    hK hprime hlevel hz hbase hs hsLower hsUpper.le
      (fun u hu huz => hStrict u z hu huz)
  rw [upperRosserFailurePartialSum_zero] at hzeroRaw
  have hzero :
      upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹) level z 0 <
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (dimensionOneRosserModelPlusPartialSum 0 s +
            9 * K / Real.log level) := by
    simpa only [div_eq_mul_inv, mul_assoc] using hzeroRaw
  have hbudget := dimensionOneRosserSourceUpperSmallCoordinateRawBudget_le
    hc.le hD hK.le hs0Large hsPos.le hsUpper.le data.hsource data.hLExp
      data.hgate data.hsmall hDdom (hmodelPlus (by norm_num))
  have hbudget' :
      9 * K / Real.log level + rho * B <=
        dimensionOneRosserModelPlusRaw 3 +
          D * dimensionOneRosserSourcePlusProfile (Real.log level) s := by
    simpa only [rho, B] using hbudget
  have hmodelZero :
      dimensionOneRosserModelPlusPartialSum 0 s = 3 - s := by
    rw [dimensionOneRosserModelPlusPartialSum_zero,
      dimensionOneRosserModelPlusTerm_zero]
    simp [hsLower.le, hsUpper.le]
  have hmodelBoundary :=
    dimensionOneRosserModelPlusRaw_add_eq_at_three hsLower hsUpper.le
  have hmodelSplit :
      dimensionOneRosserModelPlusPartialSum 0 s +
          dimensionOneRosserModelPlusRaw 3 =
        dimensionOneRosserModelPlusRaw s := by
    rw [hmodelZero]
    linarith
  have houterScale : 0 <=
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s :=
    div_nonneg (sieveDensityBelow_reciprocal_pos P z hprime).le hsPos.le
  unfold dimensionOneRosserFullSourceUpperTarget
  calc
    upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
        upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹) level z 0 +
          (upperRosserFailureSum P (fun p => (p : Real)⁻¹) level
              (level ^ (1 / data.s0)) +
            dimensionOneRosserPlusRawFirstPrimeSum P level data.s0
              (iwaniecBaseCutoff level) +
            D * dimensionOneRosserPlusSecondRawPrimeSum P level data.s0
              (iwaniecBaseCutoff level)) := hshell
    _ < sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
            (dimensionOneRosserModelPlusPartialSum 0 s +
              9 * K / Real.log level) +
          sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
            (rho * B) := add_lt_add hzero hledgerCurrent
    _ = sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (dimensionOneRosserModelPlusPartialSum 0 s +
          (9 * K / Real.log level + rho * B)) := by ring
    _ <= sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (dimensionOneRosserModelPlusPartialSum 0 s +
          (dimensionOneRosserModelPlusRaw 3 +
            D * dimensionOneRosserSourcePlusProfile
              (Real.log level) s)) :=
      mul_le_mul_of_nonneg_left (by linarith [hbudget']) houterScale
    _ = sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (dimensionOneRosserModelPlusRaw s +
          D * dimensionOneRosserSourcePlusProfile
            (Real.log level) s) := by rw [← add_assoc, hmodelSplit]

end PrimesRestrictedDigits
