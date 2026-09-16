import PrimesRestrictedDigits.MajorArcs.M2ContributionLogScale
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletProgressionPositiveBlock

/-!
# Unconditional repaired M2 contribution

This inserts the repaired prime-log progression theorem into the conditional
class-two estimate for `MAYNARD-PRD-PUBLISHED`, pp. 187--188.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- One threshold gives the repaired Eq. (11.5) class-two bound with no
remaining arithmetic-progression premise. -/
theorem exists_majorArcClassTwoRegionContributionLogScaleThreshold_unconditional
    (D R : Nat) {eta : Real} (heta : 0 < eta) :
    ∃ K0 : Nat, ∀ K : Nat, K0 <= K ->
      ∀ k : Nat, k <= R -> ∀ digit : Fin 10,
      ∀ a : Fin k -> Real, (∀ i, eta / 2 <= a i) ->
      (∑ i, a i) < 1 - eta / 2 ->
      ((k + 1 : Nat) : Real) <= 2 / eta ->
      ‖majorArcClassTwoContribution
          (10 ^ K) (Real.log (((10 ^ K : Nat) : Real)) ^ D)
          (paddedRestrictedNumbers digit K) (Finset.range (10 ^ K))
          (fun n => (majorArcRegionWeightAtProduct (10 ^ K) a
            (majorArcM2LogLogDelta (10 ^ K)) eta n : Complex))‖ <=
        210 * ((paddedRestrictedNumbers digit K).card : Real) /
          Real.log (((10 ^ K : Nat) : Real)) ^ D := by
  obtain ⟨E, hE, XPNT, hPNT⟩ :=
    exists_majorArcPositiveBlockSource_primeLog_error_le D (R + 1) heta
  obtain ⟨KARC, hARC⟩ :=
    exists_majorArcClassTwoRegionContributionLogScaleThreshold D R heta hE.le
  obtain ⟨XSUPPORT, hSUPPORT⟩ :=
    exists_majorArcM2LogScaleThreshold D R heta hE.le
  have self_le_ten_pow : ∀ n : Nat, n <= 10 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        have hpow : 0 < 10 ^ n := by positivity
        omega
  let K0 := max KARC (max XPNT XSUPPORT)
  refine ⟨K0, ?_⟩
  intro K hK k hk digit a hlower hsum hell
  have hKARC : KARC <= K :=
    (le_max_left KARC (max XPNT XSUPPORT)).trans hK
  have hXPNT : XPNT <= K :=
    (le_max_left XPNT XSUPPORT).trans
      ((le_max_right KARC (max XPNT XSUPPORT)).trans hK)
  have hXSUPPORT : XSUPPORT <= K :=
    (le_max_right XPNT XSUPPORT).trans
      ((le_max_right KARC (max XPNT XSUPPORT)).trans hK)
  have hXPNTpow : XPNT <= 10 ^ K := hXPNT.trans (self_le_ten_pow K)
  have hXSUPPORTpow : XSUPPORT <= 10 ^ K :=
    hXSUPPORT.trans (self_le_ten_pow K)
  obtain ⟨_hX, _hlogX, hloglog, _hlarge, _hscale⟩ :=
    hSUPPORT (10 ^ K) hXSUPPORTpow
  apply hARC K hKARC k hk digit a hlower hsum hell
  intro q hq hqdiv hqlog m hm hweight j hj r hr
  have hmData := Finset.mem_Ico.mp hm
  have hjData := Finset.mem_Ico.mp hj
  have hSmooth : IsDecimalSmooth q :=
    (isDecimalSmooth_iff_exists_dvd_pow_ten q).2 ⟨K, hqdiv⟩
  have hCoprime : Nat.Coprime r q := by
    rw [majorArcReducedResidues, Finset.mem_filter] at hr
    exact hr.2
  have hmSupport := projectedPrimeBoxWeightAtProduct_logLog_support_bounds
    heta hsum hell hloglog (by
      simpa only [majorArcM2LogLogDelta] using hweight)
  exact hPNT (10 ^ K) (k + 1) m j q r hXPNTpow (by omega) (by omega)
    hell (by omega) (hmSupport.1.trans_lt hmSupport.2) (by omega) hjData.2 hq
    hSmooth hqlog hCoprime

end PrimesRestrictedDigits
