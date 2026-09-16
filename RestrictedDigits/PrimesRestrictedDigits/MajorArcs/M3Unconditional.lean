import PrimesRestrictedDigits.MajorArcs.M3ProgressionEstimate
import PrimesRestrictedDigits.MajorArcs.M3ContributionLogScale

/-!
# Unconditional M3 contribution

This inserts the uniform weighted progression estimate into the corrected M3
aggregation on `MAYNARD-PRD-PUBLISHED`, pp. 188--189.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem self_le_ten_pow_m3 (K : Nat) : K <= 10 ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [pow_succ]
      have hpow : 0 < 10 ^ K := by positivity
      omega

/-- One threshold gives the complete class-three estimate for every source
region of bounded arity, with no remaining progression premise. -/
theorem exists_majorArcClassThreeRegionContributionLogScaleThreshold_unconditional
    (D R : Nat) (hD : 0 < D) {eta : Real} (heta : 0 < eta) :
    ∃ K0 : Nat, ∀ K : Nat, K0 <= K ->
      ∀ k : Nat, k <= R -> ∀ digit : Fin 10,
      ∀ a : Fin k -> Real, (∀ i, eta / 2 <= a i) ->
      (∑ i, a i) < 1 - eta / 2 ->
      ((k + 1 : Nat) : Real) <= 2 / eta ->
      ‖majorArcClassThreeContribution
          (10 ^ K) (Real.log (((10 ^ K : Nat) : Real)) ^ D)
          (paddedRestrictedNumbers digit K) (Finset.range (10 ^ K))
          (fun n => (majorArcRegionWeightAtProduct (10 ^ K) a
            (majorArcM2LogLogDelta (10 ^ K)) eta n : Complex)) -
        (restrictedDigitDensity digit : Complex) *
          ((paddedRestrictedNumbers digit K).card : Complex) *
          majorArcRegionTotalWeight (10 ^ K) a
            (majorArcM2LogLogDelta (10 ^ K)) eta /
          ((10 ^ K : Nat) : Complex)‖ <=
        14 * ((paddedRestrictedNumbers digit K).card : Real) /
          Real.log (((10 ^ K : Nat) : Real)) ^ D := by
  obtain ⟨XPNT, hPNT⟩ :=
    exists_majorArcRegionResidueWeightSum_logScaleThreshold D R heta
  obtain ⟨XSUPPORT, hSUPPORT⟩ :=
    exists_majorArcM2LogScaleThreshold D R heta (show (0 : Real) <= 0 by rfl)
  let XLOG : Nat := Nat.ceil (Real.exp 10)
  let K0 := max 1 (max XPNT (max XSUPPORT XLOG))
  refine ⟨K0, ?_⟩
  intro K hK k hk digit a ha hsum hroom
  have hKOne : 1 <= K := (le_max_left 1 _).trans hK
  have hKRest : max XPNT (max XSUPPORT XLOG) <= K :=
    (le_max_right 1 _).trans hK
  have hXPNTK : XPNT <= K := (le_max_left XPNT _).trans hKRest
  have hXSupportK : XSUPPORT <= K :=
    (le_max_left XSUPPORT XLOG).trans
      ((le_max_right XPNT _).trans hKRest)
  have hXLogK : XLOG <= K :=
    (le_max_right XSUPPORT XLOG).trans
      ((le_max_right XPNT _).trans hKRest)
  have hself : K <= 10 ^ K := self_le_ten_pow_m3 K
  have hXPNTpow : XPNT <= 10 ^ K := hXPNTK.trans hself
  have hXSupportPow : XSUPPORT <= 10 ^ K := hXSupportK.trans hself
  obtain ⟨hX4, hQX, _hloglog, hlarge, _hscale⟩ :=
    hSUPPORT (10 ^ K) hXSupportPow
  have hExpLog : Real.exp 10 <= ((10 ^ K : Nat) : Real) := by
    calc
      Real.exp 10 <= (XLOG : Real) := Nat.le_ceil (Real.exp 10)
      _ <= (K : Real) := by exact_mod_cast hXLogK
      _ <= ((10 ^ K : Nat) : Real) := by exact_mod_cast hself
  have hlogTen : (10 : Real) <=
      Real.log (((10 ^ K : Nat) : Real)) := by
    rw [← Real.log_exp 10]
    exact Real.log_le_log (Real.exp_pos 10) hExpLog
  have hlogOne : (1 : Real) <=
      Real.log (((10 ^ K : Nat) : Real)) := by linarith
  have hQ : (10 : Real) <=
      Real.log (((10 ^ K : Nat) : Real)) ^ D :=
    hlogTen.trans (le_self_pow₀ hlogOne (by omega))
  have hKPos : 0 < K := by omega
  let w : Nat -> Complex := fun n =>
    (majorArcRegionWeightAtProduct (10 ^ K) a
      (majorArcM2LogLogDelta (10 ^ K)) eta n : Complex)
  have hsupport : ∀ n ∈ Finset.range (10 ^ K), w n ≠ 0 ->
      Nat.Coprime n 10 := by
    intro n hn hnweight
    apply majorArcRegionWeightAtProduct_coprime_of_dvd_powerTen
      (delta := majorArcM2LogLogDelta (10 ^ K))
      (by omega : 1 < 10 ^ K) heta ha hlarge rfl
      (show 10 ∣ 10 ^ K by
        obtain ⟨J, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hKPos.ne'
        rw [pow_succ]
        exact dvd_mul_left 10 (10 ^ J))
    dsimp [w] at hnweight
    exact_mod_cast hnweight
  have hAP := hPNT (10 ^ K) K k hXPNTpow hk a ha hsum hroom rfl
  have hbound := norm_majorArcClassThreeContribution_sub_density_le_logScale
    digit hKPos rfl hQ hQX (show (0 : Real) <= 1 by norm_num)
    (Finset.range (10 ^ K)) w hsupport
    (majorArcRegionTotalWeight (10 ^ K) a
      (majorArcM2LogLogDelta (10 ^ K)) eta)
    (fun q hq hqdiv hqLog r hr => by
      simpa [one_mul] using hAP q hq hqdiv hqLog r hr)
  simpa [w, one_mul] using hbound

end PrimesRestrictedDigits
