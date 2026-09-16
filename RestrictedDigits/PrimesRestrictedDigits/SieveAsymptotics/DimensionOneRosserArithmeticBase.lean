import PrimesRestrictedDigits.SieveAsymptotics.DecimalDensityRatio
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelPartialSums
import PrimesRestrictedDigits.SieveAsymptotics.RosserCutoffRecurrence

/-!
# The arithmetic rank-zero Rosser estimate in dimension one

This is the rank-zero case of Iwaniec's Section 8 comparison, specialized to dimension one and
the beta-two weights. See `IWANIEC-ROSSER-SIEVE-1980`, Eq. (8.3).
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

/-- The upper rank-zero correction is exactly the density lost between the
beta-two base cutoff and `z`. -/
theorem dimensionOneRosserRankZero_eq_density_sub
    (P : Finset Nat) (nu : Nat -> Real) {level z : Real}
    (hlevel : 0 <= level)
    (hcutoff : iwaniecBaseCutoff level <= z) :
    upperRosserFailureSumAtRank P nu level z 0 =
      sieveDensityBelow P nu (iwaniecBaseCutoff level) -
        sieveDensityBelow P nu z := by
  rw [upperRosserFailureSumAtRank_zero_eq_cubic_sum,
    ← sum_mul_sieveDensityBelow_eq_sub P nu hcutoff]
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_filter]
    rw [iwaniecBaseCutoff_le_iff_cube_le hlevel (by positivity)]
    tauto
  · intro p hp
    rfl

theorem log_iwaniecBaseCutoff {level : Real} (hlevel : 0 < level) :
    Real.log (iwaniecBaseCutoff level) = Real.log level / 3 := by
  rw [iwaniecBaseCutoff, Real.log_rpow hlevel]
  ring

theorem two_le_iwaniecBaseCutoff_of_eight_le {level : Real}
    (hlevel : 8 <= level) :
    2 <= iwaniecBaseCutoff level := by
  have hbaseNonneg := iwaniecBaseCutoff_nonneg (show 0 <= level by linarith)
  have hcube := iwaniecBaseCutoff_pow_three (show 0 <= level by linarith)
  by_contra hnot
  have hbaseLt : iwaniecBaseCutoff level < 2 := lt_of_not_ge hnot
  have hcubeLt : iwaniecBaseCutoff level ^ (3 : Nat) < (2 : Real) ^ 3 :=
    pow_lt_pow_left₀ hbaseLt hbaseNonneg (by norm_num)
  norm_num at hcubeLt
  nlinarith

private theorem iwaniecBaseCutoff_lt_of_logRatio_lt_three
    {level z : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hratio : Real.log level / Real.log z < 3) :
    iwaniecBaseCutoff level < z := by
  have hlevelPos : 0 < level := by linarith
  have hzPos : 0 < z := by linarith
  have hbasePos : 0 < iwaniecBaseCutoff level := by
    exact Real.rpow_pos_of_pos hlevelPos _
  apply (Real.log_lt_log_iff hbasePos hzPos).mp
  rw [log_iwaniecBaseCutoff hlevelPos]
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlog : Real.log level < 3 * Real.log z :=
    (div_lt_iff₀ hlogz).mp hratio
  linarith

/-- The explicit-`K` rank-zero case of the dimension-one arithmetic-to-model
comparison. Keeping `K` explicit lets the later induction reuse the same
density-ratio witness in weighted Lemma 21. -/
theorem dimensionOneRosserRankZero_lt_model_add_error_of_ratio
    (P : Finset Nat) {K level z s : Real}
    (hK : 0 < K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hbase : 2 <= iwaniecBaseCutoff level)
    (hs : s = Real.log level / Real.log z)
    (hsLower : 1 < s) (hsUpper : s <= 3)
    (hRatio : ∀ u : Real, 2 <= u -> u < z ->
      sieveDensityBelow P (fun p => (p : Real)⁻¹) u /
          sieveDensityBelow P (fun p => (p : Real)⁻¹) z <
        (Real.log z / Real.log u) *
          (1 + K / Real.log u)) :
    upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
        level z 0 <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z * s⁻¹ *
        (dimensionOneRosserModelPlusPartialSum 0 s +
          9 * K / Real.log level) := by
  have hlevelPos : 0 < level := by linarith
  have hzPos : 0 < z := by linarith
  have hlogLevel : 0 < Real.log level := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hsPos : 0 < s := by linarith
  have hVPos : 0 < sieveDensityBelow P
      (fun p => (p : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hmodel : dimensionOneRosserModelPlusPartialSum 0 s = 3 - s := by
    rw [dimensionOneRosserModelPlusPartialSum_zero,
      dimensionOneRosserModelPlusTerm_zero]
    simp [hsLower.le, hsUpper]
  rcases hsUpper.lt_or_eq with hsThree | hsThree
  · have hratio : Real.log level / Real.log z < 3 := by
      rwa [← hs]
    have hbasez : iwaniecBaseCutoff level < z :=
      iwaniecBaseCutoff_lt_of_logRatio_lt_three hlevel hz hratio
    rw [upperRosserFailurePartialSum_zero,
      dimensionOneRosserRankZero_eq_density_sub P _ (by positivity)
        hbasez.le, hmodel]
    have hRatioBase := hRatio (iwaniecBaseCutoff level) hbase hbasez
    have hVIdentity :
        sieveDensityBelow P (fun p => (p : Real)⁻¹)
              (iwaniecBaseCutoff level) -
            sieveDensityBelow P (fun p => (p : Real)⁻¹) z =
          sieveDensityBelow P (fun p => (p : Real)⁻¹) z *
            (sieveDensityBelow P (fun p => (p : Real)⁻¹)
                (iwaniecBaseCutoff level) /
              sieveDensityBelow P (fun p => (p : Real)⁻¹) z - 1) := by
      rw [mul_sub, mul_one]
      calc
        sieveDensityBelow P (fun p => (p : Real)⁻¹)
              (iwaniecBaseCutoff level) -
            sieveDensityBelow P (fun p => (p : Real)⁻¹) z =
            (sieveDensityBelow P (fun p => (p : Real)⁻¹)
                (iwaniecBaseCutoff level) /
              sieveDensityBelow P (fun p => (p : Real)⁻¹) z) *
                sieveDensityBelow P (fun p => (p : Real)⁻¹) z -
              sieveDensityBelow P (fun p => (p : Real)⁻¹) z := by
          rw [div_mul_cancel₀ _ hVPos.ne']
        _ = _ := by ring
    rw [hVIdentity]
    calc
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z *
            (sieveDensityBelow P (fun p => (p : Real)⁻¹)
                (iwaniecBaseCutoff level) /
              sieveDensityBelow P (fun p => (p : Real)⁻¹) z - 1) <
          sieveDensityBelow P (fun p => (p : Real)⁻¹) z *
            ((Real.log z / Real.log (iwaniecBaseCutoff level)) *
              (1 + K / Real.log (iwaniecBaseCutoff level)) - 1) := by
        exact mul_lt_mul_of_pos_left
          (sub_lt_sub_right hRatioBase 1) hVPos
      _ = sieveDensityBelow P (fun p => (p : Real)⁻¹) z * s⁻¹ *
            (3 - s + 9 * K / Real.log level) := by
        rw [log_iwaniecBaseCutoff hlevelPos, hs]
        field_simp
        ring
  · have hsEq : s = 3 := hsThree
    have hratio : (3 : Real) <= Real.log level / Real.log z := by
      rw [← hs, hsEq]
    have hcube : z ^ (3 : Nat) <= level :=
      power_le_of_natCast_le_log_div_log hlevel hz hratio
    rw [upperRosserFailurePartialSum_zero,
      upperRosserFailureSumAtRank_eq_zero_of_cutoffPow_le
        P (fun p => (p : Real)⁻¹) level z 0 hprime]
    · rw [hmodel, hsEq]
      positivity
    · simpa using hcube

/-- One coefficient, chosen before every finite decimal prime set and every
later parameter, proves the rank-zero Section 8 estimate in the large-level
Maynard regime. -/
theorem exists_decimalDimensionOneRosserRankZero_bound :
    ∃ K : Real, 2 <= K ∧
      ∀ (P : Finset Nat) (level z s : Real),
        (∀ p ∈ P, p.Prime) ->
        (∀ p ∈ P, ¬p ∣ 10) ->
        8 <= level -> 2 <= z ->
        s = Real.log level / Real.log z ->
        1 < s -> s <= 3 ->
        upperRosserFailurePartialSum P
            (fun p => (p : Real)⁻¹) level z 0 <
          sieveDensityBelow P (fun p => (p : Real)⁻¹) z * s⁻¹ *
            (dimensionOneRosserModelPlusPartialSum 0 s +
              9 * K / Real.log level) := by
  obtain ⟨K, hK, hRatio⟩ := exists_decimalSieveDensityRatio_bound
  refine ⟨K, hK, ?_⟩
  intro P level z s hprime hdecimal hlevel hz hs hsLower hsUpper
  apply dimensionOneRosserRankZero_lt_model_add_error_of_ratio
    P (by linarith [hK]) hprime (by linarith) hz
      (two_le_iwaniecBaseCutoff_of_eight_le hlevel)
      hs hsLower hsUpper
  intro u hu huz
  exact hRatio P u z hprime hdecimal hu huz

end PrimesRestrictedDigits
