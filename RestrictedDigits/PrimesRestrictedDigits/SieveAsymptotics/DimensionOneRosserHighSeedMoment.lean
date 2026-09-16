import PrimesRestrictedDigits.BasicEstimates.ReciprocalPrimeChebyshev
import PrimesRestrictedDigits.SieveAsymptotics.DecimalDensityRatio
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserHighSeedScalars
import PrimesRestrictedDigits.SieveAsymptotics.RosserRecurrenceVanishing

/-!
# Finite-product moment bounds for the high-rank Rosser seed

This file supplies the prime-set-dependent finite arithmetic behind the independent
replacement for Iwaniec's Eq. (8.13).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A reciprocal-prime density is at most one. -/
theorem sieveDensityBelow_reciprocal_le_one
    (P : Finset Nat) (z : Real) (hprime : forall p, p ∈ P -> p.Prime) :
    sieveDensityBelow P (fun p => (p : Real)⁻¹) z <= 1 := by
  rw [sieveDensityBelow]
  apply Finset.prod_le_one
  · intro p hp
    have hpPrime := hprime p (Finset.mem_filter.mp hp).1
    have hpOne : (1 : Real) < p := by exact_mod_cast hpPrime.one_lt
    exact (sub_pos.mpr (inv_lt_one_of_one_lt₀ hpOne)).le
  · intro p hp
    have hpPrime := hprime p (Finset.mem_filter.mp hp).1
    have hpPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
    linarith [inv_pos.mpr hpPos]

/-- The inverse reciprocal-prime density is controlled by twice the
reciprocal mass on its exact finite carrier. -/
theorem sieveDensityBelow_reciprocal_inv_le_exp_sum
    (P : Finset Nat) (z : Real) (hprime : forall p, p ∈ P -> p.Prime) :
    (sieveDensityBelow P (fun p => (p : Real)⁻¹) z)⁻¹ <=
      Real.exp (2 * ∑ p ∈ P.filter (fun p : Nat => (p : Real) < z),
        (p : Real)⁻¹) := by
  let S := P.filter (fun p : Nat => (p : Real) < z)
  rw [sieveDensityBelow, <- Finset.prod_inv_distrib]
  calc
    (∏ p ∈ S, (1 - (p : Real)⁻¹)⁻¹) <=
        ∏ p ∈ S, (1 + 2 * (p : Real)⁻¹) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpPrime := hprime p (Finset.mem_filter.mp hp).1
        have hpOne : (1 : Real) < p := by exact_mod_cast hpPrime.one_lt
        exact inv_nonneg.mpr
          (sub_pos.mpr (inv_lt_one_of_one_lt₀ hpOne)).le
      · intro p hp
        exact inverse_one_sub_prime_inv_le
          (hprime p (Finset.mem_filter.mp hp).1).two_le
    _ <= Real.exp (∑ p ∈ S, 2 * (p : Real)⁻¹) :=
      Real.prod_one_add_le_exp_sum S (fun p => by positivity)
    _ = Real.exp (2 * ∑ p ∈ S, (p : Real)⁻¹) := by
      rw [Finset.mul_sum]

/-- The exact logarithmic ratio and the upper seed band bound the prime
cutoff scale. -/
theorem dimensionOneRosserSeed_log_cutoff_le_pow
    {level z s : Real} (hz : 2 <= z) (hsPos : 0 < s)
    (hs : s = Real.log level / Real.log z)
    (hband : Real.log level <= s ^ 51) :
    Real.log z <= s ^ 50 := by
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hratio : Real.log level = s * Real.log z := by
    rw [hs]
    field_simp
  have hmul : s * Real.log z <= s ^ 51 := by rwa [<- hratio]
  rw [show s ^ 51 = s * s ^ 50 by ring] at hmul
  exact (mul_le_mul_iff_right₀ hsPos).mp hmul

/-- The reciprocal mass of the selected prime factors satisfies the coarse
Chebyshev bound needed by the seed scalar estimates. -/
theorem sieveFactorsBelow_reciprocalSum_le_seedBound
    (P : Finset Nat) {z s : Real}
    (hprime : forall p, p ∈ P -> p.Prime) (hz : 2 <= z)
    (hsLarge : Real.exp 5000 + 1 <= s)
    (hlogz : Real.log z <= s ^ 50) :
    (∑ p ∈ P.filter (fun p : Nat => (p : Real) < z), (p : Real)⁻¹) <=
      24 + 400 * Real.log s := by
  let S := P.filter (fun p : Nat => (p : Real) < z)
  let T := (naturalLeftClosedRightOpenInterval 2 z).filter Nat.Prime
  have hST : S ⊆ T := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨mem_naturalLeftClosedRightOpenInterval.mpr ⟨?_, hpData.2⟩,
      hprime p hpData.1⟩
    exact_mod_cast (hprime p hpData.1).two_le
  have hsumST : (∑ p ∈ S, (p : Real)⁻¹) <= ∑ p ∈ T, (p : Real)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hST
    intro p hpT hpS
    positivity
  have hCheb := sum_prime_inv_halfOpen_le_chebyshev 2 z (by norm_num) hz
  have hsPos : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hlogs : 0 < Real.log s := by
    linarith [dimensionOneRosserSeed_log_gt hsLarge]
  have hlogzPos : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwoHalf : (1 / 2 : Real) < Real.log 2 := by
    exact (by norm_num : (1 / 2 : Real) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hfirst : 8 / Real.log z <= 16 := by
    rw [div_le_iff₀ hlogzPos]
    have hlogTwoLe : Real.log 2 <= Real.log z :=
      Real.log_le_log (by norm_num) hz
    nlinarith
  have hratioPos : 0 < Real.log z / Real.log 2 :=
    div_pos hlogzPos hlogTwoPos
  have hpowPos : 0 < s ^ 50 := pow_pos hsPos _
  have hratioLe : Real.log z / Real.log 2 <= 2 * s ^ 50 := by
    rw [div_le_iff₀ hlogTwoPos]
    calc
      Real.log z <= s ^ 50 := hlogz
      _ <= 2 * s ^ 50 * Real.log 2 := by
        nlinarith
  have hlogRatio :
      Real.log (Real.log z / Real.log 2) <= 1 + 50 * Real.log s := by
    calc
      Real.log (Real.log z / Real.log 2) <= Real.log (2 * s ^ 50) :=
        Real.strictMonoOn_log.monotoneOn hratioPos
          (mul_pos (by norm_num) hpowPos) hratioLe
      _ = Real.log 2 + 50 * Real.log s := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero _ hsPos.ne'),
          Real.log_pow]
        norm_num
      _ <= 1 + 50 * Real.log s := by
        linarith [Real.log_two_lt_d9]
  calc
    (∑ p ∈ S, (p : Real)⁻¹) <= ∑ p ∈ T, (p : Real)⁻¹ := hsumST
    _ <= 8 / Real.log z +
        8 * Real.log (Real.log z / Real.log 2) := hCheb
    _ <= 8 / Real.log z + 8 * (1 + 50 * Real.log s) := by
      gcongr
    _ <= 24 + 400 * Real.log s := by linarith

/-- A first-failure tuple has length strictly larger than `s - 2`. -/
theorem rosserFirstFailure_sub_two_lt_length
    (checked : Nat -> Prop) (P : Finset Nat) {level z s : Real}
    {xs : List Nat} (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsublist : List.Sublist xs (sieveFactorsBelow P z))
    (hfailure : IsFirstRosserFailure checked level xs) :
    s - 2 < (xs.length : Real) := by
  have hcubic :
      level <= ((xs.dropLast.prod * xs.getLastD 1 ^ 3 : Nat) : Real) := by
    apply le_of_not_gt
    intro hlt
    exact hfailure.2.2.2
      ((rosserBoundary_iff_dropLast_cube hfailure.1).mpr hlt)
  have hpower := rosserFailureCubic_lt_cutoffPow hprime hsublist hfailure.1
  have hlevelPower : level < z ^ (xs.length + 2) := hcubic.trans_lt hpower
  have hlevelPos : 0 < level := by linarith
  have hzPos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlog : Real.log level < Real.log (z ^ (xs.length + 2)) :=
    Real.strictMonoOn_log hlevelPos (pow_pos hzPos _) hlevelPower
  rw [Real.log_pow] at hlog
  have hsLt : s < (xs.length : Real) + 2 := by
    rw [hs, div_lt_iff₀ hlogz]
    norm_num at hlog ⊢
    nlinarith
  linarith

private theorem tiltedSublistProductSum_eq
    (ambient : List Nat) (a : Real) :
    (ambient.sublists.map fun xs =>
      (xs.map fun (p : Nat) => a * (p : Real)⁻¹).prod).sum =
      (ambient.map fun (p : Nat) => 1 + a * (p : Real)⁻¹).prod := by
  induction ambient using List.reverseRecOn with
  | nil => simp
  | append_singleton ambient p ih =>
      simp only [List.sublists_concat, List.map_append, List.sum_append,
        List.map_map,  List.map_singleton, List.prod_append,
        List.prod_singleton]
      rw [show
        (fun xs : List Nat =>
          (xs.map fun (q : Nat) => a * (q : Real)⁻¹).prod) ∘
            (fun xs => xs ++ [p]) =
          fun xs =>
            (xs.map fun (q : Nat) => a * (q : Real)⁻¹).prod *
              (a * (p : Real)⁻¹) by
        funext xs
        simp [pow_succ]
        ring]
      rw [List.sum_map_mul_right, ih]
      ring

/-- Exact finite generating product for tilted sublists of the sieve factor
list. -/
theorem sieveFactorsBelow_tiltedSublistProductSum_eq
    (P : Finset Nat) (z a : Real) :
    (∑ xs ∈ (sieveFactorsBelow P z).sublists.toFinset,
      (xs.map fun (p : Nat) => a * (p : Real)⁻¹).prod) =
      ∏ p ∈ P.filter (fun p : Nat => (p : Real) < z),
        (1 + a * (p : Real)⁻¹) := by
  rw [List.sum_toFinset _ (sieveFactorsBelow_sortedGT P z).nodup.sublists]
  rw [tiltedSublistProductSum_eq]
  rw [<- List.prod_toFinset _ (sieveFactorsBelow_sortedGT P z).nodup]
  simp [sieveFactorsBelow]

private theorem rosserFailureMass_reciprocal_nonneg
    (P : Finset Nat) (xs : List Nat)
    (hprime : forall p, p ∈ P -> p.Prime) :
    0 <= rosserFailureMass P (fun p => (p : Real)⁻¹) xs := by
  apply mul_nonneg
  · apply List.prod_nonneg
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    positivity
  · exact (sieveDensityBelow_reciprocal_pos P (xs.getLastD 1) hprime).le

/-- Every upper reciprocal-prime rank correction is nonnegative. -/
theorem upperRosserFailureSumAtRank_reciprocal_nonneg
    (P : Finset Nat) (level z : Real) (r : Nat)
    (hprime : forall p, p ∈ P -> p.Prime) :
    0 <= upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
      level z r := by
  rw [upperRosserFailureSumAtRank]
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨xs, hxs, rfl⟩ := hx
  exact rosserFailureMass_reciprocal_nonneg P xs hprime

/-- Every lower reciprocal-prime rank correction is nonnegative. -/
theorem lowerRosserFailureSumAtRank_reciprocal_nonneg
    (P : Finset Nat) (level z : Real) (r : Nat)
    (hprime : forall p, p ∈ P -> p.Prime) :
    0 <= lowerRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
      level z r := by
  rw [lowerRosserFailureSumAtRank]
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨xs, hxs, rfl⟩ := hx
  exact rosserFailureMass_reciprocal_nonneg P xs hprime

/-- The generic first-failure sum is bounded by its multiplicative tilted
moment. -/
theorem rosserFirstFailureSum_le_seedMoment
    (checked : Nat -> Prop) (P : Finset Nat) {level z s : Real}
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) :
    rosserFirstFailureSum checked P (fun p => (p : Real)⁻¹) level z <=
      Real.exp ((3 - s) * Real.log (dimensionOneRosserSeedTilt s) +
        dimensionOneRosserSeedTilt s *
          ∑ p ∈ P.filter (fun p : Nat => (p : Real) < z),
            (p : Real)⁻¹) := by
  classical
  let a := dimensionOneRosserSeedTilt s
  let carrier := P.filter (fun p : Nat => (p : Real) < z)
  let S := ∑ p ∈ carrier, (p : Real)⁻¹
  have haPos : 0 < a := dimensionOneRosserSeedTilt_pos hsLarge
  have haOne : 1 < a := one_lt_dimensionOneRosserSeedTilt hsLarge
  have hterm : ∀ xs ∈ (sieveFactorsBelow P z).sublists.toFinset,
      (if IsFirstRosserFailure checked level xs then
          rosserFailureMass P (fun p => (p : Real)⁻¹) xs
        else 0) <=
        a ^ (3 - s) *
          (xs.map fun (p : Nat) => a * (p : Real)⁻¹).prod := by
    intro xs hxs
    by_cases hfailure : IsFirstRosserFailure checked level xs
    · rw [if_pos hfailure]
      have hsublist : List.Sublist xs (sieveFactorsBelow P z) :=
        List.mem_sublists.mp (List.mem_toFinset.mp hxs)
      have hlength := rosserFirstFailure_sub_two_lt_length checked P hprime
        hlevel hz hs hsublist hfailure
      have hrecipNonneg :
          0 <= (xs.map fun (p : Nat) => (p : Real)⁻¹).prod := by
        apply List.prod_nonneg
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        positivity
      have hmass :
          rosserFailureMass P (fun p => (p : Real)⁻¹) xs <=
            (xs.map fun (p : Nat) => (p : Real)⁻¹).prod := by
        rw [rosserFailureMass]
        exact mul_le_of_le_one_right hrecipNonneg
          (sieveDensityBelow_reciprocal_le_one P _ hprime)
      have hexponent : 0 < 3 - s + (xs.length : Real) := by
        linarith
      have hcoefficient :
          1 <= a ^ (3 - s) * a ^ xs.length := by
        calc
          1 <= a ^ (3 - s + (xs.length : Real)) :=
            (Real.one_lt_rpow haOne hexponent).le
          _ = a ^ (3 - s) * a ^ xs.length := by
            rw [Real.rpow_add haPos, Real.rpow_natCast]
      have htilted :
          (xs.map fun (p : Nat) => a * (p : Real)⁻¹).prod =
            a ^ xs.length *
              (xs.map fun (p : Nat) => (p : Real)⁻¹).prod := by
        rw [List.prod_map_mul]
        simp
      calc
        rosserFailureMass P (fun p => (p : Real)⁻¹) xs <=
            (xs.map fun (p : Nat) => (p : Real)⁻¹).prod := hmass
        _ <= (a ^ (3 - s) * a ^ xs.length) *
            (xs.map fun (p : Nat) => (p : Real)⁻¹).prod :=
          by simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hcoefficient hrecipNonneg)
        _ = a ^ (3 - s) *
            (xs.map fun (p : Nat) => a * (p : Real)⁻¹).prod := by
          rw [htilted]
          ring
    · rw [if_neg hfailure]
      exact mul_nonneg (Real.rpow_nonneg haPos.le _)
        (List.prod_nonneg (by
          intro x hx
          simp only [List.mem_map] at hx
          obtain ⟨p, hp, rfl⟩ := hx
          positivity))
  have hproduct :
      carrier.prod (fun p => 1 + a * (p : Real)⁻¹) <=
        Real.exp (a * S) := by
    calc
      carrier.prod (fun p => 1 + a * (p : Real)⁻¹) <=
          Real.exp (carrier.sum (fun p => a * (p : Real)⁻¹)) :=
        Real.prod_one_add_le_exp_sum carrier
          (fun p => mul_nonneg haPos.le (by positivity))
      _ = Real.exp (a * S) := by rw [Finset.mul_sum]
  rw [rosserFirstFailureSum]
  calc
    (∑ xs ∈ (sieveFactorsBelow P z).sublists.toFinset,
        if IsFirstRosserFailure checked level xs then
          rosserFailureMass P (fun p => (p : Real)⁻¹) xs else 0) <=
        ∑ xs ∈ (sieveFactorsBelow P z).sublists.toFinset,
          a ^ (3 - s) *
            (xs.map fun (p : Nat) => a * (p : Real)⁻¹).prod :=
      Finset.sum_le_sum hterm
    _ = a ^ (3 - s) *
        carrier.prod (fun p => 1 + a * (p : Real)⁻¹) := by
      rw [<- Finset.mul_sum,
        sieveFactorsBelow_tiltedSublistProductSum_eq]
    _ <= a ^ (3 - s) * Real.exp (a * S) :=
      mul_le_mul_of_nonneg_left hproduct (Real.rpow_nonneg haPos.le _)
    _ = Real.exp ((3 - s) * Real.log a + a * S) := by
      rw [Real.rpow_def_of_pos haPos, <- Real.exp_add]
      congr 1
      ring

/-- The upper all-rank correction satisfies the generic seed moment. -/
theorem upperRosserFailureSum_le_seedMoment
    (P : Finset Nat) {level z s : Real}
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) :
    upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
      Real.exp ((3 - s) * Real.log (dimensionOneRosserSeedTilt s) +
        dimensionOneRosserSeedTilt s *
          ∑ p ∈ P.filter (fun p : Nat => (p : Real) < z),
            (p : Real)⁻¹) := by
  rw [upperRosserFailureSum_eq_firstFailureSum]
  exact rosserFirstFailureSum_le_seedMoment UpperRosserRank P hprime
    hlevel hz hs hsLarge

/-- The lower all-rank correction satisfies the generic seed moment. -/
theorem lowerRosserFailureSum_le_seedMoment
    (P : Finset Nat) {level z s : Real}
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) :
    lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
      Real.exp ((3 - s) * Real.log (dimensionOneRosserSeedTilt s) +
        dimensionOneRosserSeedTilt s *
          ∑ p ∈ P.filter (fun p : Nat => (p : Real) < z),
            (p : Real)⁻¹) := by
  rw [lowerRosserFailureSum_eq_firstFailureSum]
  exact rosserFirstFailureSum_le_seedMoment LowerRosserRank P hprime
    hlevel hz hs hsLarge

/-- Every upper partial aggregate is at most the finite all-rank sum. -/
theorem upperRosserFailurePartialSum_le_failureSum
    (P : Finset Nat) (level z : Real) (R : Nat)
    (hprime : forall p, p ∈ P -> p.Prime) :
    upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level z R <=
      upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z := by
  rw [upperRosserFailurePartialSum, upperRosserFailureSum]
  let N := ((sieveFactorsBelow P z).length + 1) / 2
  by_cases hR : R + 1 <= N
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hR)
      (fun r hr hrSmall =>
        upperRosserFailureSumAtRank_reciprocal_nonneg P level z r hprime)
  · have hNR : N <= R + 1 := le_of_not_ge hR
    have hsum := Finset.sum_subset (Finset.range_mono hNR) (f := fun r =>
      upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹) level z r) ?_
    · exact hsum.symm.le
    · intro r hr hrN
      apply upperRosserFailureSumAtRank_eq_zero_of_length_lt
      simp only [Finset.mem_range] at hr hrN
      dsimp only [N] at hrN
      omega

/-- Every lower partial aggregate is at most the finite all-rank sum. -/
theorem lowerRosserFailurePartialSum_le_failureSum
    (P : Finset Nat) (level z : Real) (R : Nat)
    (hprime : forall p, p ∈ P -> p.Prime) :
    lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level z R <=
      lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level z := by
  rw [lowerRosserFailurePartialSum, lowerRosserFailureSum]
  let N := (sieveFactorsBelow P z).length / 2
  by_cases hR : R <= N
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc (le_refl 1) hR)
      (fun r hr hrSmall =>
        lowerRosserFailureSumAtRank_reciprocal_nonneg P level z r hprime)
  · have hNR : N <= R := le_of_not_ge hR
    have hsum := Finset.sum_subset
      (Finset.Icc_subset_Icc (le_refl 1) hNR) (f := fun r =>
        lowerRosserFailureSumAtRank P (fun p => (p : Real)⁻¹) level z r) ?_
    · exact hsum.symm.le
    · intro r hr hrN
      apply lowerRosserFailureSumAtRank_eq_zero_of_length_lt
      simp only [Finset.mem_Icc] at hr hrN
      dsimp only [N] at hrN
      omega

end

end PrimesRestrictedDigits
