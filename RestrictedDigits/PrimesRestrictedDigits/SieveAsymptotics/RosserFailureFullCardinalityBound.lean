import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserHighSeedMoment

/-!
# Coarse finite cardinality bounds for complete Rosser failures

Every reciprocal-prime first-failure mass is at most one, so the complete finite sum is
bounded by the number of sublists of the strict factor carrier. This is a project-local
small-log fallback, not Iwaniec's factorial estimate near Eq. (8.4).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

theorem sieveFactorsBelow_length_le_ceil
    (P : Finset Nat) (z : Real) :
    (sieveFactorsBelow P z).length <= Nat.ceil z := by
  rw [sieveFactorsBelow, Finset.length_sort,
    ← Finset.card_range (Nat.ceil z)]
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_range, Nat.lt_ceil]
  exact (Finset.mem_filter.mp hp).2

private theorem list_prod_reciprocal_le_one
    (xs : List Nat) (hprime : ∀ p ∈ xs, p.Prime) :
    (xs.map (fun p : Nat => (p : Real)⁻¹)).prod <= 1 := by
  induction xs with
  | nil => simp
  | cons p xs ih =>
      have hpPrime : p.Prime := hprime p (by simp)
      have hpPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
      have hpOne : (1 : Real) <= p := by exact_mod_cast hpPrime.one_le
      have hinvLe : (p : Real)⁻¹ <= 1 :=
        (inv_le_one₀ hpPos).mpr hpOne
      have ih' : (xs.map (fun q : Nat => (q : Real)⁻¹)).prod <= 1 := by
        apply ih
        intro q hq
        exact hprime q (by simp [hq])
      have hprodNonneg : 0 <=
          (xs.map (fun q : Nat => (q : Real)⁻¹)).prod := by
        apply List.prod_nonneg
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨q, _hq, rfl⟩ := hx
        exact inv_nonneg.mpr (Nat.cast_nonneg q)
      simpa using mul_le_one₀ hinvLe hprodNonneg ih'

private theorem rosserFailureMass_reciprocal_le_one_of_sublist
    (P : Finset Nat) {z : Real} (xs : List Nat)
    (hprime : ∀ p ∈ P, p.Prime)
    (hxs : List.Sublist xs (sieveFactorsBelow P z)) :
    rosserFailureMass P (fun p => (p : Real)⁻¹) xs <= 1 := by
  have hmembers : ∀ p ∈ xs, p.Prime := by
    intro p hp
    exact hprime p ((sourceTuple_of_sublist_sieveFactorsBelow hxs).2 p hp).1
  have hprod := list_prod_reciprocal_le_one xs hmembers
  have hprodNonneg : 0 <=
      (xs.map (fun p : Nat => (p : Real)⁻¹)).prod := by
    apply List.prod_nonneg
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨p, _hp, rfl⟩ := hx
    exact inv_nonneg.mpr (Nat.cast_nonneg p)
  have hVNonneg : 0 <= sieveDensityBelow P (fun p => (p : Real)⁻¹)
      (xs.getLastD 1) := (sieveDensityBelow_reciprocal_pos P _ hprime).le
  have hVLe := sieveDensityBelow_reciprocal_le_one P (xs.getLastD 1) hprime
  unfold rosserFailureMass
  exact mul_le_one₀ hprod hVNonneg hVLe

theorem rosserFirstFailureSum_reciprocal_le_two_pow_length
    (checked : Nat -> Prop) (P : Finset Nat) (level z : Real)
    (hprime : ∀ p ∈ P, p.Prime) :
    rosserFirstFailureSum checked P (fun p => (p : Real)⁻¹) level z <=
      (2 : Real) ^ (sieveFactorsBelow P z).length := by
  classical
  let ambient := sieveFactorsBelow P z
  let carrier := ambient.sublists.toFinset
  have hterm : ∀ xs ∈ carrier,
      (if IsFirstRosserFailure checked level xs then
          rosserFailureMass P (fun p => (p : Real)⁻¹) xs else 0) <= 1 := by
    intro xs hxs
    split_ifs
    · apply rosserFailureMass_reciprocal_le_one_of_sublist P xs hprime
      exact List.mem_sublists.mp (List.mem_toFinset.mp hxs)
    · norm_num
  have hsum := Finset.sum_le_card_nsmul carrier
    (fun xs => if IsFirstRosserFailure checked level xs then
      rosserFailureMass P (fun p => (p : Real)⁻¹) xs else 0) (1 : Real) hterm
  have hcard : carrier.card = 2 ^ ambient.length := by
    dsimp [carrier]
    rw [List.toFinset_card_of_nodup
      ((List.nodup_sublists.mpr (sieveFactorsBelow_sortedGT P z).nodup))]
    exact List.length_sublists ambient
  rw [rosserFirstFailureSum]
  calc
    (∑ xs ∈ carrier,
        if IsFirstRosserFailure checked level xs then
          rosserFailureMass P (fun p => (p : Real)⁻¹) xs else 0) <=
        (carrier.card : Real) := by simpa using hsum
    _ = (2 ^ ambient.length : Nat) := by rw [hcard]
    _ = (2 : Real) ^ (sieveFactorsBelow P z).length := by
      norm_num [ambient]

theorem upperRosserFailureSum_reciprocal_le_two_pow_length
    (P : Finset Nat) (level z : Real)
    (hprime : ∀ p ∈ P, p.Prime) :
    upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
      (2 : Real) ^ (sieveFactorsBelow P z).length := by
  rw [upperRosserFailureSum_eq_firstFailureSum]
  exact rosserFirstFailureSum_reciprocal_le_two_pow_length
    UpperRosserRank P level z hprime

theorem lowerRosserFailureSum_reciprocal_le_two_pow_length
    (P : Finset Nat) (level z : Real)
    (hprime : ∀ p ∈ P, p.Prime) :
    lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
      (2 : Real) ^ (sieveFactorsBelow P z).length := by
  rw [lowerRosserFailureSum_eq_firstFailureSum]
  exact rosserFirstFailureSum_reciprocal_le_two_pow_length
    LowerRosserRank P level z hprime

theorem upperRosserFailureSum_reciprocal_le_two_pow_ceil
    (P : Finset Nat) (level z : Real)
    (hprime : ∀ p ∈ P, p.Prime) :
    upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
      (2 : Real) ^ Nat.ceil z := by
  calc
    upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
        (2 : Real) ^ (sieveFactorsBelow P z).length :=
      upperRosserFailureSum_reciprocal_le_two_pow_length P level z hprime
    _ <= (2 : Real) ^ Nat.ceil z := by
      have hpow := Nat.pow_le_pow_right (by omega : 0 < 2)
        (sieveFactorsBelow_length_le_ceil P z)
      exact_mod_cast hpow

theorem lowerRosserFailureSum_reciprocal_le_two_pow_ceil
    (P : Finset Nat) (level z : Real)
    (hprime : ∀ p ∈ P, p.Prime) :
    lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
      (2 : Real) ^ Nat.ceil z := by
  calc
    lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
        (2 : Real) ^ (sieveFactorsBelow P z).length :=
      lowerRosserFailureSum_reciprocal_le_two_pow_length P level z hprime
    _ <= (2 : Real) ^ Nat.ceil z := by
      have hpow := Nat.pow_le_pow_right (by omega : 0 < 2)
        (sieveFactorsBelow_length_le_ceil P z)
      exact_mod_cast hpow

end PrimesRestrictedDigits
