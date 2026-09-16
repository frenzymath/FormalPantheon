import PrimesRestrictedDigits.TypeI.ScalePartition
import PrimesRestrictedDigits.TypeI.SmallBandDecay

/-!
# Finite aggregation of the small Type I bands

This sums the weak-small per-band estimate over active scales and the four divisors of ten,
including the outer harmonic factor.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Beyond the uniform one-band threshold, the harmonic factor, four decimal
divisors, and active scale count consume exactly the two reserved logarithms. -/
theorem exists_harmonic_mul_sum_smallTypeIBands_le
    (saving : Real) (hsaving : 0 < saving) :
    ∃ length0 : Nat, ∀ length : Nat, length0 ≤ length →
      ∀ (digit : Fin 10) (Q : Real),
        Q ≤ (((10 ^ length : Nat) : Real) ^ (50 / 77 : Real)) *
          Real.log (((10 ^ length : Nat) : Real)) ^
            (-2 * saving - 2) →
        (harmonic (Nat.ceil Q - 1) : Real) *
            ∑ d ∈ Nat.divisors 10,
              ∑ R ∈ typeISmallDecadeScales saving length Q,
                ∑ q ∈ typeIDecadeFiber Q R,
                  typeIReducedFrequencyMass digit length d q / (q : Real) ≤
          720 * Real.log (((10 ^ length : Nat) : Real)) ^ (-saving) := by
  obtain ⟨lengthBand, hband⟩ :=
    exists_sum_typeIDecadeFiber_div_le_smallBand saving hsaving
  refine ⟨max 1 lengthBand, ?_⟩
  intro length hlength digit Q hQ
  have hlengthOne : 1 ≤ length :=
    (Nat.le_max_left 1 lengthBand).trans hlength
  have hlengthBand : lengthBand ≤ length :=
    (Nat.le_max_right 1 lengthBand).trans hlength
  let X : Real := ((10 ^ length : Nat) : Real)
  let L : Real := Real.log X
  let B : Real := 30 * L ^ (-(saving + 2))
  have hlog : 1 ≤ Real.log (((10 ^ length : Nat) : Real)) :=
    one_le_log_typeIDecimalScale hlengthOne
  have hXOne : (1 : Real) ≤ X := by
    dsimp [X]
    exact_mod_cast (Nat.one_le_pow' length 9)
  have hQX : Q ≤ X := typeILevel_le_scale hsaving hXOne hlog hQ
  have hscaleCard : ((typeIDecadeScalesBelow Q).card : Real) ≤ 3 * L :=
    card_typeIDecadeScalesBelow_cast_le_three_log hlengthOne hQX
  have hsmallCard :
      ((typeISmallDecadeScales saving length Q).card : Real) ≤ 3 * L := by
    have hnat : (typeISmallDecadeScales saving length Q).card ≤
        (typeIDecadeScalesBelow Q).card := Finset.card_filter_le _ _
    have hreal : ((typeISmallDecadeScales saving length Q).card : Real) ≤
        ((typeIDecadeScalesBelow Q).card : Real) := by
      exact_mod_cast hnat
    exact hreal.trans hscaleCard
  have hLPos : 0 < L := zero_lt_one.trans_le hlog
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg hLPos.le _)
  have hperBand (d : Nat) (hd : d ∈ Nat.divisors 10)
      (R : Real) (hR : R ∈ typeISmallDecadeScales saving length Q) :
      (∑ q ∈ typeIDecadeFiber Q R,
        typeIReducedFrequencyMass digit length d q / (q : Real)) ≤ B := by
    rcases Finset.mem_filter.mp hR with ⟨hRActive, hRUpper⟩
    exact hband length hlengthBand digit d Q R hd hRActive hRUpper
  have hfixed (d : Nat) (hd : d ∈ Nat.divisors 10) :
      (∑ R ∈ typeISmallDecadeScales saving length Q,
        ∑ q ∈ typeIDecadeFiber Q R,
          typeIReducedFrequencyMass digit length d q / (q : Real)) ≤
        3 * L * B := by
    calc
      (∑ R ∈ typeISmallDecadeScales saving length Q,
          ∑ q ∈ typeIDecadeFiber Q R,
            typeIReducedFrequencyMass digit length d q / (q : Real)) ≤
          ∑ R ∈ typeISmallDecadeScales saving length Q, B := by
        apply Finset.sum_le_sum
        intro R hR
        exact hperBand d hd R hR
      _ = ((typeISmallDecadeScales saving length Q).card : Real) * B := by
        simp
      _ ≤ (3 * L) * B := mul_le_mul_of_nonneg_right hsmallCard hB
      _ = 3 * L * B := by ring
  have hsum :
      (∑ d ∈ Nat.divisors 10,
        ∑ R ∈ typeISmallDecadeScales saving length Q,
          ∑ q ∈ typeIDecadeFiber Q R,
            typeIReducedFrequencyMass digit length d q / (q : Real)) ≤
        12 * L * B := by
    calc
      (∑ d ∈ Nat.divisors 10,
          ∑ R ∈ typeISmallDecadeScales saving length Q,
            ∑ q ∈ typeIDecadeFiber Q R,
              typeIReducedFrequencyMass digit length d q / (q : Real)) ≤
          ∑ d ∈ Nat.divisors 10, 3 * L * B := by
        apply Finset.sum_le_sum
        intro d hd
        exact hfixed d hd
      _ = 12 * L * B := by
        have hcard : (Nat.divisors 10).card = 4 := by decide
        simp [hcard]
        ring
  have hsumNonneg : 0 ≤
      ∑ d ∈ Nat.divisors 10,
        ∑ R ∈ typeISmallDecadeScales saving length Q,
          ∑ q ∈ typeIDecadeFiber Q R,
            typeIReducedFrequencyMass digit length d q / (q : Real) := by
    apply Finset.sum_nonneg
    intro d hd
    apply Finset.sum_nonneg
    intro R hR
    apply Finset.sum_nonneg
    intro q hq
    exact div_nonneg (typeIReducedFrequencyMass_nonneg digit length d q)
      (by positivity)
  have hharmonic : (harmonic (Nat.ceil Q - 1) : Real) ≤ 2 * L :=
    harmonic_ceil_sub_one_le_two_log_decimalScale hlengthOne hQX
  have hpower : L ^ 2 * L ^ (-(saving + 2)) = L ^ (-saving) := by
    calc
      L ^ 2 * L ^ (-(saving + 2)) =
          L ^ (2 : Real) * L ^ (-(saving + 2)) := by
        rw [Real.rpow_two]
      _ = L ^ ((2 : Real) + (-(saving + 2))) :=
        (Real.rpow_add hLPos _ _).symm
      _ = L ^ (-saving) := by ring_nf
  calc
    (harmonic (Nat.ceil Q - 1) : Real) *
        ∑ d ∈ Nat.divisors 10,
          ∑ R ∈ typeISmallDecadeScales saving length Q,
            ∑ q ∈ typeIDecadeFiber Q R,
              typeIReducedFrequencyMass digit length d q / (q : Real) ≤
        (2 * L) *
          ∑ d ∈ Nat.divisors 10,
            ∑ R ∈ typeISmallDecadeScales saving length Q,
              ∑ q ∈ typeIDecadeFiber Q R,
                typeIReducedFrequencyMass digit length d q / (q : Real) :=
      mul_le_mul_of_nonneg_right hharmonic hsumNonneg
    _ ≤ (2 * L) * (12 * L * B) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 720 * L ^ (-saving) := by
      dsimp [B]
      rw [show (2 * L) * (12 * L * (30 * L ^ (-(saving + 2)))) =
          720 * (L ^ 2 * L ^ (-(saving + 2))) by ring]
      rw [hpower]
    _ = 720 * Real.log (((10 ^ length : Nat) : Real)) ^ (-saving) := by
      rfl

end

end PrimesRestrictedDigits
