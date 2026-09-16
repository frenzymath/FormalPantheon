import PrimesRestrictedDigits.TypeI.ScaleLogBounds
import PrimesRestrictedDigits.TypeI.ScalePartition

/-!
# Finite aggregation of the large Type I bands

This sums the large-band estimate over active scales and the four divisors of ten, including
the outer harmonic factor.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The total large-band contribution, including the harmonic factor, has
the requested logarithmic saving. -/
theorem harmonic_mul_sum_largeTypeIBands_le
    (saving : Real) (digit : Fin 10) (length : Nat) (Q : Real)
    (hsaving : 0 < saving) (hlength : 1 ≤ length)
    (hQ : Q ≤ (((10 ^ length : Nat) : Real) ^ (50 / 77 : Real)) *
      Real.log (((10 ^ length : Nat) : Real)) ^ (-2 * saving - 2)) :
    (harmonic (Nat.ceil Q - 1) : Real) *
        ∑ d ∈ Nat.divisors 10,
          ∑ R ∈ typeILargeDecadeScales saving length Q,
            ∑ q ∈ typeIDecadeFiber Q R,
              typeIReducedFrequencyMass digit length d q / (q : Real) ≤
      26400 * largeSieveConstant *
        Real.log (((10 ^ length : Nat) : Real)) ^ (-saving) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let L : Real := Real.log X
  let B : Real := 1100 * largeSieveConstant * L ^ (-(saving + 2))
  have hlog : 1 ≤ Real.log (((10 ^ length : Nat) : Real)) :=
    one_le_log_typeIDecimalScale hlength
  have hXOne : (1 : Real) ≤ X := by
    dsimp [X]
    exact_mod_cast (Nat.one_le_pow' length 9)
  have hQX : Q ≤ X := typeILevel_le_scale hsaving hXOne hlog hQ
  have hscaleCard : ((typeIDecadeScalesBelow Q).card : Real) ≤ 3 * L :=
    card_typeIDecadeScalesBelow_cast_le_three_log hlength hQX
  have hlargeCard :
      ((typeILargeDecadeScales saving length Q).card : Real) ≤ 3 * L := by
    have hnat : (typeILargeDecadeScales saving length Q).card ≤
        (typeIDecadeScalesBelow Q).card := Finset.card_filter_le _ _
    have hreal : ((typeILargeDecadeScales saving length Q).card : Real) ≤
        ((typeIDecadeScalesBelow Q).card : Real) := by
      exact_mod_cast hnat
    exact hreal.trans hscaleCard
  have hLPos : 0 < L := zero_lt_one.trans_le hlog
  have hconstant : 0 ≤ largeSieveConstant := by
    unfold largeSieveConstant
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (by norm_num) hconstant)
      (Real.rpow_nonneg hLPos.le _)
  have hperBand (d : Nat) (hd : d ∈ Nat.divisors 10)
      (R : Real) (hR : R ∈ typeILargeDecadeScales saving length Q) :
      (∑ q ∈ typeIDecadeFiber Q R,
        typeIReducedFrequencyMass digit length d q / (q : Real)) ≤ B := by
    rcases Finset.mem_filter.mp hR with ⟨hRActive, hRLower⟩
    exact sum_typeIDecadeFiber_div_le_largeBand saving digit length d hd
      hsaving hlog hQ hRActive hRLower
  have hfixed (d : Nat) (hd : d ∈ Nat.divisors 10) :
      (∑ R ∈ typeILargeDecadeScales saving length Q,
        ∑ q ∈ typeIDecadeFiber Q R,
          typeIReducedFrequencyMass digit length d q / (q : Real)) ≤
        3 * L * B := by
    calc
      (∑ R ∈ typeILargeDecadeScales saving length Q,
          ∑ q ∈ typeIDecadeFiber Q R,
            typeIReducedFrequencyMass digit length d q / (q : Real)) ≤
          ∑ R ∈ typeILargeDecadeScales saving length Q, B := by
        apply Finset.sum_le_sum
        intro R hR
        exact hperBand d hd R hR
      _ = ((typeILargeDecadeScales saving length Q).card : Real) * B := by
        simp
      _ ≤ (3 * L) * B := mul_le_mul_of_nonneg_right hlargeCard hB
      _ = 3 * L * B := by ring
  have hsum :
      (∑ d ∈ Nat.divisors 10,
        ∑ R ∈ typeILargeDecadeScales saving length Q,
          ∑ q ∈ typeIDecadeFiber Q R,
            typeIReducedFrequencyMass digit length d q / (q : Real)) ≤
        12 * L * B := by
    calc
      (∑ d ∈ Nat.divisors 10,
          ∑ R ∈ typeILargeDecadeScales saving length Q,
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
        ∑ R ∈ typeILargeDecadeScales saving length Q,
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
    harmonic_ceil_sub_one_le_two_log_decimalScale hlength hQX
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
          ∑ R ∈ typeILargeDecadeScales saving length Q,
            ∑ q ∈ typeIDecadeFiber Q R,
              typeIReducedFrequencyMass digit length d q / (q : Real) ≤
        (2 * L) *
          ∑ d ∈ Nat.divisors 10,
            ∑ R ∈ typeILargeDecadeScales saving length Q,
              ∑ q ∈ typeIDecadeFiber Q R,
                typeIReducedFrequencyMass digit length d q / (q : Real) :=
      mul_le_mul_of_nonneg_right hharmonic hsumNonneg
    _ ≤ (2 * L) * (12 * L * B) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 26400 * largeSieveConstant * L ^ (-saving) := by
      dsimp [B]
      rw [show (2 * L) *
          (12 * L * (1100 * largeSieveConstant * L ^ (-(saving + 2)))) =
          26400 * largeSieveConstant *
            (L ^ 2 * L ^ (-(saving + 2))) by ring]
      rw [hpower]

end

end PrimesRestrictedDigits
