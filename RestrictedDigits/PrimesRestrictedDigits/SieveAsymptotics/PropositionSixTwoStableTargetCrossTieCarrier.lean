import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatterns
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectQuarterTieCardinality

/-!
# Proposition 6.2 target cross-tie carrier

A displayed/residual prime-value tie in a successful Proposition 6.2 reverse decoder enters
the common fixed-quarter squareful carrier. The strict lower endpoint is half the weak
displayed theta-gap exponent.

Source: `MAYNARD-PRD-PUBLISHED`, proof of Lemma 7.3, pp. 149--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A displayed/off-range tie above the weak exponent-`eta` source endpoint
lies in the common quarter-split carrier with strict lower exponent
`eta / 2`. -/
theorem propositionSixTwoStableTarget_crossTie_mem_quarterTieCarrier
    {X eta : Real} {ell M N : Nat} {C : Finset Nat}
    {j : Fin ell}
    {pattern : PropositionSixTwoStablePattern ell M}
    {factors : Fin (ell + pattern.1.1) -> Nat}
    (heta : 0 < eta)
    (hprime : forall z, (factors z).Prime)
    (hproduct : primeTupleProduct factors = N)
    (hmonotone : Monotone factors)
    (hoffRangeOrder : forall z, z ∉ Set.range pattern.2 -> pattern.2 j < z)
    (hdisplayLower : forall i,
      X ^ eta <= (factors (pattern.2 i) : Real))
    (hNpos : 0 < N)
    (hNX : (N : Real) < X)
    (hNC : N ∈ C)
    (hfive : 5 <= X ^ (eta / 2))
    {i : Fin ell} {z : Fin (ell + pattern.1.1)}
    (hz : z ∉ Set.range pattern.2)
    (htie : factors (pattern.2 i) = factors z) :
    N ∈ sectionSixDirectQuarterTieCarrier C X (eta / 2) := by
  let p : Nat := factors (pattern.2 i)
  have hNone : 1 <= N := by omega
  have hX : (1 : Real) < X := by
    have hNoneReal : (1 : Real) <= (N : Real) := by exact_mod_cast hNone
    exact hNoneReal.trans_lt hNX
  have hetaHalf : eta / 2 < eta := by linarith
  have hhalfPower : X ^ (eta / 2) < X ^ eta :=
    Real.rpow_lt_rpow_of_exponent_lt hX hetaHalf
  have hfactorFive : forall w, 5 < (factors w : Real) := by
    intro w
    by_cases hw : w ∈ Set.range pattern.2
    · obtain ⟨a, rfl⟩ := hw
      exact hfive.trans_lt (hhalfPower.trans_le (hdisplayLower a))
    · calc
        (5 : Real) <= X ^ (eta / 2) := hfive
        _ < X ^ eta := hhalfPower
        _ <= (factors (pattern.2 j) : Real) := hdisplayLower j
        _ <= (factors w : Real) := by
          exact_mod_cast hmonotone (hoffRangeOrder w hw).le
  have hfactorTen : forall w, (factors w).Coprime 10 := by
    intro w
    rw [show 10 = 2 * 5 by norm_num, Nat.coprime_mul_iff_right]
    constructor
    · rw [(hprime w).coprime_iff_not_dvd]
      intro hwDvd
      have hwLe : factors w <= 2 := Nat.le_of_dvd (by norm_num) hwDvd
      have hwLeReal : (factors w : Real) <= 2 := by exact_mod_cast hwLe
      linarith [hfactorFive w]
    · rw [(hprime w).coprime_iff_not_dvd]
      intro hwDvd
      have hwLe : factors w <= 5 := Nat.le_of_dvd (by norm_num) hwDvd
      have hwLeReal : (factors w : Real) <= 5 := by exact_mod_cast hwLe
      linarith [hfactorFive w]
  have hNTen : N.Coprime 10 := by
    rw [← hproduct, primeTupleProduct, Nat.coprime_prod_left_iff]
    intro w _hw
    exact hfactorTen w
  have hpPrime : p.Prime := hprime _
  have hpSq : p * p ∣ N := by
    have hne : pattern.2 i ≠ z := by
      intro h
      exact hz ⟨i, h⟩
    have hsquare := square_dvd_primeTupleProduct_of_distinct_equal
      factors hne htie
    simpa only [p, hproduct] using hsquare
  have hpLower : X ^ (eta / 2) < (p : Real) := by
    exact hhalfPower.trans_le (hdisplayLower i)
  have hpUpper : (p : Real) <= X ^ (1 / 2 : Real) := by
    have hppNat : p * p <= N := Nat.le_of_dvd hNpos hpSq
    have hpp : (p : Real) ^ 2 < X := by
      calc
        (p : Real) ^ 2 = ((p * p : Nat) : Real) := by
          norm_num [pow_two]
        _ <= (N : Real) := by exact_mod_cast hppNat
        _ < X := hNX
    have hpSqrt : (p : Real) < Real.sqrt X :=
      Real.lt_sqrt_of_sq_lt hpp
    rw [Real.sqrt_eq_rpow] at hpSqrt
    exact hpSqrt.le
  rw [mem_sectionSixDirectQuarterTieCarrier]
  rcases le_or_gt (p : Real) (X ^ (1 / 4 : Real)) with hpSmall | hpLarge
  · left
    exact mem_sectionSixRepeatedCoprimeSquarefulCarrier.mpr
      ⟨hNC, hNTen, p,
        mem_sievePrimeInterval.mpr ⟨hpPrime, hpLower, hpSmall⟩, hpSq⟩
  · right
    exact mem_sectionSixRepeatedSquarefulCarrier.mpr
      ⟨hNC, hNpos, p,
        mem_sievePrimeInterval.mpr ⟨hpPrime, hpLarge, hpUpper⟩, hpSq⟩

end

end PrimesRestrictedDigits
