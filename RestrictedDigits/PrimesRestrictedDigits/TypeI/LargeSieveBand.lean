import PrimesRestrictedDigits.TypeI.DecadePartition
import PrimesRestrictedDigits.TypeI.FourierInputs
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Large-sieve estimate on one Type I decimal band

This applies published Lemma 8.1 to the real-capped bands in the proof of Proposition 7.1. The
total denominator cutoff remains `d * S`, and the harmonic weight costs exactly the band
factor ten.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def typeIScaledBandPairCarrier
    (band : Finset Nat) (d : Nat) (S : Real) : Finset (Nat × Nat) :=
  (band.product (Finset.range (Nat.floor ((d : Real) * S)))).filter fun pair =>
    pair.2 < d * pair.1 ∧ pair.2.Coprime (d * pair.1)

private theorem typeIScaledBandPairCarrier_mem
    {band : Finset Nat} {d : Nat} {S : Real} {pair : Nat × Nat}
    (hpair : pair ∈ typeIScaledBandPairCarrier band d S) :
    pair.1 ∈ band ∧ pair.2 < d * pair.1 ∧
      pair.2.Coprime (d * pair.1) := by
  rcases Finset.mem_filter.mp hpair with ⟨hproduct, hdata⟩
  exact ⟨(Finset.mem_product.mp hproduct).1, hdata⟩

private theorem sum_typeIReducedFrequencyMass_eq_scaledBandPairCarrier
    (digit : Fin 10) (length d : Nat) (band : Finset Nat) (S : Real)
    (hband : ∀ q ∈ band, (q : Real) ≤ S) :
    (∑ q ∈ band, typeIReducedFrequencyMass digit length d q) =
      ∑ pair ∈ typeIScaledBandPairCarrier band d S,
        normalizedPaddedDigitFourierMagnitudeAt digit length
          ((pair.2 : Real) / ((d * pair.1 : Nat) : Real)) := by
  classical
  rw [typeIScaledBandPairCarrier, Finset.sum_filter]
  change (∑ q ∈ band, typeIReducedFrequencyMass digit length d q) =
    ∑ pair ∈ band ×ˢ Finset.range (Nat.floor ((d : Real) * S)),
      if pair.2 < d * pair.1 ∧ pair.2.Coprime (d * pair.1) then
        normalizedPaddedDigitFourierMagnitudeAt digit length
          ((pair.2 : Real) / ((d * pair.1 : Nat) : Real)) else 0
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q hq
  have hdqFloor : d * q ≤ Nat.floor ((d : Real) * S) := by
    apply Nat.le_floor
    push_cast
    exact mul_le_mul_of_nonneg_left (hband q hq) (by positivity)
  have hrange :
      (Finset.range (Nat.floor ((d : Real) * S))).filter (fun b =>
          b < d * q ∧ b.Coprime (d * q)) =
        (Finset.range (d * q)).filter (fun b => b.Coprime (d * q)) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, hb, hcop⟩
      exact ⟨hb, hcop⟩
    · rintro ⟨hb, hcop⟩
      exact ⟨hb.trans_le hdqFloor, hb, hcop⟩
  rw [typeIReducedFrequencyMass, ← hrange, Finset.sum_filter]

private theorem sum_typeIScaledBandPairCarrier_le_reducedFractionCarrier
    (digit : Fin 10) (length d : Nat) (band : Finset Nat) (S : Real)
    (hd : 0 < d) (hbandOne : ∀ q ∈ band, 1 < q)
    (hbandUpper : ∀ q ∈ band, (q : Real) ≤ S) :
    (∑ pair ∈ typeIScaledBandPairCarrier band d S,
      normalizedPaddedDigitFourierMagnitudeAt digit length
        ((pair.2 : Real) / ((d * pair.1 : Nat) : Real))) ≤
      ∑ pair ∈ reducedFractionCarrier (Nat.floor ((d : Real) * S)),
        normalizedPaddedDigitFourierMagnitudeAt digit length
          (reducedFractionValue pair) := by
  classical
  let mapPair : Nat × Nat → Nat × Nat := fun pair => (d * pair.1, pair.2)
  let source := typeIScaledBandPairCarrier band d S
  let target := reducedFractionCarrier (Nat.floor ((d : Real) * S))
  have hinjective : Set.InjOn mapPair source := by
    intro left hleft right hright heq
    change (d * left.1, left.2) = (d * right.1, right.2) at heq
    have hcomponents := Prod.mk.inj heq
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left hd hcomponents.1) hcomponents.2
  have hsubset : source.image mapPair ⊆ target := by
    intro pair hpair
    rcases Finset.mem_image.mp hpair with ⟨sourcePair, hsourcePair, rfl⟩
    rcases typeIScaledBandPairCarrier_mem hsourcePair with
      ⟨hqBand, hbLt, hbCoprime⟩
    have hqOne := hbandOne sourcePair.1 hqBand
    have hdenOne : 1 ≤ d * sourcePair.1 := by
      exact (show 1 ≤ d from hd).trans
        (Nat.le_mul_of_pos_right d (by omega))
    have hdenFloor : d * sourcePair.1 ≤ Nat.floor ((d : Real) * S) := by
      apply Nat.le_floor
      push_cast
      exact mul_le_mul_of_nonneg_left (hbandUpper sourcePair.1 hqBand)
        (by positivity)
    have hbPos : 0 < sourcePair.2 := by
      by_contra hb
      have hbZero : sourcePair.2 = 0 := Nat.eq_zero_of_not_pos hb
      have hdenEq : d * sourcePair.1 = 1 := by
        simpa [hbZero] using hbCoprime
      have hdenGt : 1 < d * sourcePair.1 :=
        hqOne.trans_le (Nat.le_mul_of_pos_left sourcePair.1 hd)
      exact hdenGt.ne hdenEq.symm
    apply mem_reducedFractionCarrier_iff.mpr
    exact ⟨hdenOne, hdenFloor, hbPos, hbLt, hbCoprime⟩
  calc
    (∑ pair ∈ typeIScaledBandPairCarrier band d S,
        normalizedPaddedDigitFourierMagnitudeAt digit length
          ((pair.2 : Real) / ((d * pair.1 : Nat) : Real))) =
        ∑ pair ∈ source,
          normalizedPaddedDigitFourierMagnitudeAt digit length
            (reducedFractionValue (mapPair pair)) := by rfl
    _ = ∑ pair ∈ source.image mapPair,
          normalizedPaddedDigitFourierMagnitudeAt digit length
            (reducedFractionValue pair) := by
      rw [Finset.sum_image hinjective]
    _ ≤ ∑ pair ∈ target,
          normalizedPaddedDigitFourierMagnitudeAt digit length
            (reducedFractionValue pair) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro pair hpairTarget hpairImage
      exact normalizedPaddedDigitFourierMagnitudeAt_nonneg _ _ _

/-- The fully reduced numerator mass is nonnegative. -/
theorem typeIReducedFrequencyMass_nonneg
    (digit : Fin 10) (length d q : Nat) :
    0 ≤ typeIReducedFrequencyMass digit length d q := by
  unfold typeIReducedFrequencyMass
  exact Finset.sum_nonneg fun b hb =>
    normalizedPaddedDigitFourierMagnitudeAt_nonneg _ _ _

private theorem sum_inv_mul_typeIReducedFrequencyMass_le_largeSieve
    (digit : Fin 10) (length d : Nat) (band : Finset Nat) (S : Real)
    (hd : d ∈ Nat.divisors 10) (hS : 0 ≤ S)
    (hband : ∀ q ∈ band,
      1 < q ∧ q.Coprime 10 ∧ S / 10 < (q : Real) ∧ (q : Real) ≤ S) :
    (∑ q ∈ band,
      (1 / (q : Real)) * typeIReducedFrequencyMass digit length d q) ≤
      (10 / S) * largeSieveConstant *
        (((d : Real) * S) ^ (54 / 77 : Real) +
          ((d : Real) * S) ^ 2 *
            (((10 ^ length : Nat) : Real) ^ (-(50 / 77 : Real)))) := by
  classical
  rcases band.eq_empty_or_nonempty with hbandEmpty | hbandNonempty
  · rw [hbandEmpty]
    simp only [Finset.sum_empty]
    exact mul_nonneg
      (mul_nonneg (div_nonneg (by norm_num) hS)
        (by unfold largeSieveConstant; positivity))
      (add_nonneg (Real.rpow_nonneg (mul_nonneg (by positivity) hS) _)
        (mul_nonneg (by positivity) (by positivity)))
  obtain ⟨q0, hq0Band⟩ := hbandNonempty
  rcases hband q0 hq0Band with ⟨hq0One, _, _, hq0S⟩
  have hSPos : 0 < S := by
    exact (by exact_mod_cast (by omega : 0 < q0) : (0 : Real) < q0).trans_le
      hq0S
  have hdPos : 0 < d := Nat.pos_of_ne_zero
    (ne_zero_of_dvd_ne_zero (by norm_num) (Nat.dvd_of_mem_divisors hd))
  have hcutoff : (1 : Real) ≤ (d : Real) * S := by
    have hq0Cast : (1 : Real) ≤ q0 := by
      exact_mod_cast (by omega : 1 ≤ q0)
    calc
      (1 : Real) ≤ (d : Real) * q0 := by
        nlinarith [show (1 : Real) ≤ d by exact_mod_cast hdPos]
      _ ≤ (d : Real) * S :=
        mul_le_mul_of_nonneg_left hq0S (by positivity)
  have hmass :
      (∑ q ∈ band, typeIReducedFrequencyMass digit length d q) ≤
        largeSieveConstant *
          (((d : Real) * S) ^ (54 / 77 : Real) +
            ((d : Real) * S) ^ 2 *
              (((10 ^ length : Nat) : Real) ^ (-(50 / 77 : Real)))) := by
    rw [sum_typeIReducedFrequencyMass_eq_scaledBandPairCarrier
      digit length d band S (fun q hq => (hband q hq).2.2.2)]
    calc
      _ ≤ ∑ pair ∈ reducedFractionCarrier (Nat.floor ((d : Real) * S)),
          normalizedPaddedDigitFourierMagnitudeAt digit length
            (reducedFractionValue pair) :=
        sum_typeIScaledBandPairCarrier_le_reducedFractionCarrier
          digit length d band S hdPos (fun q hq => (hband q hq).1)
            (fun q hq => (hband q hq).2.2.2)
      _ ≤ largeSieveConstant *
          (((d : Real) * S) ^ (54 / 77 : Real) +
            ((d : Real) * S) ^ 2 *
              (((10 ^ length : Nat) : Real) ^ (-(50 / 77 : Real)))) :=
        typeILargeSieveEstimate digit length hcutoff
  have hweight (q : Nat) (hq : q ∈ band) :
      (1 / (q : Real)) ≤ 10 / S := by
    rcases hband q hq with ⟨hqOne, _, hqLower, hqUpper⟩
    have hqPos : (0 : Real) < q := by
      exact_mod_cast (by omega : 0 < q)
    apply (div_le_div_iff₀ hqPos hSPos).mpr
    nlinarith
  calc
    (∑ q ∈ band,
        (1 / (q : Real)) * typeIReducedFrequencyMass digit length d q) ≤
        ∑ q ∈ band,
          (10 / S) * typeIReducedFrequencyMass digit length d q := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_right (hweight q hq)
        (typeIReducedFrequencyMass_nonneg digit length d q)
    _ = (10 / S) *
        ∑ q ∈ band, typeIReducedFrequencyMass digit length d q := by
      rw [Finset.mul_sum]
    _ ≤ (10 / S) *
        (largeSieveConstant *
          (((d : Real) * S) ^ (54 / 77 : Real) +
            ((d : Real) * S) ^ 2 *
              (((10 ^ length : Nat) : Real) ^ (-(50 / 77 : Real))))) :=
      mul_le_mul_of_nonneg_left hmass (div_nonneg (by norm_num) hS)
    _ = (10 / S) * largeSieveConstant *
        (((d : Real) * S) ^ (54 / 77 : Real) +
          ((d : Real) * S) ^ 2 *
            (((10 ^ length : Nat) : Real) ^ (-(50 / 77 : Real)))) := by
      ring

/-- Lemma 8.1 on one source band, retaining the exact divisor-scaled cutoff
and the original reciprocal denominator weight. -/
theorem sum_typeIReducedFrequencyMass_div_le_largeSieve
    (digit : Fin 10) (length d : Nat) (band : Finset Nat) (S : Real)
    (hd : d ∈ Nat.divisors 10) (hS : 0 ≤ S)
    (hband : ∀ q ∈ band,
      1 < q ∧ q.Coprime 10 ∧ S / 10 < (q : Real) ∧ (q : Real) ≤ S) :
    (∑ q ∈ band,
      typeIReducedFrequencyMass digit length d q / (q : Real)) ≤
      (10 / S) * largeSieveConstant *
        (((d : Real) * S) ^ (54 / 77 : Real) +
          ((d : Real) * S) ^ 2 *
            (((10 ^ length : Nat) : Real) ^ (-(50 / 77 : Real)))) := by
  calc
    (∑ q ∈ band,
        typeIReducedFrequencyMass digit length d q / (q : Real)) =
        ∑ q ∈ band,
          (1 / (q : Real)) * typeIReducedFrequencyMass digit length d q := by
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ _ := sum_inv_mul_typeIReducedFrequencyMass_le_largeSieve
      digit length d band S hd hS hband

end

end PrimesRestrictedDigits
