import PrimesRestrictedDigits.SieveAsymptotics.SectionSixSquarefulCarrierBound
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Coprime repeated-square carriers

The restricted repeated-terminal carrier is covered by coprime square progressions at the
repeated prime. Their union is bounded by the exact Type I progression errors without
identifying the repeated square with the complete state modulus.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Members of `C` in the coprime progression at the square `q^2`. -/
noncomputable def sectionSixCoprimeSquareProgression
    (C : Finset Nat) (q : Nat) : Finset Nat :=
  C.filter fun n => q * q ∣ n ∧ n.Coprime 10

@[simp] theorem mem_sectionSixCoprimeSquareProgression
    {C : Finset Nat} {q n : Nat} :
    n ∈ sectionSixCoprimeSquareProgression C q ↔
      n ∈ C ∧ q * q ∣ n ∧ n.Coprime 10 := by
  simp [sectionSixCoprimeSquareProgression]

/-- The union of coprime square progressions over the exact source interval. -/
noncomputable def sectionSixRepeatedCoprimeSquarefulCarrier
    (C : Finset Nat) (X delta theta : Real) : Finset Nat :=
  (sievePrimeInterval (X ^ delta) (X ^ theta)).biUnion
    (sectionSixCoprimeSquareProgression C)

@[simp] theorem mem_sectionSixRepeatedCoprimeSquarefulCarrier
    {C : Finset Nat} {X delta theta : Real} {n : Nat} :
    n ∈ sectionSixRepeatedCoprimeSquarefulCarrier C X delta theta ↔
      n ∈ C ∧ n.Coprime 10 ∧
        ∃ q ∈ sievePrimeInterval (X ^ delta) (X ^ theta), q * q ∣ n := by
  classical
  simp only [sectionSixRepeatedCoprimeSquarefulCarrier, Finset.mem_biUnion,
    mem_sectionSixCoprimeSquareProgression]
  constructor
  · rintro ⟨q, hq, hnC, hqSq, hnTen⟩
    exact ⟨hnC, hnTen, q, hq, hqSq⟩
  · rintro ⟨hnC, hnTen, q, hq, hqSq⟩
    exact ⟨q, hq, hnC, hqSq, hnTen⟩

/-- Coprimality with ten removes zero from the restricted squareful carrier. -/
theorem sectionSixRepeatedCoprimeSquarefulCarrier_pos
    {C : Finset Nat} {X delta theta : Real} {n : Nat}
    (hn : n ∈ sectionSixRepeatedCoprimeSquarefulCarrier C X delta theta) :
    0 < n := by
  have hnTen := (mem_sectionSixRepeatedCoprimeSquarefulCarrier.mp hn).2.1
  by_contra hnPos
  have hnZero : n = 0 := Nat.eq_zero_of_not_pos hnPos
  subst n
  norm_num [Nat.Coprime] at hnTen

/-- The square-progression cardinality is exactly its Type I main term plus
the signed progression error. -/
theorem card_sectionSixCoprimeSquareProgression_padded_eq
    (digit : Fin 10) (length q : Nat) :
    ((sectionSixCoprimeSquareProgression
      (paddedRestrictedNumbers digit length) q).card : Real) =
      (typeIProgressionDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            ((q * q : Nat) : Real) +
        realTypeIProgressionError digit length (q * q) := by
  rw [sectionSixCoprimeSquareProgression, realTypeIProgressionError]
  ring

/-- The restricted squareful union is controlled by its reciprocal-square
main term and the strict Type I progression-error sum. -/
theorem card_sectionSixRepeatedCoprimeSquarefulCarrier_padded_le
    (digit : Fin 10) (length : Nat) {delta theta Q : Real}
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta)
    (hcutoff : ∀ q,
      q ∈ sievePrimeInterval
        (((10 ^ length : Nat) : Real) ^ delta)
        (((10 ^ length : Nat) : Real) ^ theta) →
      ((q * q : Nat) : Real) < Q) :
    ((sectionSixRepeatedCoprimeSquarefulCarrier
      (paddedRestrictedNumbers digit length)
      ((10 ^ length : Nat) : Real) delta theta).card : Real) ≤
      2 * (typeIProgressionDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            (((10 ^ length : Nat) : Real) ^ delta) +
        ∑ r ∈ typeIModuliBelow Q,
          |realTypeIProgressionError digit length r| := by
  classical
  let X : Real := ((10 ^ length : Nat) : Real)
  let y : Real := X ^ delta
  let P : Finset Nat := sievePrimeInterval y (X ^ theta)
  have hcardNat :
      (P.biUnion (sectionSixCoprimeSquareProgression
        (paddedRestrictedNumbers digit length))).card ≤
        ∑ q ∈ P, (sectionSixCoprimeSquareProgression
          (paddedRestrictedNumbers digit length) q).card :=
    Finset.card_biUnion_le
  have hcardReal :
      ((P.biUnion (sectionSixCoprimeSquareProgression
        (paddedRestrictedNumbers digit length))).card : Real) ≤
        ∑ q ∈ P, ((sectionSixCoprimeSquareProgression
          (paddedRestrictedNumbers digit length) q).card : Real) := by
    exact_mod_cast hcardNat
  have hkappa : 0 ≤ (typeIProgressionDensity digit : Real) := by
    rw [typeIProgressionDensity_eq]
    split_ifs <;> norm_num
  have hmain :
      (∑ q ∈ P,
        (typeIProgressionDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real) /
              (q : Real) ^ (2 : Nat)) ≤
        2 * (typeIProgressionDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real) / y := by
    calc
      _ = ((typeIProgressionDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real)) *
          (∑ q ∈ P, 1 / (q : Real) ^ (2 : Nat)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ ((typeIProgressionDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real)) *
          (2 / y) := by
        gcongr
        exact sum_reciprocal_square_sievePrimeInterval_le (by linarith)
      _ = 2 * (typeIProgressionDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real) / y := by
        ring
  have herror :
      (∑ q ∈ P, |realTypeIProgressionError digit length (q * q)|) ≤
        ∑ r ∈ typeIModuliBelow Q,
          |realTypeIProgressionError digit length r| := by
    apply sum_abs_realTypeIProgressionError_sievePrimeSquares_le digit length hy
    intro q hq
    exact hcutoff q (by simpa only [P, y, X] using hq)
  change ((P.biUnion (sectionSixCoprimeSquareProgression
    (paddedRestrictedNumbers digit length))).card : Real) ≤ _
  calc
    _ ≤ ∑ q ∈ P, ((sectionSixCoprimeSquareProgression
        (paddedRestrictedNumbers digit length) q).card : Real) := hcardReal
    _ ≤ ∑ q ∈ P,
        ((typeIProgressionDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real) /
              (q : Real) ^ (2 : Nat) +
          |realTypeIProgressionError digit length (q * q)|) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [card_sectionSixCoprimeSquareProgression_padded_eq]
      have hcast : ((q * q : Nat) : Real) = (q : Real) ^ (2 : Nat) := by
        norm_num [pow_two]
      rw [hcast]
      gcongr
      exact le_abs_self _
    _ = (∑ q ∈ P,
          (typeIProgressionDensity digit : Real) *
              ((paddedRestrictedNumbers digit length).card : Real) /
                (q : Real) ^ (2 : Nat)) +
        ∑ q ∈ P, |realTypeIProgressionError digit length (q * q)| := by
      rw [Finset.sum_add_distrib]
    _ ≤ 2 * (typeIProgressionDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) / y +
        ∑ r ∈ typeIModuliBelow Q,
          |realTypeIProgressionError digit length r| := add_le_add hmain herror
    _ = _ := by rfl

/-- A canonical repeated carrier lies in the sharper coprime squareful
carrier. Strictness above five is used only for decimal coprimality. -/
theorem sectionSixRepeatedRepresentedCarrier_subset_coprimeSquareful
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon ≤ 1 / 64}
    {hlength : 1 ≤ length}
    {hdeltaGap : delta ≤ sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    {C : Finset Nat}
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta)
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band) :
    sectionSixRepeatedRepresentedCarrier C
        (((10 ^ length : Nat) : Real) ^ delta) state ⊆
      sectionSixRepeatedCoprimeSquarefulCarrier C
        ((10 ^ length : Nat) : Real) delta (sectionSixThetaGap epsilon) := by
  intro n hn
  have hnData := mem_sectionSixRepeatedRepresentedCarrier.mp hn
  have hrepeated :=
    (sectionSixRepeatedTerminalPredicate_eq_true state).mp hnData.1
  have hcarrier :=
    sectionSixSourceBandTerminalRepresentedCarrier_mem_data
      hy.le hstate hnData.2
  have hsquare :=
    sectionSixSourceBandTerminalRepresentedCarrier_repeatedSquare
      hy.le hstate hrepeated hnData.2
  have hnTen := weakRoughPredicate_coprime_ten_of_five_lt hy hcarrier.2.2.2
  exact mem_sectionSixRepeatedCoprimeSquarefulCarrier.mpr
    ⟨hcarrier.1, hnTen, hsquare⟩

/-- Refined natural-cardinality aggregate for one canonical source band. -/
theorem sum_card_sectionSixSourceBandRepeatedRepresentedCarrier_coprime_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (C : Finset Nat)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta) :
    (∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
        hepsilonSmall hlength hdeltaGap band,
      (sectionSixRepeatedRepresentedCarrier C
        (((10 ^ length : Nat) : Real) ^ delta) state).card) ≤
      ((5 * (Nat.ceil (1 / delta)) ^ ell) *
        2 ^ Nat.ceil (1 / delta)) *
        (sectionSixRepeatedCoprimeSquarefulCarrier C
          ((10 ^ length : Nat) : Real) delta
          (sectionSixThetaGap epsilon)).card := by
  classical
  apply sum_card_le_of_element_fiber_card
  · intro state hstate
    exact sectionSixRepeatedRepresentedCarrier_subset_coprimeSquareful hy
      (mem_sectionSixSourceBandTerminalStateFinset.mp hstate)
  · intro n hn
    exact card_sectionSixSourceBandRepeatedRepresentedCarrier_fiber_le
      region hepsilon hepsilonSmall hlength hdelta hdeltaGap band C hC hy.le n

/-- Real-cardinality form of the refined aggregate. -/
theorem sum_card_sectionSixSourceBandRepeatedRepresentedCarrier_coprime_real_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (C : Finset Nat)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta) :
    (∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
        hepsilonSmall hlength hdeltaGap band,
      ((sectionSixRepeatedRepresentedCarrier C
        (((10 ^ length : Nat) : Real) ^ delta) state).card : Real)) ≤
      (((5 * (Nat.ceil (1 / delta)) ^ ell) *
        2 ^ Nat.ceil (1 / delta) : Nat) : Real) *
        ((sectionSixRepeatedCoprimeSquarefulCarrier C
          ((10 ^ length : Nat) : Real) delta
          (sectionSixThetaGap epsilon)).card : Real) := by
  classical
  apply sum_card_le_of_element_fiber_card_real
  · intro state hstate
    exact sectionSixRepeatedRepresentedCarrier_subset_coprimeSquareful hy
      (mem_sectionSixSourceBandTerminalStateFinset.mp hstate)
  · intro n hn
    exact card_sectionSixSourceBandRepeatedRepresentedCarrier_fiber_le
      region hepsilon hepsilonSmall hlength hdelta hdeltaGap band C hC hy.le n

/-- The refined restricted aggregate composed with the finite Type I-ready
squareful cardinality bound. -/
theorem sum_card_sectionSixSourceBandRepeatedRepresentedCarrier_padded_real_le
    (digit : Fin 10) {epsilon delta Q : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta)
    (hcutoff : ∀ q,
      q ∈ sievePrimeInterval
        (((10 ^ length : Nat) : Real) ^ delta)
        (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) →
      ((q * q : Nat) : Real) < Q) :
    (∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
        hepsilonSmall hlength hdeltaGap band,
      ((sectionSixRepeatedRepresentedCarrier
        (paddedRestrictedNumbers digit length)
        (((10 ^ length : Nat) : Real) ^ delta) state).card : Real)) ≤
      (((5 * (Nat.ceil (1 / delta)) ^ ell) *
        2 ^ Nat.ceil (1 / delta) : Nat) : Real) *
        (2 * (typeIProgressionDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real) /
              (((10 ^ length : Nat) : Real) ^ delta) +
          ∑ r ∈ typeIModuliBelow Q,
            |realTypeIProgressionError digit length r|) := by
  have haggregate :=
    sum_card_sectionSixSourceBandRepeatedRepresentedCarrier_coprime_real_le
      region hepsilon hepsilonSmall hlength hdelta hdeltaGap band
      (paddedRestrictedNumbers digit length)
      (paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length) hy
  have hcard :=
    card_sectionSixRepeatedCoprimeSquarefulCarrier_padded_le
      digit length hy hcutoff
  exact haggregate.trans (mul_le_mul_of_nonneg_left hcard (by positivity))

/--
The original aggregate over the decimal ambient composed with the elementary positive
squareful bound.
-/
theorem
    sum_card_sectionSixSourceBandRepeatedRepresentedCarrier_maynardAmbient_real_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (hy : 5 ≤ ((10 ^ length : Nat) : Real) ^ delta) :
    (∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
        hepsilonSmall hlength hdeltaGap band,
      ((sectionSixRepeatedRepresentedCarrier
        (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
        (((10 ^ length : Nat) : Real) ^ delta) state).card : Real)) ≤
      (((5 * (Nat.ceil (1 / delta)) ^ ell) *
        2 ^ Nat.ceil (1 / delta) : Nat) : Real) *
        (2 * ((10 ^ length : Nat) : Real) /
          (((10 ^ length : Nat) : Real) ^ delta)) := by
  have haggregate :=
    sum_card_sectionSixSourceBandRepeatedRepresentedCarrier_real_le
      region hepsilon hepsilonSmall hlength hdelta hdeltaGap band
      (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
      (fun _ hn => hn) hy
  have hcard :=
    card_sectionSixRepeatedSquarefulCarrier_maynardAmbient_le
      (theta := sectionSixThetaGap epsilon) length (by linarith)
  exact haggregate.trans (mul_le_mul_of_nonneg_left hcard (by positivity))

end

end PrimesRestrictedDigits
