import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstPairSums

/-!
# Low central-large continuation indices

This file defines the exact continuation-prime carriers for the retained low central-large
pair piece in Section 6. The continuation interval is `(q, sqrt (X / (p * q))]`; the reduced
threshold records the preceding factor-reduction error without changing that interval.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142, Eqs. (6.8)--(6.11).
-/

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstPairModulus
    (index : SectionSixFirstStrictIndex) : PNat :=
  Nat.toPNat' index.1 * Nat.toPNat' index.2

def sectionSixFirstPairTerminalThreshold
    (length : Nat) (index : SectionSixFirstStrictIndex) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  Real.sqrt (X / (sectionSixFirstPairProduct index : Real))

def sectionSixFirstPairReducedThreshold
    (length : Nat) (index : SectionSixFirstStrictIndex) : Real :=
  min (index.2 : Real)
    (sectionSixFirstPairTerminalThreshold length index)

abbrev SectionSixFirstPairContinuationIndex :=
  Sigma fun _ : SectionSixFirstStrictIndex => Nat

noncomputable def sectionSixFirstLowCentralLargeContinuationIndices
    (epsilon : Real) (length : Nat) :
    Finset SectionSixFirstPairContinuationIndex :=
  (sectionSixFirstPairPieceIndices epsilon length
      .lowCentralLarge).sigma fun index =>
    sievePrimeInterval (index.2 : Real)
      (sectionSixFirstPairTerminalThreshold length index)

@[simp] theorem mem_sectionSixFirstLowCentralLargeContinuationIndices
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstPairContinuationIndex} :
    index ∈ sectionSixFirstLowCentralLargeContinuationIndices
        epsilon length ↔
      index.1 ∈ sectionSixFirstPairPieceIndices epsilon length
        .lowCentralLarge ∧
      index.2 ∈ sievePrimeInterval (index.1.2 : Real)
        (sectionSixFirstPairTerminalThreshold length index.1) := by
  classical
  simp [sectionSixFirstLowCentralLargeContinuationIndices]

inductive SectionSixFirstLowCentralLargeContinuationPiece
  | below
  | band
  | above
  deriving DecidableEq

def sectionSixFirstLowCentralLargeContinuationMem
    (epsilon : Real) (length : Nat)
    (piece : SectionSixFirstLowCentralLargeContinuationPiece)
    (index : SectionSixFirstPairContinuationIndex) : Prop :=
  let X : Real := ((10 ^ length : Nat) : Real)
  let qr : Real := ((index.1.2 * index.2 : Nat) : Real)
  match piece with
  | .below => qr < sectionSixZTwo epsilon X
  | .band => sectionSixZTwo epsilon X ≤ qr ∧
      qr ≤ sectionSixZThree epsilon X
  | .above => sectionSixZThree epsilon X < qr

local instance sectionSixFirstLowCentralLargeContinuationMemDecidable
    (epsilon : Real) (length : Nat)
    (piece : SectionSixFirstLowCentralLargeContinuationPiece)
    (index : SectionSixFirstPairContinuationIndex) :
    Decidable (sectionSixFirstLowCentralLargeContinuationMem
      epsilon length piece index) :=
  Classical.propDecidable _

noncomputable def sectionSixFirstLowCentralLargeContinuationPieceIndices
    (epsilon : Real) (length : Nat)
    (piece : SectionSixFirstLowCentralLargeContinuationPiece) :
    Finset SectionSixFirstPairContinuationIndex :=
  (sectionSixFirstLowCentralLargeContinuationIndices epsilon length).filter
    (sectionSixFirstLowCentralLargeContinuationMem epsilon length piece)

@[simp] theorem mem_sectionSixFirstLowCentralLargeContinuationPieceIndices
    {epsilon : Real} {length : Nat}
    {piece : SectionSixFirstLowCentralLargeContinuationPiece}
    {index : SectionSixFirstPairContinuationIndex} :
    index ∈ sectionSixFirstLowCentralLargeContinuationPieceIndices
        epsilon length piece <->
      index ∈ sectionSixFirstLowCentralLargeContinuationIndices
          epsilon length ∧
        sectionSixFirstLowCentralLargeContinuationMem
          epsilon length piece index := by
  classical
  simp [sectionSixFirstLowCentralLargeContinuationPieceIndices]

theorem sectionSixFirstPair_le_terminalThreshold_iff
    {length : Nat} {index : SectionSixFirstStrictIndex} {r : Nat}
    (hp : index.1.Prime) (hq : index.2.Prime) (hr : r.Prime) :
    (r : Real) <= sectionSixFirstPairTerminalThreshold length index <->
      sectionSixFirstPairProduct index * r * r <= 10 ^ length := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let d : Real := (sectionSixFirstPairProduct index : Real)
  have hdNatPos : 0 < sectionSixFirstPairProduct index := by
    exact Nat.mul_pos hp.pos hq.pos
  have hdPos : 0 < d := by
    dsimp only [d]
    exact_mod_cast hdNatPos
  have hrPos : (0 : Real) < r := by exact_mod_cast hr.pos
  unfold sectionSixFirstPairTerminalThreshold
  change (r : Real) <= Real.sqrt (X / d) <-> _
  rw [Real.le_sqrt' hrPos]
  constructor
  · intro h
    have hreal : d * (r : Real) * (r : Real) <= X := by
      apply (le_div_iff₀ hdPos).1 at h
      nlinarith
    dsimp only [d, X] at hreal
    exact_mod_cast hreal
  · intro h
    apply (le_div_iff₀ hdPos).2
    have hreal :
        (((sectionSixFirstPairProduct index * r * r : Nat) : Real)) <=
          ((10 ^ length : Nat) : Real) := by
      exact_mod_cast h
    norm_num only [Nat.cast_mul] at hreal
    dsimp only [d, X]
    nlinarith

theorem sectionSixFirst_sievePrimeInterval_min_left (a b : Real) :
    sievePrimeInterval (min a b) b = sievePrimeInterval a b := by
  ext p
  rw [mem_sievePrimeInterval, mem_sievePrimeInterval]
  constructor
  · rintro ⟨hp, hab, hpb⟩
    refine ⟨hp, ?_, hpb⟩
    by_cases hle : a ≤ b
    · simpa [min_eq_left hle] using hab
    · exfalso
      have hba : b < a := lt_of_not_ge hle
      simp [min_eq_right hba.le] at hab
      linarith
  · rintro ⟨hp, hap, hpb⟩
    exact ⟨hp, lt_of_le_of_lt (min_le_left a b) hap, hpb⟩

theorem sectionSixFirstPairModulus_coe
    {index : SectionSixFirstStrictIndex}
    (hp : index.1.Prime) (hq : index.2.Prime) :
    (sectionSixFirstPairModulus index : Nat) =
      sectionSixFirstPairProduct index := by
  simp only [sectionSixFirstPairModulus, sectionSixFirstPairProduct,
    PNat.mul_coe]
  rw [Nat.toPNat'_coe, if_pos hp.pos, Nat.toPNat'_coe, if_pos hq.pos]

theorem sectionSixFirstLowCentralLarge_term_eq_siftedSum
    {epsilon : Real} {digit : Fin 10} {length : Nat}
    {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .lowCentralLarge) :
    sectionSixStrictPrimeTerm digit length
        (Nat.toPNat' index.1) index.2 =
      sectionSixSiftedSum digit length
        (sectionSixFirstPairModulus index) (index.2 : Real) := by
  have hfiltered : index ∈ sectionSixFirstStrictIndices epsilon length ∧
      sectionSixFirstPairMem epsilon length .lowCentralLarge index := by
    simpa [sectionSixFirstPairPieceIndices] using hindex
  have hpiece : index ∈ sectionSixFirstLowStrictIndices epsilon length ∧
      sectionSixZThree epsilon (((10 ^ length : Nat) : Real)) <
          (sectionSixFirstPairProduct index : Real) ∧
        (sectionSixFirstPairProduct index : Real) <
            sectionSixZFive epsilon (((10 ^ length : Nat) : Real)) ∧
          sectionSixZSix epsilon (((10 ^ length : Nat) : Real)) ≤
            (sectionSixFirstPairSquareProduct index : Real) := by
    simpa [sectionSixFirstPairMem] using hfiltered.2
  have hq : index.2.Prime :=
    (mem_sievePrimeInterval.mp
      (mem_sectionSixFirstSecondRepeatedIndices.mp hpiece.1).2).1
  rw [sectionSixStrictPrimeTerm_eq_siftedSum digit length
    (Nat.toPNat' index.1) hq]
  rfl

end


end PrimesRestrictedDigits
