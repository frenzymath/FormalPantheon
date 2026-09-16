import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralLargeIndices

/-!
# Low-below continuation indices

Exact recurrence-native triple, raw quadruple, and clean quadruple carriers for the retained
low-below first-pair piece.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 143--144, Eq. (6.13) and region `R_4`.
-/

namespace PrimesRestrictedDigits

noncomputable section

abbrev SectionSixFirstLowBelowTripleIndex :=
  Sigma fun _ : SectionSixFirstStrictIndex => Nat

noncomputable def sectionSixFirstLowBelowTripleIndices
    (epsilon : Real) (length : Nat) :
    Finset SectionSixFirstLowBelowTripleIndex :=
  let X : Real := ((10 ^ length : Nat) : Real)
  (sectionSixFirstPairPieceIndices epsilon length .lowBelow).sigma
    fun index => sievePrimeInterval
      (sectionSixZOne epsilon X) (index.2 : Real)

@[simp] theorem mem_sectionSixFirstLowBelowTripleIndices
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstLowBelowTripleIndex} :
    index ∈ sectionSixFirstLowBelowTripleIndices epsilon length <->
      index.1 ∈ sectionSixFirstPairPieceIndices epsilon length .lowBelow /\
        index.2 ∈ sievePrimeInterval
          (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
          (index.1.2 : Real) := by
  classical
  simp [sectionSixFirstLowBelowTripleIndices]

def sectionSixFirstLowBelowTripleProduct
    (index : SectionSixFirstLowBelowTripleIndex) : Nat :=
  sectionSixFirstPairProduct index.1 * index.2

def sectionSixFirstLowBelowTripleModulus
    (index : SectionSixFirstLowBelowTripleIndex) : PNat :=
  sectionSixFirstPairModulus index.1 * Nat.toPNat' index.2

theorem sectionSixFirstLowBelowTripleModulus_coe
    {index : SectionSixFirstLowBelowTripleIndex}
    (hp : index.1.1.Prime) (hq : index.1.2.Prime)
    (hr : index.2.Prime) :
    (sectionSixFirstLowBelowTripleModulus index : Nat) =
      sectionSixFirstLowBelowTripleProduct index := by
  simp only [sectionSixFirstLowBelowTripleModulus,
    sectionSixFirstLowBelowTripleProduct, PNat.mul_coe]
  rw [sectionSixFirstPairModulus_coe hp hq, Nat.toPNat'_coe,
    if_pos hr.pos]

abbrev SectionSixFirstLowBelowQuadrupleIndex :=
  Sigma fun _ : SectionSixFirstLowBelowTripleIndex => Nat

noncomputable def sectionSixFirstLowBelowRawQuadrupleIndices
    (epsilon : Real) (length : Nat) :
    Finset SectionSixFirstLowBelowQuadrupleIndex :=
  let X : Real := ((10 ^ length : Nat) : Real)
  (sectionSixFirstLowBelowTripleIndices epsilon length).sigma
    fun index => sievePrimeInterval
      (sectionSixZOne epsilon X) (index.2 : Real)

@[simp] theorem mem_sectionSixFirstLowBelowRawQuadrupleIndices
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstLowBelowQuadrupleIndex} :
    index ∈ sectionSixFirstLowBelowRawQuadrupleIndices epsilon length <->
      index.1 ∈ sectionSixFirstLowBelowTripleIndices epsilon length /\
        index.2 ∈ sievePrimeInterval
          (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
          (index.1.2 : Real) := by
  classical
  simp [sectionSixFirstLowBelowRawQuadrupleIndices]

def sectionSixFirstLowBelowCleanQuadrupleMem
    (epsilon : Real) (length : Nat)
    (index : SectionSixFirstLowBelowQuadrupleIndex) : Prop :=
  let X : Real := ((10 ^ length : Nat) : Real)
  let outsideFirstBand : Nat -> Prop := fun n =>
    (n : Real) < sectionSixZTwo epsilon X \/
      sectionSixZThree epsilon X < (n : Real)
  let outsideSecondBand : Nat -> Prop := fun n =>
    (n : Real) < sectionSixZFive epsilon X \/
      sectionSixZSix epsilon X < (n : Real)
  let p := index.1.1.1
  let q := index.1.1.2
  let r := index.1.2
  let s := index.2
  outsideFirstBand (p * q * r) /\
    outsideFirstBand (p * q * s) /\
    outsideFirstBand (p * r * s) /\
    outsideFirstBand (q * r * s) /\
    outsideFirstBand (p * q * r * s) /\
    outsideSecondBand (p * q * r * s)

noncomputable def sectionSixFirstLowBelowQuadrupleIndices
    (epsilon : Real) (length : Nat) :
    Finset SectionSixFirstLowBelowQuadrupleIndex :=
  by
    classical
    exact (sectionSixFirstLowBelowRawQuadrupleIndices epsilon length).filter
      (sectionSixFirstLowBelowCleanQuadrupleMem epsilon length)

@[simp] theorem mem_sectionSixFirstLowBelowQuadrupleIndices
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstLowBelowQuadrupleIndex} :
    index ∈ sectionSixFirstLowBelowQuadrupleIndices epsilon length <->
      index ∈ sectionSixFirstLowBelowRawQuadrupleIndices epsilon length /\
        sectionSixFirstLowBelowCleanQuadrupleMem epsilon length index := by
  classical
  simp [sectionSixFirstLowBelowQuadrupleIndices]

end

end PrimesRestrictedDigits
