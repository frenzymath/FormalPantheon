import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralLargeIndices

/-!
# Low central-small continuation indices

Exact recurrence-native triple, raw quadruple, and clean quadruple carriers for the retained
low central-small first-pair piece.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 143, Eq. (6.12) and region `R_3`.
-/

namespace PrimesRestrictedDigits

noncomputable section

local instance sectionSixFirstLowCentralSmallPairMemDecidable
    (epsilon : Real) (length : Nat) (piece : SectionSixFirstPairPiece)
    (index : SectionSixFirstStrictIndex) :
    Decidable (sectionSixFirstPairMem epsilon length piece index) :=
  Classical.propDecidable _

abbrev SectionSixFirstLowCentralSmallTripleIndex :=
  Sigma fun _ : SectionSixFirstStrictIndex => Nat

noncomputable def sectionSixFirstLowCentralSmallTripleIndices
    (epsilon : Real) (length : Nat) :
    Finset SectionSixFirstLowCentralSmallTripleIndex :=
  let X : Real := ((10 ^ length : Nat) : Real)
  (sectionSixFirstPairPieceIndices epsilon length .lowCentralSmall).sigma
    fun index => sievePrimeInterval
      (sectionSixZOne epsilon X) (index.2 : Real)

@[simp] theorem mem_sectionSixFirstLowCentralSmallTripleIndices
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstLowCentralSmallTripleIndex} :
    index ∈ sectionSixFirstLowCentralSmallTripleIndices epsilon length <->
      index.1 ∈ sectionSixFirstPairPieceIndices epsilon length
          .lowCentralSmall /\
        index.2 ∈ sievePrimeInterval
          (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
          (index.1.2 : Real) := by
  classical
  simp [sectionSixFirstLowCentralSmallTripleIndices]

def sectionSixFirstLowCentralSmallTripleProduct
    (index : SectionSixFirstLowCentralSmallTripleIndex) : Nat :=
  sectionSixFirstPairProduct index.1 * index.2

def sectionSixFirstLowCentralSmallTripleModulus
    (index : SectionSixFirstLowCentralSmallTripleIndex) : PNat :=
  sectionSixFirstPairModulus index.1 * Nat.toPNat' index.2

theorem sectionSixFirstLowCentralSmallTripleModulus_coe
    {index : SectionSixFirstLowCentralSmallTripleIndex}
    (hp : index.1.1.Prime) (hq : index.1.2.Prime)
    (hr : index.2.Prime) :
    (sectionSixFirstLowCentralSmallTripleModulus index : Nat) =
      sectionSixFirstLowCentralSmallTripleProduct index := by
  simp only [sectionSixFirstLowCentralSmallTripleModulus,
    sectionSixFirstLowCentralSmallTripleProduct, PNat.mul_coe]
  rw [sectionSixFirstPairModulus_coe hp hq, Nat.toPNat'_coe,
    if_pos hr.pos]

def sectionSixFirstLowCentralSmallTripleTerminalThreshold
    (length : Nat) (index : SectionSixFirstLowCentralSmallTripleIndex) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  Real.sqrt (X /
    (sectionSixFirstLowCentralSmallTripleProduct index : Real))

def sectionSixFirstLowCentralSmallTripleReducedThreshold
    (length : Nat) (index : SectionSixFirstLowCentralSmallTripleIndex) : Real :=
  min (index.2 : Real)
    (sectionSixFirstLowCentralSmallTripleTerminalThreshold length index)

theorem sectionSixFirstLowCentralSmall_le_tripleTerminalThreshold_iff
    {length : Nat} {index : SectionSixFirstLowCentralSmallTripleIndex}
    {s : Nat} (hp : index.1.1.Prime) (hq : index.1.2.Prime)
    (hr : index.2.Prime) (hs : s.Prime) :
    (s : Real) <=
        sectionSixFirstLowCentralSmallTripleTerminalThreshold length index <->
      sectionSixFirstLowCentralSmallTripleProduct index * s * s <=
        10 ^ length := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let d : Real :=
    (sectionSixFirstLowCentralSmallTripleProduct index : Real)
  have hdNatPos :
      0 < sectionSixFirstLowCentralSmallTripleProduct index := by
    exact Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos
  have hdPos : 0 < d := by
    dsimp only [d]
    exact_mod_cast hdNatPos
  have hsPos : (0 : Real) < s := by exact_mod_cast hs.pos
  unfold sectionSixFirstLowCentralSmallTripleTerminalThreshold
  change (s : Real) <= Real.sqrt (X / d) <-> _
  rw [Real.le_sqrt' hsPos]
  constructor
  · intro h
    have hreal : d * (s : Real) * (s : Real) <= X := by
      apply (le_div_iff₀ hdPos).1 at h
      nlinarith
    dsimp only [d, X] at hreal
    exact_mod_cast hreal
  · intro h
    apply (le_div_iff₀ hdPos).2
    have hreal :
        (((sectionSixFirstLowCentralSmallTripleProduct index * s * s : Nat) :
          Real)) <= ((10 ^ length : Nat) : Real) := by
      exact_mod_cast h
    norm_num only [Nat.cast_mul] at hreal
    dsimp only [d, X]
    nlinarith

abbrev SectionSixFirstLowCentralSmallQuadrupleIndex :=
  Sigma fun _ : SectionSixFirstLowCentralSmallTripleIndex => Nat

noncomputable def sectionSixFirstLowCentralSmallRawQuadrupleIndices
    (epsilon : Real) (length : Nat) :
    Finset SectionSixFirstLowCentralSmallQuadrupleIndex :=
  let X : Real := ((10 ^ length : Nat) : Real)
  (sectionSixFirstLowCentralSmallTripleIndices epsilon length).sigma
    fun index => sievePrimeInterval
      (sectionSixZOne epsilon X)
      (sectionSixFirstLowCentralSmallTripleReducedThreshold length index)

@[simp] theorem mem_sectionSixFirstLowCentralSmallRawQuadrupleIndices
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstLowCentralSmallQuadrupleIndex} :
    index ∈ sectionSixFirstLowCentralSmallRawQuadrupleIndices
        epsilon length <->
      index.1 ∈ sectionSixFirstLowCentralSmallTripleIndices epsilon length /\
        index.2 ∈ sievePrimeInterval
          (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
          (sectionSixFirstLowCentralSmallTripleReducedThreshold
            length index.1) := by
  classical
  simp [sectionSixFirstLowCentralSmallRawQuadrupleIndices]

def sectionSixFirstLowCentralSmallCleanQuadrupleMem
    (epsilon : Real) (length : Nat)
    (index : SectionSixFirstLowCentralSmallQuadrupleIndex) : Prop :=
  let X : Real := ((10 ^ length : Nat) : Real)
  let outsideFirstBand : Nat -> Nat -> Prop := fun a b =>
    ((a * b : Nat) : Real) < sectionSixZTwo epsilon X \/
      sectionSixZThree epsilon X < ((a * b : Nat) : Real)
  outsideFirstBand index.1.1.1 index.1.2 /\
    outsideFirstBand index.1.1.1 index.2 /\
    outsideFirstBand index.1.1.2 index.1.2 /\
    outsideFirstBand index.1.1.2 index.2 /\
    outsideFirstBand index.1.2 index.2

local instance sectionSixFirstLowCentralSmallCleanQuadrupleMemDecidable
    (epsilon : Real) (length : Nat)
    (index : SectionSixFirstLowCentralSmallQuadrupleIndex) :
    Decidable (sectionSixFirstLowCentralSmallCleanQuadrupleMem
      epsilon length index) :=
  Classical.propDecidable _

noncomputable def sectionSixFirstLowCentralSmallQuadrupleIndices
    (epsilon : Real) (length : Nat) :
    Finset SectionSixFirstLowCentralSmallQuadrupleIndex :=
  (sectionSixFirstLowCentralSmallRawQuadrupleIndices epsilon length).filter
    (sectionSixFirstLowCentralSmallCleanQuadrupleMem epsilon length)

@[simp] theorem mem_sectionSixFirstLowCentralSmallQuadrupleIndices
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstLowCentralSmallQuadrupleIndex} :
    index ∈ sectionSixFirstLowCentralSmallQuadrupleIndices epsilon length <->
      index ∈ sectionSixFirstLowCentralSmallRawQuadrupleIndices
          epsilon length /\
        sectionSixFirstLowCentralSmallCleanQuadrupleMem
          epsilon length index := by
  classical
  simp [sectionSixFirstLowCentralSmallQuadrupleIndices]

end


end PrimesRestrictedDigits
