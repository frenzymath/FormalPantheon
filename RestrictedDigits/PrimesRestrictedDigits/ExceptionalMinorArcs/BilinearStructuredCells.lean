import PrimesRestrictedDigits.ExceptionalMinorArcs.AnglesGeneratingLines
import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearCellCarriers
import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearGeometrySplit
import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearWeights
import PrimesRestrictedDigits.LatticeEstimates.PropositionThirteenThree

/-!
# Structured bilinear energy cells

Rich relation layers are embedded into the existing Proposition 13.3 and Proposition 13.4
carriers. The lattice subtype is exposed through an injective plain-pair image so both
branches can use the same Fourier weight.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

theorem latticeGeneratingPairWeight_eq_bilinearPairFourierWeight
    (digit : Fin 10) (length : Nat)
    (pair : Fin (10 ^ length) × Fin (10 ^ length)) :
    latticeGeneratingPairWeight digit length pair =
      bilinearPairFourierWeight digit length pair := by
  rw [latticeGeneratingPairWeight, bilinearPairFourierWeight]
  have hfirst := normalizedPaddedDigitFourierMagnitudeAt_grid
    digit length pair.1.val
  have hsecond := normalizedPaddedDigitFourierMagnitudeAt_grid
    digit length pair.2.val
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using congrArg₂ (· * ·) hfirst hsecond

/-- Proposition 13.3's subtype carrier, projected injectively to ordinary
ordered frequency pairs. -/
noncomputable def latticePropositionThirteenThreePlainPairs
    (digit : Fin 10) (length : Nat) (N K delta Q E : Real) :
    Finset (Fin (10 ^ length) × Fin (10 ^ length)) := by
  classical
  exact (latticePropositionThirteenThreePairs
    digit length N K delta Q E).image Subtype.val

@[simp]
theorem mem_latticePropositionThirteenThreePlainPairs_iff
    {digit : Fin 10} {length : Nat} {N K delta Q E : Real}
    {pair : Fin (10 ^ length) × Fin (10 ^ length)} :
    pair ∈ latticePropositionThirteenThreePlainPairs
        digit length N K delta Q E ↔
      pair ∈ latticeGeneratingPairs N K delta ∧
        pair.1 ∈ genericExceptionalFrequencies digit length ∧
        pair.2 ∈ genericExceptionalFrequencies digit length ∧
        pair.1 ∈ latticeRationalApproximationBand Q E ∧
        pair.2 ∈ latticeRationalApproximationBand Q E := by
  classical
  constructor
  · intro hpair
    rw [latticePropositionThirteenThreePlainPairs,
      Finset.mem_image] at hpair
    obtain ⟨a, ha, rfl⟩ := hpair
    have hdata := mem_latticePropositionThirteenThreePairs_iff.mp ha
    exact ⟨a.property, hdata⟩
  · rintro ⟨hgen, hfirstExceptional, hsecondExceptional,
      hfirstRational, hsecondRational⟩
    let a : LatticeGeneratingPair length N K delta := ⟨pair, hgen⟩
    apply Finset.mem_image.mpr
    refine ⟨a, ?_, rfl⟩
    apply mem_latticePropositionThirteenThreePairs_iff.mpr
    exact ⟨hfirstExceptional, hsecondExceptional,
      hfirstRational, hsecondRational⟩

/-- Projecting the Proposition 13.3 carrier does not change its mass. -/
theorem sum_latticePropositionThirteenThreePlainPairs
    (digit : Fin 10) (length : Nat) (N K delta Q E : Real) :
    (∑ pair ∈ latticePropositionThirteenThreePlainPairs
        digit length N K delta Q E,
      bilinearPairFourierWeight digit length pair) =
      latticePropositionThirteenThreeMass
        digit length N K delta Q E := by
  classical
  unfold latticePropositionThirteenThreePlainPairs
  rw [Finset.sum_image]
  · unfold latticePropositionThirteenThreeMass
    apply Finset.sum_congr rfl
    intro a ha
    exact (latticeGeneratingPairWeight_eq_bilinearPairFourierWeight
      digit length a.val).symm
  · intro a ha b hb hab
    exact Subtype.ext hab

/-- A rich pair at layer `j` lies in the lattice carrier or the line carrier
with the corrected source-facing parameters. -/
theorem mem_latticePlain_or_linePairs_of_mem_bilinearRichLayerPairs
    {digit : Fin 10} {length : Nat}
    {A : Finset (Fin (10 ^ length))} {N Q E B : Real}
    {k j : Nat} (hN : 1 <= N)
    (hAExceptional : A ⊆ genericExceptionalFrequencies digit length)
    (hARational : A ⊆ latticeRationalApproximationBand Q E)
    (hAComparable : A ⊆ comparableMagnitudeFrequencies digit length B)
    (hKLarge : 100 * geometryOfNumbersK0 <=
      ((10 ^ k : Nat) : Real) /
        (20 * bilinearLayerCount length))
    {pair : Fin (10 ^ length) × Fin (10 ^ length)}
    (hpair : pair ∈ bilinearRichLayerPairs A N k j) :
    pair ∈ latticePropositionThirteenThreePlainPairs digit length
          (10 * N)
          ((((10 ^ k : Nat) : Real) /
            (20 * bilinearLayerCount length)) / 2000)
          (10 * bilinearLayerWidth length N j) Q E ∨
      pair ∈ lineGeneratingPairs
        (comparableMagnitudeFrequencies digit length B)
        (10 * bilinearLayerWidth length N j) (10 * N)
        ((((10 ^ k : Nat) : Real) /
          (20 * bilinearLayerCount length)) / 2000) := by
  have hrich := mem_bilinearRichLayerPairs_iff.mp hpair
  have hcell := mem_bilinearEnergyIndexPairs_iff.mp hrich.1
  have hdelta : 0 < bilinearLayerWidth length N j :=
    bilinearLayerWidth_pos (zero_lt_one.trans_le hN) j
  have hrelation :
      bilinearLayerWidth length N j *
          (((10 ^ k : Nat) : Real) /
            (20 * bilinearLayerCount length)) * N ^ 2 <=
        ((bilinearRelationPoints pair.1 pair.2 N
          (bilinearLayerWidth length N j)).card : Real) := by
    rw [← bilinearClosePairCount_eq_card_relationPoints]
    nlinarith [hrich.2]
  have hsplit := latticeGenerating_or_lineGenerating_of_relationPoints
    (Nat.pow_pos (by norm_num : 0 < 10)) pair.1 pair.2 hN hdelta hKLarge
      hrelation
  rcases hsplit with hlattice | hline
  · left
    apply mem_latticePropositionThirteenThreePlainPairs_iff.mpr
    exact ⟨hlattice,
      hAExceptional hcell.1,
      hAExceptional hcell.2.1,
      hARational hcell.1,
      hARational hcell.2.1⟩
  · right
    apply mem_lineGeneratingPairs.mpr
    exact ⟨hAComparable hcell.1,
      hAComparable hcell.2.1, hline⟩

/-- The Fourier weight of a rich layer is bounded by the sum of the two
existing structured masses. -/
theorem sum_bilinearRichLayerPairs_le_structuredMass
    {digit : Fin 10} {length : Nat}
    {A : Finset (Fin (10 ^ length))} {N Q E B : Real}
    {k j : Nat} (hN : 1 <= N)
    (hAExceptional : A ⊆ genericExceptionalFrequencies digit length)
    (hARational : A ⊆ latticeRationalApproximationBand Q E)
    (hAComparable : A ⊆ comparableMagnitudeFrequencies digit length B)
    (hKLarge : 100 * geometryOfNumbersK0 <=
      ((10 ^ k : Nat) : Real) /
        (20 * bilinearLayerCount length)) :
    (∑ pair ∈ bilinearRichLayerPairs A N k j,
      bilinearPairFourierWeight digit length pair) <=
      latticePropositionThirteenThreeMass digit length
          (10 * N)
          ((((10 ^ k : Nat) : Real) /
            (20 * bilinearLayerCount length)) / 2000)
          (10 * bilinearLayerWidth length N j) Q E +
        lineGeneratingBandWeightSum digit length B
          (10 * bilinearLayerWidth length N j) (10 * N)
          ((((10 ^ k : Nat) : Real) /
            (20 * bilinearLayerCount length)) / 2000) := by
  classical
  let rich := bilinearRichLayerPairs A N k j
  let lattice := latticePropositionThirteenThreePlainPairs digit length
    (10 * N)
    ((((10 ^ k : Nat) : Real) /
      (20 * bilinearLayerCount length)) / 2000)
    (10 * bilinearLayerWidth length N j) Q E
  let line := lineGeneratingPairs
    (comparableMagnitudeFrequencies digit length B)
    (10 * bilinearLayerWidth length N j) (10 * N)
    ((((10 ^ k : Nat) : Real) /
      (20 * bilinearLayerCount length)) / 2000)
  have hfirst : rich.filter (fun pair => pair ∈ lattice) ⊆ lattice := by
    intro pair hpair
    exact (Finset.mem_filter.mp hpair).2
  have hsecond : rich.filter (fun pair => pair ∉ lattice) ⊆ line := by
    intro pair hpair
    have hdata := Finset.mem_filter.mp hpair
    have hclassified :=
      mem_latticePlain_or_linePairs_of_mem_bilinearRichLayerPairs
        hN hAExceptional hARational hAComparable hKLarge hdata.1
    exact hclassified.resolve_left hdata.2
  have hfirstSum :
      (∑ pair ∈ rich.filter (fun pair => pair ∈ lattice),
        bilinearPairFourierWeight digit length pair) <=
        ∑ pair ∈ lattice, bilinearPairFourierWeight digit length pair := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hfirst
      (fun pair hp hnot => bilinearPairFourierWeight_nonneg digit length pair)
  have hsecondSum :
      (∑ pair ∈ rich.filter (fun pair => pair ∉ lattice),
        bilinearPairFourierWeight digit length pair) <=
        ∑ pair ∈ line, bilinearPairFourierWeight digit length pair := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsecond
      (fun pair hp hnot => bilinearPairFourierWeight_nonneg digit length pair)
  calc
    (∑ pair ∈ rich, bilinearPairFourierWeight digit length pair) =
        (∑ pair ∈ rich.filter (fun pair => pair ∈ lattice),
          bilinearPairFourierWeight digit length pair) +
        ∑ pair ∈ rich.filter (fun pair => pair ∉ lattice),
          bilinearPairFourierWeight digit length pair := by
      simpa only using (rich.sum_filter_add_sum_filter_not
        (fun pair => pair ∈ lattice)
        (bilinearPairFourierWeight digit length)).symm
    _ <= (∑ pair ∈ lattice, bilinearPairFourierWeight digit length pair) +
        ∑ pair ∈ line, bilinearPairFourierWeight digit length pair :=
      add_le_add hfirstSum hsecondSum
    _ = latticePropositionThirteenThreeMass digit length
          (10 * N)
          ((((10 ^ k : Nat) : Real) /
            (20 * bilinearLayerCount length)) / 2000)
          (10 * bilinearLayerWidth length N j) Q E +
        lineGeneratingBandWeightSum digit length B
          (10 * bilinearLayerWidth length N j) (10 * N)
          ((((10 ^ k : Nat) : Real) /
            (20 * bilinearLayerCount length)) / 2000) := by
      rw [show (∑ pair ∈ lattice,
          bilinearPairFourierWeight digit length pair) =
          latticePropositionThirteenThreeMass digit length
            (10 * N)
            ((((10 ^ k : Nat) : Real) /
              (20 * bilinearLayerCount length)) / 2000)
            (10 * bilinearLayerWidth length N j) Q E by
        exact sum_latticePropositionThirteenThreePlainPairs
          digit length _ _ _ Q E]
      rfl

end PrimesRestrictedDigits
