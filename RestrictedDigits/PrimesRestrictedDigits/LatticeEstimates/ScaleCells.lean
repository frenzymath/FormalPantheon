import PrimesRestrictedDigits.LatticeEstimates.SelectedDecomposition
import PrimesRestrictedDigits.GenericMinorArcs.GenericFrequencyBounds

/-!
# Fixed scale cells for the Lemma 14.3 decomposition

These finite cells partition the exceptional generating pairs after the one-time approximation
choice and the two orientation branches. Each cell fixes the five decimal scales and the two
actual decimal-smooth factors.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- The original product Fourier weight of a generating pair. -/
def latticeGeneratingPairWeight
    (digit : Fin 10) (length : Nat)
    (a : Fin (10 ^ length) × Fin (10 ^ length)) : Real :=
  normalizedPaddedDigitFourierMagnitudeAt digit length
      ((a.1.val : Real) / ((10 ^ length : Nat) : Real)) *
    normalizedPaddedDigitFourierMagnitudeAt digit length
      ((a.2.val : Real) / ((10 ^ length : Nat) : Real))

theorem latticeGeneratingPairWeight_nonneg
    (digit : Fin 10) (length : Nat)
    (a : Fin (10 ^ length) × Fin (10 ^ length)) :
    0 <= latticeGeneratingPairWeight digit length a :=
  mul_nonneg
    (normalizedPaddedDigitFourierMagnitudeAt_nonneg digit length _)
    (normalizedPaddedDigitFourierMagnitudeAt_nonneg digit length _)

/-- Exceptional generating pairs before the orientation split. -/
noncomputable def latticeGeneratingExceptionalPairs
    (digit : Fin 10) (length : Nat) (N K delta : Real) :
    Finset (LatticeGeneratingPair length N K delta) := by
  classical
  exact Finset.univ.filter fun a =>
    a.val.1 ∈ genericExceptionalFrequencies digit length ∧
      a.val.2 ∈ genericExceptionalFrequencies digit length

theorem mem_latticeGeneratingExceptionalPairs_iff
    {digit : Fin 10} {length : Nat} {N K delta : Real}
    {a : LatticeGeneratingPair length N K delta} :
    a ∈ latticeGeneratingExceptionalPairs digit length N K delta ↔
      a.val.1 ∈ genericExceptionalFrequencies digit length ∧
      a.val.2 ∈ genericExceptionalFrequencies digit length := by
  classical
  simp [latticeGeneratingExceptionalPairs]

/-- The total exceptional `B_1` mass on the left side of repaired Lemma
14.3. -/
noncomputable def latticeGeneratingExceptionalMass
    (digit : Fin 10) (length : Nat) (N K delta : Real) : Real :=
  ∑ a ∈ latticeGeneratingExceptionalPairs digit length N K delta,
    latticeGeneratingPairWeight digit length a.val

/-- The selected five-scale key in the first orientation. -/
noncomputable def latticeFirstOrientedScaleKey
    {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : LatticeFirstOrientedGeneratingPair length N K delta
      hN hK hdelta hdeltaLower) :
    LatticeDecompositionScaleKey length :=
  let w := latticeFirstOrientedApproximation N K delta hN hK hdelta
    hdeltaLower a
  let f := latticeFirstOrientedFactorization N K delta hN hK hdelta
    hdeltaLower a
  w.decompositionScaleKey (one_le_latticeApproximationScale hN hK) f

/-- The selected five-scale key in the swapped orientation. -/
noncomputable def latticeSecondOrientedScaleKey
    {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : LatticeSecondOrientedGeneratingPair length N K delta
      hN hK hdelta hdeltaLower) :
    LatticeDecompositionScaleKey length :=
  let w := latticeSecondOrientedApproximation N K delta hN hK hdelta
    hdeltaLower a
  let f := latticeSecondOrientedFactorization N K delta hN hK hdelta
    hdeltaLower a
  w.decompositionScaleKey (one_le_latticeApproximationScale hN hK) f

/-- One first-orientation cell with fixed key and actual smooth factors. -/
noncomputable def latticeFirstScaleCell
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat) :
    Finset (LatticeFirstOrientedGeneratingPair length N K delta
      hN hK hdelta hdeltaLower) := by
  classical
  exact Finset.univ.filter fun a =>
    a.val.val.1 ∈ genericExceptionalFrequencies digit length ∧
    a.val.val.2 ∈ genericExceptionalFrequencies digit length ∧
    latticeFirstOrientedScaleKey N K delta hN hK hdelta hdeltaLower a = key ∧
    (latticeFirstOrientedFactorization N K delta hN hK hdelta
      hdeltaLower a).d0 = d0 ∧
    (latticeFirstOrientedFactorization N K delta hN hK hdelta
      hdeltaLower a).d1 = d1

theorem mem_latticeFirstScaleCell_iff
    {digit : Fin 10} {length : Nat} {N K delta : Real}
    {hN : 1 <= N} {hK : 1 <= K} {hdelta : 0 < delta}
    {hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta}
    {key : LatticeDecompositionScaleKey length} {d0 d1 : Nat}
    {a : LatticeFirstOrientedGeneratingPair length N K delta
      hN hK hdelta hdeltaLower} :
    a ∈ latticeFirstScaleCell digit N K delta hN hK hdelta hdeltaLower
        key d0 d1 ↔
      a.val.val.1 ∈ genericExceptionalFrequencies digit length ∧
      a.val.val.2 ∈ genericExceptionalFrequencies digit length ∧
      latticeFirstOrientedScaleKey N K delta hN hK hdelta hdeltaLower a = key ∧
      (latticeFirstOrientedFactorization N K delta hN hK hdelta
        hdeltaLower a).d0 = d0 ∧
      (latticeFirstOrientedFactorization N K delta hN hK hdelta
        hdeltaLower a).d1 = d1 := by
  classical
  simp [latticeFirstScaleCell]

/-- One swapped-orientation cell with fixed key and actual smooth factors. -/
noncomputable def latticeSecondScaleCell
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat) :
    Finset (LatticeSecondOrientedGeneratingPair length N K delta
      hN hK hdelta hdeltaLower) := by
  classical
  exact Finset.univ.filter fun a =>
    a.val.val.1 ∈ genericExceptionalFrequencies digit length ∧
    a.val.val.2 ∈ genericExceptionalFrequencies digit length ∧
    latticeSecondOrientedScaleKey N K delta hN hK hdelta hdeltaLower a = key ∧
    (latticeSecondOrientedFactorization N K delta hN hK hdelta
      hdeltaLower a).d0 = d0 ∧
    (latticeSecondOrientedFactorization N K delta hN hK hdelta
      hdeltaLower a).d1 = d1

theorem mem_latticeSecondScaleCell_iff
    {digit : Fin 10} {length : Nat} {N K delta : Real}
    {hN : 1 <= N} {hK : 1 <= K} {hdelta : 0 < delta}
    {hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta}
    {key : LatticeDecompositionScaleKey length} {d0 d1 : Nat}
    {a : LatticeSecondOrientedGeneratingPair length N K delta
      hN hK hdelta hdeltaLower} :
    a ∈ latticeSecondScaleCell digit N K delta hN hK hdelta hdeltaLower
        key d0 d1 ↔
      a.val.val.1 ∈ genericExceptionalFrequencies digit length ∧
      a.val.val.2 ∈ genericExceptionalFrequencies digit length ∧
      latticeSecondOrientedScaleKey N K delta hN hK hdelta hdeltaLower a = key ∧
      (latticeSecondOrientedFactorization N K delta hN hK hdelta
        hdeltaLower a).d0 = d0 ∧
      (latticeSecondOrientedFactorization N K delta hN hK hdelta
        hdeltaLower a).d1 = d1 := by
  classical
  simp [latticeSecondScaleCell]

/-- The original source mass in one first-orientation cell. -/
noncomputable def latticeFirstScaleCellMass
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat) : Real :=
  ∑ a ∈ latticeFirstScaleCell digit N K delta hN hK hdelta hdeltaLower
      key d0 d1,
    latticeGeneratingPairWeight digit length a.val.val

/-- The original source mass in one swapped-orientation cell. -/
noncomputable def latticeSecondScaleCellMass
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat) : Real :=
  ∑ a ∈ latticeSecondScaleCell digit N K delta hN hK hdelta hdeltaLower
      key d0 d1,
    latticeGeneratingPairWeight digit length a.val.val

end

end PrimesRestrictedDigits
