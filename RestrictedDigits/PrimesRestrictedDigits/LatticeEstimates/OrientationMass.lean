import PrimesRestrictedDigits.LatticeEstimates.ScaleCells
import PrimesRestrictedDigits.LatticeEstimates.WeightedReindex

/-!
# Exceptional mass split into two orientations

The weak first branch contains gcd ties; the second branch is strict. The sum type keeps the
branch tag, so the orientation map is injective and the outer proof pays exactly the explicit
factor two.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

abbrev LatticeFirstExceptionalOrientedPair
    (digit : Fin 10) (length : Nat) (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta) :=
  {a : LatticeFirstOrientedGeneratingPair length N K delta
      hN hK hdelta hdeltaLower //
    a.val.val.1 ∈ genericExceptionalFrequencies digit length ∧
      a.val.val.2 ∈ genericExceptionalFrequencies digit length}

abbrev LatticeSecondExceptionalOrientedPair
    (digit : Fin 10) (length : Nat) (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta) :=
  {a : LatticeSecondOrientedGeneratingPair length N K delta
      hN hK hdelta hdeltaLower //
    a.val.val.1 ∈ genericExceptionalFrequencies digit length ∧
      a.val.val.2 ∈ genericExceptionalFrequencies digit length}

noncomputable def latticeFirstOrientedExceptionalMass
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta) : Real :=
  ∑ a : LatticeFirstExceptionalOrientedPair digit length N K delta
      hN hK hdelta hdeltaLower,
    latticeGeneratingPairWeight digit length a.val.val.val

noncomputable def latticeSecondOrientedExceptionalMass
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta) : Real :=
  ∑ a : LatticeSecondExceptionalOrientedPair digit length N K delta
      hN hK hdelta hdeltaLower,
    latticeGeneratingPairWeight digit length a.val.val.val

abbrev LatticeExceptionalOrientationTarget
    (digit : Fin 10) (length : Nat) (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta) :=
  LatticeFirstExceptionalOrientedPair digit length N K delta
      hN hK hdelta hdeltaLower ⊕
    LatticeSecondExceptionalOrientedPair digit length N K delta
      hN hK hdelta hdeltaLower

def latticeExceptionalOrientationTargetPair
    {digit : Fin 10} {length : Nat} {N K delta : Real}
    {hN : 1 <= N} {hK : 1 <= K} {hdelta : 0 < delta}
    {hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta} :
    LatticeExceptionalOrientationTarget digit length N K delta
      hN hK hdelta hdeltaLower -> LatticeGeneratingPair length N K delta :=
  Sum.elim (fun a => a.val.val) (fun a => a.val.val)

def latticeExceptionalOrientationTargetWeight
    (digit : Fin 10) {length : Nat} {N K delta : Real}
    {hN : 1 <= N} {hK : 1 <= K} {hdelta : 0 < delta}
    {hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta}
    (target : LatticeExceptionalOrientationTarget digit length N K delta
      hN hK hdelta hdeltaLower) : Real :=
  latticeGeneratingPairWeight digit length
    (latticeExceptionalOrientationTargetPair target).val

noncomputable def latticeExceptionalOrientationMap
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : {a // a ∈ latticeGeneratingExceptionalPairs digit length N K delta}) :
    LatticeExceptionalOrientationTarget digit length N K delta
      hN hK hdelta hdeltaLower := by
  let w := latticeSelectedPrimitiveApproximation N K delta hN hK hdelta
    hdeltaLower a.val
  have hexceptional := mem_latticeGeneratingExceptionalPairs_iff.mp a.property
  by_cases hordered : w.firstGcd <= w.secondGcd
  · exact Sum.inl ⟨⟨a.val, hordered⟩, hexceptional⟩
  · exact Sum.inr ⟨⟨a.val, lt_of_not_ge hordered⟩, hexceptional⟩

theorem latticeExceptionalOrientationMap_pair
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : {a // a ∈ latticeGeneratingExceptionalPairs digit length N K delta}) :
    latticeExceptionalOrientationTargetPair
      (latticeExceptionalOrientationMap digit N K delta hN hK hdelta
        hdeltaLower a) = a.val := by
  unfold latticeExceptionalOrientationMap
    latticeExceptionalOrientationTargetPair
  dsimp only
  split <;> rfl

theorem latticeExceptionalOrientationMap_injective
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta) :
    Function.Injective
      (latticeExceptionalOrientationMap digit N K delta hN hK hdelta
        hdeltaLower) := by
  intro a b hab
  apply Subtype.ext
  have hpair := congrArg latticeExceptionalOrientationTargetPair hab
  simpa only [latticeExceptionalOrientationMap_pair] using hpair

theorem latticeExceptionalOrientationMap_weight
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : {a // a ∈ latticeGeneratingExceptionalPairs digit length N K delta}) :
    latticeGeneratingPairWeight digit length a.val.val =
      latticeExceptionalOrientationTargetWeight digit
        (latticeExceptionalOrientationMap digit N K delta hN hK hdelta
          hdeltaLower a) := by
  unfold latticeExceptionalOrientationTargetWeight
  rw [latticeExceptionalOrientationMap_pair]

/-- The total exceptional mass is bounded by the sum of the two disjoint
orientation masses. -/
theorem latticeGeneratingExceptionalMass_le_orientations
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta) :
    latticeGeneratingExceptionalMass digit length N K delta <=
      latticeFirstOrientedExceptionalMass digit N K delta hN hK hdelta
          hdeltaLower +
        latticeSecondOrientedExceptionalMass digit N K delta hN hK hdelta
          hdeltaLower := by
  unfold latticeGeneratingExceptionalMass
  calc
    (∑ a ∈ latticeGeneratingExceptionalPairs digit length N K delta,
      latticeGeneratingPairWeight digit length a.val) <=
        ∑ target : LatticeExceptionalOrientationTarget digit length N K delta
            hN hK hdelta hdeltaLower,
          latticeExceptionalOrientationTargetWeight digit target := by
      exact finset_sum_le_fintype_sum_of_injective
        (latticeGeneratingExceptionalPairs digit length N K delta)
        (fun a => latticeGeneratingPairWeight digit length a.val)
        (latticeExceptionalOrientationTargetWeight digit)
        (latticeExceptionalOrientationMap digit N K delta hN hK hdelta
          hdeltaLower)
        (latticeExceptionalOrientationMap_injective digit N K delta hN hK
          hdelta hdeltaLower)
        (latticeExceptionalOrientationMap_weight digit N K delta hN hK hdelta
          hdeltaLower)
        (fun target => latticeGeneratingPairWeight_nonneg digit length
          (latticeExceptionalOrientationTargetPair target).val)
    _ = latticeFirstOrientedExceptionalMass digit N K delta hN hK hdelta
          hdeltaLower +
        latticeSecondOrientedExceptionalMass digit N K delta hN hK hdelta
          hdeltaLower := by
      rw [Fintype.sum_sum_type]
      rfl

end

end PrimesRestrictedDigits
