import PrimesRestrictedDigits.LatticeEstimates.DecompositionErrorScale

/-!
# One selected decomposition per generating pair

The repaired proof of `MAYNARD-PRD-PUBLISHED`, Lemma 14.3 must select one primitive
approximation before summing. This module makes that choice once, partitions by orientation
with ties in the first branch, and then chooses one exact factorization in each branch.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- A generating pair together with its proof of membership in `B_1`. -/
abbrev LatticeGeneratingPair
    (length : Nat) (N K delta : Real) :=
  {a : Fin (10 ^ length) × Fin (10 ^ length) //
    a ∈ latticeGeneratingPairs N K delta}

theorem one_le_latticeApproximationScale
    {N K : Real} (hN : 1 <= N) (hK : 1 <= K) :
    1 <= N * K := by nlinarith

/-- The unique project-level choice of primitive approximation for a
generating pair. -/
noncomputable def latticeSelectedPrimitiveApproximation
    {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : LatticeGeneratingPair length N K delta) :
    LatticePrimitiveApproximation a.val.1 a.val.2 (N * K) :=
  Classical.choice <| exists_latticePrimitiveApproximation_of_mem a.property
    (Nat.one_le_pow length 10 (by norm_num)) hN hK hdelta hdeltaLower

/-- Generating pairs assigned to the first orientation, including gcd ties. -/
abbrev LatticeFirstOrientedGeneratingPair
    (length : Nat) (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta) :=
  {a : LatticeGeneratingPair length N K delta //
    (latticeSelectedPrimitiveApproximation N K delta hN hK hdelta
      hdeltaLower a).firstGcd <=
    (latticeSelectedPrimitiveApproximation N K delta hN hK hdelta
      hdeltaLower a).secondGcd}

/-- Generating pairs assigned to the strictly reversed orientation. -/
abbrev LatticeSecondOrientedGeneratingPair
    (length : Nat) (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta) :=
  {a : LatticeGeneratingPair length N K delta //
    (latticeSelectedPrimitiveApproximation N K delta hN hK hdelta
      hdeltaLower a).secondGcd <
    (latticeSelectedPrimitiveApproximation N K delta hN hK hdelta
      hdeltaLower a).firstGcd}

/-- The selected approximation in the first orientation. -/
noncomputable def latticeFirstOrientedApproximation
    {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : LatticeFirstOrientedGeneratingPair length N K delta
      hN hK hdelta hdeltaLower) :
    LatticePrimitiveApproximation a.val.val.1 a.val.val.2 (N * K) :=
  latticeSelectedPrimitiveApproximation N K delta hN hK hdelta
    hdeltaLower a.val

theorem latticeFirstOrientedApproximation_ordered
    {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : LatticeFirstOrientedGeneratingPair length N K delta
      hN hK hdelta hdeltaLower) :
    (latticeFirstOrientedApproximation N K delta hN hK hdelta
      hdeltaLower a).firstGcd <=
    (latticeFirstOrientedApproximation N K delta hN hK hdelta
      hdeltaLower a).secondGcd :=
  a.property

/-- The selected approximation after swapping the second orientation. -/
noncomputable def latticeSecondOrientedApproximation
    {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : LatticeSecondOrientedGeneratingPair length N K delta
      hN hK hdelta hdeltaLower) :
    LatticePrimitiveApproximation a.val.val.2 a.val.val.1 (N * K) :=
  (latticeSelectedPrimitiveApproximation N K delta hN hK hdelta
    hdeltaLower a.val).swap

theorem latticeSecondOrientedApproximation_ordered
    {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : LatticeSecondOrientedGeneratingPair length N K delta
      hN hK hdelta hdeltaLower) :
    (latticeSecondOrientedApproximation N K delta hN hK hdelta
      hdeltaLower a).firstGcd <=
    (latticeSecondOrientedApproximation N K delta hN hK hdelta
      hdeltaLower a).secondGcd := by
  simpa only [latticeSecondOrientedApproximation,
    LatticePrimitiveApproximation.swap_firstGcd,
    LatticePrimitiveApproximation.swap_secondGcd] using a.property.le

/-- The chosen exact factorization in the first branch. -/
noncomputable def latticeFirstOrientedFactorization
    {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : LatticeFirstOrientedGeneratingPair length N K delta
      hN hK hdelta hdeltaLower) :=
  (latticeFirstOrientedApproximation N K delta hN hK hdelta
    hdeltaLower a).factorization
      (latticeFirstOrientedApproximation_ordered N K delta hN hK hdelta
        hdeltaLower a)

/-- The chosen exact factorization in the swapped branch. -/
noncomputable def latticeSecondOrientedFactorization
    {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : LatticeSecondOrientedGeneratingPair length N K delta
      hN hK hdelta hdeltaLower) :=
  (latticeSecondOrientedApproximation N K delta hN hK hdelta
    hdeltaLower a).factorization
      (latticeSecondOrientedApproximation_ordered N K delta hN hK hdelta
        hdeltaLower a)

/-- Every selected pair belongs to exactly the weak first branch or the
strict reversed branch. -/
theorem latticeSelectedOrientation_cases
    {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : LatticeGeneratingPair length N K delta) :
    let w := latticeSelectedPrimitiveApproximation N K delta hN hK hdelta
      hdeltaLower a
    w.firstGcd <= w.secondGcd ∨ w.secondGcd < w.firstGcd := by
  exact le_or_gt _ _

end

end PrimesRestrictedDigits
