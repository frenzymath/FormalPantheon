import PrimesRestrictedDigits.LatticeEstimates.GeneratingPoints

/-!
# Pairs generating rank-two lattices

This is the exact finite `B_1(N,K,delta)` carrier from published Proposition 13.3.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Pairs for which the canonical lattice point set is large and is not
contained in a line through the origin. -/
noncomputable def latticeGeneratingPairs
    {X : Nat} (N K delta : Real) : Finset (Fin X × Fin X) := by
  classical
  exact Finset.univ.filter fun a =>
    ∃ Lambda : RankTwoIntegralLattice,
      delta * K * N ^ 2 <=
        ((latticeGeneratingIntegerPoints
          a.1 a.2 Lambda delta N).card : Real) ∧
      LatticePointsNotContainedInLine
        (latticeGeneratingIntegerPoints a.1 a.2 Lambda delta N)

theorem mem_latticeGeneratingPairs_iff
    {X : Nat} {a : Fin X × Fin X} {N K delta : Real} :
    a ∈ latticeGeneratingPairs N K delta ↔
      ∃ Lambda : RankTwoIntegralLattice,
        delta * K * N ^ 2 <=
          ((latticeGeneratingIntegerPoints
            a.1 a.2 Lambda delta N).card : Real) ∧
        LatticePointsNotContainedInLine
          (latticeGeneratingIntegerPoints a.1 a.2 Lambda delta N) := by
  simp [latticeGeneratingPairs]

end

end PrimesRestrictedDigits
