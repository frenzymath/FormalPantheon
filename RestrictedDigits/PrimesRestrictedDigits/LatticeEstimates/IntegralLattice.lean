import PrimesRestrictedDigits.BasicEstimates.IntegerVectors
import PrimesRestrictedDigits.BasicEstimates.LLLIntegralBasis
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Rank-two integral lattices in Euclidean three-space

This is the exact lattice representation used by the repaired formalization
of `MAYNARD-PRD-PUBLISHED`, Lemma 14.1, pp. 198--201.
-/

noncomputable section

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/-- Every vector of an integer submodule has integer standard coordinates. -/
def IsIntegralSubmodule (Lambda : Submodule Int E) : Prop :=
  forall x : Lambda, exists z : Fin 3 -> Int,
    intVectorToEuclidean z = (x : E)

/-- Integrality gives unit separation in the ambient Euclidean metric. -/
theorem integralSubmodule_discreteTopology
    (Lambda : Submodule Int E) (hLambda : IsIntegralSubmodule Lambda) :
    DiscreteTopology Lambda := by
  apply DiscreteTopology.of_forall_le_dist (r := 1) zero_lt_one
  intro x y hxy
  obtain ⟨z, hz⟩ := hLambda (x - y)
  have hz0 : z ≠ 0 := by
    intro hzZero
    apply hxy
    apply Subtype.ext
    have hdiff : ((x : E) - (y : E)) = 0 := by
      simpa [hzZero] using hz.symm
    exact sub_eq_zero.mp hdiff
  rw [dist_eq_norm]
  have hnorm := one_le_norm_intVectorToEuclidean hz0
  simpa [hz] using hnorm

/-- A rank-two sublattice of `Int^3`, represented inside real Euclidean
space with an explicit integral basis. -/
structure RankTwoIntegralLattice where
  /-- The integer submodule in real Euclidean three-space. -/
  carrier : Submodule Int E
  /-- Every carrier vector has integer standard coordinates. -/
  integral : IsIntegralSubmodule carrier
  /-- The lattice has exact integral rank two. -/
  basis : Module.Basis (Fin 2) Int carrier

noncomputable instance (Lambda : RankTwoIntegralLattice) :
    DiscreteTopology Lambda.carrier :=
  integralSubmodule_discreteTopology Lambda.carrier Lambda.integral

/-- The packaged lattice is exactly the integer span of two integral vectors
whose real images are linearly independent. -/
theorem RankTwoIntegralLattice.exists_integer_basisVectors
    (Lambda : RankTwoIntegralLattice) :
    exists z : Fin 2 -> Fin 3 -> Int,
      (forall i, intVectorToEuclidean (z i) = (Lambda.basis i : E)) ∧
      LinearIndependent Real (fun i => intVectorToEuclidean (z i)) ∧
      Submodule.span Int
        (Set.range fun i => intVectorToEuclidean (z i)) = Lambda.carrier := by
  let z : Fin 2 -> Fin 3 -> Int := fun i =>
    Classical.choose (Lambda.integral (Lambda.basis i))
  have hz : forall i,
      intVectorToEuclidean (z i) = (Lambda.basis i : E) := fun i =>
    Classical.choose_spec (Lambda.integral (Lambda.basis i))
  have heq : (fun i => intVectorToEuclidean (z i)) =
      integralBasisCoe Lambda.carrier Lambda.basis := by
    funext i
    exact hz i
  refine ⟨z, hz, ?_, ?_⟩
  · rw [heq]
    exact integralBasisCoe_linearIndependent Lambda.carrier Lambda.basis
  · rw [heq]
    exact span_integralBasisCoe Lambda.carrier Lambda.basis

end PrimesRestrictedDigits
