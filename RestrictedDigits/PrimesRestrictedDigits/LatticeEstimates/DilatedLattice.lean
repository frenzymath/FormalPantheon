import PrimesRestrictedDigits.BasicEstimates.LLLFixedRankIntegralBounds
import PrimesRestrictedDigits.LatticeEstimates.DirectionalDilation
import PrimesRestrictedDigits.LatticeEstimates.IntegralLattice
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# The lattice under directional dilation

This transports the source rank-two lattice through the dilation from the
repaired proof of `MAYNARD-PRD-PUBLISHED`, Lemma 14.1.
-/

noncomputable section

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/-- The image of an integral lattice under directional dilation, represented
as the comap under the inverse equivalence. -/
def directionallyDilatedLattice (Lambda : RankTwoIntegralLattice)
    (u : E) (t : Real) (hu : u ≠ 0) (ht : t ≠ 0) : Submodule Int E :=
  ZLattice.comap Real Lambda.carrier
    (directionalDilationContinuous u t hu ht).symm.toLinearMap

noncomputable instance (Lambda : RankTwoIntegralLattice)
    (u : E) (t : Real) (hu : u ≠ 0) (ht : t ≠ 0) :
    DiscreteTopology (directionallyDilatedLattice Lambda u t hu ht) := by
  let e := directionalDilationContinuous u t hu ht
  apply ZLattice.comap_discreteTopology Real Lambda.carrier
  · exact e.symm.continuous
  · exact e.symm.injective

/-- The exact integral-linear equivalence from the original lattice to its
dilated image. -/
def directionallyDilatedLatticeEquiv (Lambda : RankTwoIntegralLattice)
    (u : E) (t : Real) (hu : u ≠ 0) (ht : t ≠ 0) :
    Lambda.carrier ≃ₗ[Int] directionallyDilatedLattice Lambda u t hu ht :=
  ZLattice.comap_equiv Real Lambda.carrier
    (directionalDilationContinuous u t hu ht).symm.toLinearEquiv

@[simp] theorem directionallyDilatedLatticeEquiv_coe
    (Lambda : RankTwoIntegralLattice)
    (u : E) (t : Real) (hu : u ≠ 0) (ht : t ≠ 0)
    (x : Lambda.carrier) :
    ((directionallyDilatedLatticeEquiv Lambda u t hu ht x :
        directionallyDilatedLattice Lambda u t hu ht) : E) =
      directionalDilation u t hu ht (x : E) :=
  rfl

/-- Transport the supplied integral basis to the dilated image lattice. -/
def directionallyDilatedBasis (Lambda : RankTwoIntegralLattice)
    (u : E) (t : Real) (hu : u ≠ 0) (ht : t ≠ 0) :
    Module.Basis (Fin 2) Int
      (directionallyDilatedLattice Lambda u t hu ht) :=
  Lambda.basis.ofZLatticeComap Real Lambda.carrier
    (directionalDilationContinuous u t hu ht).symm.toLinearEquiv

@[simp] theorem directionallyDilatedBasis_apply
    (Lambda : RankTwoIntegralLattice)
    (u : E) (t : Real) (hu : u ≠ 0) (ht : t ≠ 0) (i : Fin 2) :
    ((directionallyDilatedBasis Lambda u t hu ht i :
        directionallyDilatedLattice Lambda u t hu ht) : E) =
      directionalDilation u t hu ht (Lambda.basis i : E) := by
  rfl

/-- The dilated image admits a norm-sorted integral basis with the exact
constant-three coordinate inequality. -/
theorem exists_sortedBasis_directionallyDilatedLattice
    (Lambda : RankTwoIntegralLattice)
    (u : E) (t : Real) (hu : u ≠ 0) (ht : t ≠ 0) :
    exists b : Module.Basis (Fin 2) Int
        (directionallyDilatedLattice Lambda u t hu ht),
      Monotone (fun i => ‖(b i : E)‖) ∧
      forall a : Fin 2 -> Real,
        ∑ i, ‖a i • (b i : E)‖ <=
          3 * ‖∑ i, a i • (b i : E)‖ := by
  exact exists_sortedIntegralBasis_finTwo
    (directionallyDilatedLattice Lambda u t hu ht)
    (directionallyDilatedBasis Lambda u t hu ht)

end PrimesRestrictedDigits
