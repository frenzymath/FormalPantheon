import PrimesRestrictedDigits.BasicEstimates.IntegerVectors
import PrimesRestrictedDigits.LatticeEstimates.IntegralLattice
import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# The full integer lattice in Euclidean three-space

This identifies coordinatewise integer triples with the integer span of the
standard orthonormal basis. It is the full lattice used in the repaired proof
of `MAYNARD-PRD-PUBLISHED`, Lemma 13.2, pp. 193--195.
-/

noncomputable section

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/-- The standard copy of `Int^3` inside real Euclidean three-space. -/
def fullIntegerLattice : Submodule Int E :=
  Submodule.span Int
    (Set.range (EuclideanSpace.basisFun (Fin 3) Real).toBasis)

/-- The standard vectors form an integral basis of `fullIntegerLattice`. -/
def fullIntegerLatticeBasis :
    Module.Basis (Fin 3) Int fullIntegerLattice :=
  (EuclideanSpace.basisFun (Fin 3) Real).toBasis.restrictScalars Int

@[simp]
theorem coe_fullIntegerLatticeBasis (i : Fin 3) :
    ((fullIntegerLatticeBasis i : fullIntegerLattice) : E) =
      EuclideanSpace.basisFun (Fin 3) Real i := by
  exact Module.Basis.restrictScalars_apply Int
    (EuclideanSpace.basisFun (Fin 3) Real).toBasis i

noncomputable instance fullIntegerLattice_discreteTopology :
    DiscreteTopology fullIntegerLattice := by
  change DiscreteTopology
    (Submodule.span Int
      (Set.range (EuclideanSpace.basisFun (Fin 3) Real).toBasis))
  infer_instance

noncomputable instance fullIntegerLattice_isZLattice :
    IsZLattice Real fullIntegerLattice := by
  change IsZLattice Real
    (Submodule.span Int
      (Set.range (EuclideanSpace.basisFun (Fin 3) Real).toBasis))
  infer_instance

/-- The integral-basis element with prescribed standard integer coordinates. -/
def intVectorInFullIntegerLattice (z : Fin 3 -> Int) : fullIntegerLattice :=
  fullIntegerLatticeBasis.equivFun.symm z

@[simp]
theorem coe_intVectorInFullIntegerLattice (z : Fin 3 -> Int) :
    ((intVectorInFullIntegerLattice z : fullIntegerLattice) : E) =
      intVectorToEuclidean z := by
  rw [intVectorInFullIntegerLattice, Module.Basis.equivFun_symm_apply]
  ext j
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower,
    coe_fullIntegerLatticeBasis]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply]
  simp_rw [← Int.cast_smul_eq_zsmul Real]
  simp only [smul_eq_mul]
  change (∑ i : Fin 3, (z i : Real) *
    (EuclideanSpace.basisFun (Fin 3) Real i) j) = (z j : Real)
  simp [EuclideanSpace.basisFun_apply]

@[simp]
theorem fullIntegerLatticeBasis_repr_intVectorInFullIntegerLattice
    (z : Fin 3 -> Int) :
    fullIntegerLatticeBasis.repr (intVectorInFullIntegerLattice z) =
      Finsupp.equivFunOnFinite.symm z := by
  apply Finsupp.ext
  intro i
  change fullIntegerLatticeBasis.equivFun
      (fullIntegerLatticeBasis.equivFun.symm z) i = z i
  rw [LinearEquiv.apply_symm_apply]

/-- Every vector in the standard full lattice has integer coordinates. -/
theorem fullIntegerLattice_integral :
    IsIntegralSubmodule fullIntegerLattice := by
  intro x
  let z : Fin 3 -> Int := fullIntegerLatticeBasis.equivFun x
  refine ⟨z, ?_⟩
  rw [← coe_intVectorInFullIntegerLattice]
  apply congrArg Subtype.val
  exact fullIntegerLatticeBasis.equivFun.injective <| by
    simp [z, intVectorInFullIntegerLattice]

end PrimesRestrictedDigits
