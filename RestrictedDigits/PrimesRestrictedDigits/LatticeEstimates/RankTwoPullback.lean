import PrimesRestrictedDigits.LatticeEstimates.DilatedFullLattice
import PrimesRestrictedDigits.LatticeEstimates.RankTwoIntegralSpan
import Mathlib.Algebra.BigOperators.Fin

/-!
# Pulling a rank-two coordinate plane back to the integer lattice

This packages the first two vectors of an integral basis of a directionally
dilated full lattice, as required in the repaired proof of
`MAYNARD-PRD-PUBLISHED`, Lemma 13.2, pp. 193--195.
-/

noncomputable section

open scoped BigOperators

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/-- Pull a dilated-lattice point back into the standard full integer lattice. -/
def pullbackToFullIntegerLattice (u : E) (scale : Real)
    (hu : u ≠ 0) (hscale : scale ≠ 0)
    (x : dilatedFullIntegerLattice u scale hu hscale) :
    fullIntegerLattice :=
  (ZLattice.comap_equiv Real fullIntegerLattice
    (directionalDilationContinuous u scale hu hscale).symm.toLinearEquiv).symm x

/-- The integer coordinates of a pulled-back dilated-lattice point. -/
def pullbackIntVector (u : E) (scale : Real)
    (hu : u ≠ 0) (hscale : scale ≠ 0)
    (x : dilatedFullIntegerLattice u scale hu hscale) : Fin 3 -> Int :=
  fullIntegerLatticeBasis.equivFun
    (pullbackToFullIntegerLattice u scale hu hscale x)

@[simp]
theorem intVectorToEuclidean_pullbackIntVector (u : E) (scale : Real)
    (hu : u ≠ 0) (hscale : scale ≠ 0)
    (x : dilatedFullIntegerLattice u scale hu hscale) :
    intVectorToEuclidean (pullbackIntVector u scale hu hscale x) =
      (directionalDilation u scale hu hscale).symm (x : E) := by
  rw [← coe_intVectorInFullIntegerLattice]
  change ((intVectorInFullIntegerLattice
      (fullIntegerLatticeBasis.equivFun
        (pullbackToFullIntegerLattice u scale hu hscale x)) :
      fullIntegerLattice) : E) = _
  have hfull : intVectorInFullIntegerLattice
      (fullIntegerLatticeBasis.equivFun
        (pullbackToFullIntegerLattice u scale hu hscale x)) =
      pullbackToFullIntegerLattice u scale hu hscale x := by
    apply fullIntegerLatticeBasis.equivFun.injective
    simp [intVectorInFullIntegerLattice]
  rw [hfull]
  apply (directionalDilation u scale hu hscale).injective
  rw [(directionalDilation u scale hu hscale).apply_symm_apply]
  let e := ZLattice.comap_equiv Real fullIntegerLattice
    (directionalDilationContinuous u scale hu hscale).symm.toLinearEquiv
  have he := e.apply_symm_apply x
  change directionalDilation u scale hu hscale
    ((e.symm x : fullIntegerLattice) : E) = (x : E)
  have heApply := ZLattice.comap_equiv_apply Real fullIntegerLattice
    (directionalDilationContinuous u scale hu hscale).symm.toLinearEquiv
    (e.symm x)
  calc
    directionalDilation u scale hu hscale
        ((e.symm x : fullIntegerLattice) : E) = (e (e.symm x) : E) := by
      exact heApply.symm
    _ = (x : E) := congrArg Subtype.val he

private theorem pullbackFirstTwo_linearIndependent (u : E) (scale : Real)
    (hu : u ≠ 0) (hscale : scale ≠ 0)
    (b : Module.Basis (Fin 3) Int
      (dilatedFullIntegerLattice u scale hu hscale)) :
    LinearIndependent Real fun i : Fin 2 =>
      intVectorToEuclidean
        (pullbackIntVector u scale hu hscale (b i.castSucc)) := by
  have hb : LinearIndependent Real fun i : Fin 3 => (b i : E) :=
    integralBasisCoe_linearIndependent
      (dilatedFullIntegerLattice u scale hu hscale) b
  have hsub : LinearIndependent Real fun i : Fin 2 =>
      (b i.castSucc : E) :=
    hb.comp Fin.castSucc (Fin.castSucc_injective 2)
  have hmap := hsub.map'
    (directionalDilation u scale hu hscale).symm.toLinearMap
    (LinearMap.ker_eq_bot.mpr
      (directionalDilation u scale hu hscale).symm.injective)
  rw [show (fun i : Fin 2 =>
      intVectorToEuclidean
        (pullbackIntVector u scale hu hscale (b i.castSucc))) =
      (directionalDilation u scale hu hscale).symm.toLinearMap ∘
        (fun i : Fin 2 => (b i.castSucc : E)) by
    funext i
    exact intVectorToEuclidean_pullbackIntVector u scale hu hscale
      (b i.castSucc)]
  exact hmap

/-- Pull back the integer span of the first two members of a full integral
basis. -/
def rankTwoPullbackOfDilatedBasis (u : E) (scale : Real)
    (hu : u ≠ 0) (hscale : scale ≠ 0)
    (b : Module.Basis (Fin 3) Int
      (dilatedFullIntegerLattice u scale hu hscale)) :
    RankTwoIntegralLattice :=
  rankTwoIntegralLatticeOfIndependentIntegerVectors
    (fun i => pullbackIntVector u scale hu hscale (b i.castSucc))
    (pullbackFirstTwo_linearIndependent u scale hu hscale b)

/-- A source integer point whose dilated third basis coordinate is zero lies
in the pulled-back rank-two lattice. -/
theorem intVector_mem_rankTwoPullbackOfDilatedBasis_of_repr_two_eq_zero
    (u : E) (scale : Real) (hu : u ≠ 0) (hscale : scale ≠ 0)
    (b : Module.Basis (Fin 3) Int
      (dilatedFullIntegerLattice u scale hu hscale))
    (z : Fin 3 -> Int)
    (hcoord : b.repr
      (intVectorInDilatedFullLattice u scale hu hscale z) 2 = 0) :
    intVectorToEuclidean z ∈
      (rankTwoPullbackOfDilatedBasis u scale hu hscale b).carrier := by
  let y := intVectorInDilatedFullLattice u scale hu hscale z
  let a : Fin 2 -> Int := fun i => b.repr y i.castSucc
  let p : Fin 2 -> Fin 3 -> Int := fun i =>
    pullbackIntVector u scale hu hscale (b i.castSucc)
  have hlast : b.repr y (Fin.last 2) = 0 := by
    simpa [y] using hcoord
  have hrepr : (∑ i : Fin 2, a i • (b i.castSucc : E)) = (y : E) := by
    have hall : (∑ i : Fin 3, b.repr y i • (b i : E)) = (y : E) := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using
        congrArg Subtype.val (b.sum_repr y)
    rw [Fin.sum_univ_castSucc, hlast, zero_smul, add_zero] at hall
    exact hall
  have heq : (∑ i : Fin 2, a i • intVectorToEuclidean (p i)) =
      intVectorToEuclidean z := by
    calc
      (∑ i : Fin 2, a i • intVectorToEuclidean (p i)) =
          ∑ i : Fin 2, a i •
            (directionalDilation u scale hu hscale).symm
              (b i.castSucc : E) := by
        apply Finset.sum_congr rfl
        intro i _
        apply congrArg (fun v : E => a i • v)
        exact intVectorToEuclidean_pullbackIntVector u scale hu hscale
          (b i.castSucc)
      _ = (directionalDilation u scale hu hscale).symm
          (∑ i : Fin 2, a i • (b i.castSucc : E)) := by
        rw [map_sum]
        simp only [map_zsmul]
      _ = (directionalDilation u scale hu hscale).symm (y : E) := by
        rw [hrepr]
      _ = intVectorToEuclidean z := by
        change (directionalDilation u scale hu hscale).symm
          ((intVectorInDilatedFullLattice u scale hu hscale z :
            dilatedFullIntegerLattice u scale hu hscale) : E) = _
        rw [coe_intVectorInDilatedFullLattice]
        exact (directionalDilation u scale hu hscale).symm_apply_apply _
  rw [rankTwoPullbackOfDilatedBasis,
    rankTwoIntegralLatticeOfIndependentIntegerVectors_carrier, ← heq]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.subset_span (Set.mem_range_self i)

end PrimesRestrictedDigits
