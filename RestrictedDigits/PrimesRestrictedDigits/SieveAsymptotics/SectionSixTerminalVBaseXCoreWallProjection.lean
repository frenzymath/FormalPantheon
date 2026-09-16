import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetBaseXCore
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVFixedNormalFacts
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetPresentation
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIProjectedZeroNormal

/-!
# Projection of terminal-V literal walls

This module transports one literal wall of the terminal-V base-X core from the full sum-one
coordinate space to the canonical positive-dimensional projection used by the Type II slab
estimates.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem terminalVProjectedNormal_ne_zero_of_nonconstant
    {k : Nat} {normal : Fin (k + 1) -> Real}
    (hnonconstant : ∃ a b, normal a ≠ normal b) :
    typeIIProjectedAffineNormal normal ≠ 0 := by
  intro hzero
  have hcoeff := (typeIIProjectedAffineNormal_eq_zero_iff normal).mp hzero
  have hall : ∀ a, normal a = normal (Fin.last k) := by
    intro a
    refine Fin.lastCases rfl (fun i => ?_) a
    exact hcoeff i
  obtain ⟨a, b, hab⟩ := hnonconstant
  exact hab ((hall a).trans (hall b).symm)

private theorem terminalVProjectedWall_of_nonconstant
    {d n : Nat} (hdimension : d = n + 2)
    (x : Fin d -> Real) (hsum : (∑ i, x i) = 1)
    (normal : Fin d -> Real) (bound gamma : Real)
    (hnonconstant : ∃ a b, normal a ≠ normal b)
    (hwall : |typeIIAffineValue normal x - bound| <= gamma) :
    let cast : Fin d ≃o Fin (n + 2) := Fin.castOrderIso hdimension
    let transportedNormal : Fin (n + 2) -> Real := fun i =>
      normal (cast.symm i)
    let transportedPoint : Fin (n + 2) -> Real := fun i =>
      x (cast.symm i)
    typeIIProjectedAffineNormal transportedNormal ≠ 0 ∧
      |typeIIAffineValue (typeIIProjectedAffineNormal transportedNormal)
            (Fin.init transportedPoint) -
          typeIIProjectedAffineBound transportedNormal bound| <= gamma := by
  dsimp only
  let cast : Fin d ≃o Fin (n + 2) := Fin.castOrderIso hdimension
  let transportedNormal : Fin (n + 2) -> Real := fun i =>
    normal (cast.symm i)
  let transportedPoint : Fin (n + 2) -> Real := fun i =>
    x (cast.symm i)
  have hnonconstant' : ∃ a b,
      transportedNormal a ≠ transportedNormal b := by
    obtain ⟨a, b, hab⟩ := hnonconstant
    refine ⟨cast a, cast b, ?_⟩
    simpa only [transportedNormal, cast.symm_apply_apply] using hab
  have hprojected : typeIIProjectedAffineNormal transportedNormal ≠ 0 :=
    terminalVProjectedNormal_ne_zero_of_nonconstant hnonconstant'
  have hsum' : (∑ i, transportedPoint i) = 1 := by
    exact (Equiv.sum_comp cast.symm.toEquiv x).trans hsum
  have hcomplete :
      completeProjectedLogTuple (Fin.init transportedPoint) =
        transportedPoint :=
    completeProjectedLogTuple_init_eq_of_sum_eq_one hsum'
  have hvalueTransport :
      typeIIAffineValue transportedNormal transportedPoint =
        typeIIAffineValue normal x := by
    unfold typeIIAffineValue transportedNormal transportedPoint
    exact Equiv.sum_comp cast.symm.toEquiv (fun i => normal i * x i)
  have hvalue := typeIIAffineValue_completeProjectedLogTuple
    transportedNormal (Fin.init transportedPoint)
  rw [hcomplete] at hvalue
  have hrewrite :
      typeIIAffineValue (typeIIProjectedAffineNormal transportedNormal)
            (Fin.init transportedPoint) -
          typeIIProjectedAffineBound transportedNormal bound =
        typeIIAffineValue normal x - bound := by
    unfold typeIIProjectedAffineBound
    rw [← hvalueTransport, hvalue]
    ring
  refine ⟨hprojected, ?_⟩
  rw [hrewrite]
  exact hwall

private theorem terminalVBaseXCore_normal_nonconstant
    {epsilon delta : Real} {ell M : Nat}
    {region : Set (Fin ell -> Real)} (band : SectionSixStateBand)
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (j : Fin (sectionSixTerminalVBaseXCorePresentation sourcePresentation
      epsilon delta band pattern hinner hresidual).constraintCount)
    (hnormal : (sectionSixTerminalVBaseXCorePresentation sourcePresentation
      epsilon delta band pattern hinner hresidual).normal j ≠ 0) :
    ∃ i, (sectionSixTerminalVBaseXCorePresentation sourcePresentation
        epsilon delta band pattern hinner hresidual).normal j i ≠
      (sectionSixTerminalVBaseXCorePresentation sourcePresentation
        epsilon delta band pattern hinner hresidual).normal j
        (pattern.firstResidualPosition hresidual) := by
  unfold sectionSixTerminalVBaseXCorePresentation at hnormal ⊢
  cases j using Fin.addCases with
  | left j =>
      unfold TypeIIAffineMixedPresentation.inter at hnormal ⊢
      dsimp only at hnormal ⊢
      rw [Fin.append_left] at hnormal ⊢
      unfold TypeIIAffineMixedPresentation.liftAlongEmbedding at hnormal ⊢
      dsimp only at hnormal ⊢
      have hsourceNormal : sourcePresentation.normal j ≠ 0 := by
        intro hzero
        apply hnormal
        exact (typeIIAffineLiftNormal_eq_zero_iff
          pattern.sourcePositionEmbedding (sourcePresentation.normal j)).mpr
            hzero
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hsourceNormal
      refine ⟨pattern.sourcePositionEmbedding i, ?_⟩
      rw [typeIIAffineLiftNormal_apply,
        typeIIAffineLiftNormal_apply_of_not_mem_range]
      · exact hi
      · exact sectionSixTerminalVFirstResidual_not_mem_sourceRange
          pattern hresidual
  | right j =>
      unfold TypeIIAffineMixedPresentation.inter at hnormal ⊢
      dsimp only at hnormal ⊢
      rw [Fin.append_right] at hnormal ⊢
      exact sectionSixTerminalVFixedPresentation_normal_nonconstant epsilon
        delta band pattern hinner hresidual j hnormal

/-- Project one nonzero literal wall of the terminal-V base-X core to the
canonical positive-dimensional sum-one coordinates. The occurrence index and
the weak wall width are preserved exactly. -/
theorem sectionSixTerminalVBaseXCoreWall_exists_projected
    {epsilon delta rho : Real} {ell M : Nat}
    {region : Set (Fin ell -> Real)} (band : SectionSixStateBand)
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (x : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real)
    (hsum : (∑ i, x i) = 1)
    (j : Fin (sectionSixTerminalVBaseXCorePresentation sourcePresentation
      epsilon delta band pattern hinner hresidual).constraintCount)
    (hnormal : (sectionSixTerminalVBaseXCorePresentation sourcePresentation
      epsilon delta band pattern hinner hresidual).normal j ≠ 0)
    (hwall :
      |typeIIAffineValue
          ((sectionSixTerminalVBaseXCorePresentation sourcePresentation
            epsilon delta band pattern hinner hresidual).normal j) x -
        (sectionSixTerminalVBaseXCorePresentation sourcePresentation
          epsilon delta band pattern hinner hresidual).bound j| <=
      rho ^ 2 * typeIIAffineNormalMass
        ((sectionSixTerminalVBaseXCorePresentation sourcePresentation
          epsilon delta band pattern hinner hresidual).normal j)) :
    ∃ n : Nat,
      ∃ hdimension :
          (pattern.1.1 + ell) + pattern.2.1.1 = n + 2,
        let P := sectionSixTerminalVBaseXCorePresentation sourcePresentation
          epsilon delta band pattern hinner hresidual
        let cast := Fin.castOrderIso hdimension
        let normal : Fin (n + 2) -> Real := fun i =>
          P.normal j (cast.symm i)
        let point : Fin (n + 2) -> Real := fun i => x (cast.symm i)
        typeIIProjectedAffineNormal normal ≠ 0 ∧
          |typeIIAffineValue (typeIIProjectedAffineNormal normal)
                (Fin.init point) -
              typeIIProjectedAffineBound normal (P.bound j)| <=
            rho ^ 2 * typeIIAffineNormalMass (P.normal j) := by
  let n := (pattern.1.1 + ell) + pattern.2.1.1 - 2
  have hdimension :
      (pattern.1.1 + ell) + pattern.2.1.1 = n + 2 := by
    dsimp only [n]
    omega
  refine ⟨n, hdimension, ?_⟩
  let P := sectionSixTerminalVBaseXCorePresentation sourcePresentation
    epsilon delta band pattern hinner hresidual
  have hnonconstant : ∃ a b, P.normal j a ≠ P.normal j b := by
    obtain ⟨i, hi⟩ := terminalVBaseXCore_normal_nonconstant band
      sourcePresentation pattern hinner hresidual j hnormal
    exact ⟨i, pattern.firstResidualPosition hresidual, hi⟩
  exact terminalVProjectedWall_of_nonconstant hdimension x hsum
    (P.normal j) (P.bound j)
    (rho ^ 2 * typeIIAffineNormalMass (P.normal j)) hnonconstant hwall

end

end PrimesRestrictedDigits
