import PrimesRestrictedDigits.LatticeEstimates.CrossResidualBounds
import PrimesRestrictedDigits.LatticeEstimates.IntegralPulledBackBasis

/-!
# The integral cross-product witness

This composes the repaired reduced-basis argument with the cross-product
estimates for `MAYNARD-PRD-PUBLISHED`, Lemma 14.1.
-/

noncomputable section

namespace PrimesRestrictedDigits

open Matrix WithLp

open scoped Matrix

private abbrev E := EuclideanSpace Real (Fin 3)

/-- The source hypotheses produce one nonzero integral cross product with the
two quantitative bounds needed for rational normalization. -/
theorem exists_integralCrossProduct_with_bounds
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    (delta N K : Real) (hdelta : 0 < delta) (hN : 1 <= N) (hK : 1 <= K)
    (Lambda : RankTwoIntegralLattice)
    (hcard : delta * K * N ^ 2 <=
      ((latticeGeneratingIntegerPoints a1 a2 Lambda delta N).card : Real))
    (hnonlinear : LatticePointsNotContainedInLine
      (latticeGeneratingIntegerPoints a1 a2 Lambda delta N)) :
    exists c : Fin 3 -> Int, c ≠ 0 ∧
      ‖intVectorToEuclidean c‖ <= 705600 / (delta * K) ∧
      exists lambda : Real,
        ‖latticeAngleVector a1 a2 - lambda • intVectorToEuclidean c‖ <=
          151200 * (X : Real) /
            (N * K * ‖intVectorToEuclidean c‖) := by
  obtain ⟨_b, V, z, _hV, _hz, hzLI, hVpos, hznorm, hzinner, hproduct⟩ :=
    exists_integralPulledBackBasis_with_bounds
      hX a1 a2 delta N K hdelta hN hK Lambda hcard hnonlinear
  let w0 : E := intVectorToEuclidean (z 0)
  let w1 : E := intVectorToEuclidean (z 1)
  let c : Fin 3 -> Int := z 0 ⨯₃ z 1
  have hpair : LinearIndependent Real ![w0, w1] := by
    have hfamilies : (fun i : Fin 2 => intVectorToEuclidean (z i)) =
        ![w0, w1] := by
      funext i
      fin_cases i <;> rfl
    rw [← hfamilies]
    exact hzLI
  have hcross : euclideanCross w0 w1 ≠ 0 :=
    euclideanCross_ne_zero_iff.mpr hpair
  have hc : c ≠ 0 := by
    intro hzero
    apply hcross
    rw [← intVectorToEuclidean_cross]
    simp [c, hzero]
  have hnorm : ‖intVectorToEuclidean c‖ <= 705600 / (delta * K) := by
    have hbound := norm_euclideanCross_intVectors_le
      (z 0) (z 1) (V 0) (V 1) delta K
      (hVpos 0).le (hVpos 1).le (hznorm 0) (hznorm 1)
      hdelta (zero_lt_one.trans_le hK) hproduct
    rw [← intVectorToEuclidean_cross] at hbound
    simpa [c] using hbound
  let crossRaw : Fin 3 -> Real := w0.ofLp ⨯₃ w1.ofLp
  let lambda : Real :=
    (latticeAngleVector a1 a2).ofLp ⬝ᵥ crossRaw /
      (crossRaw ⬝ᵥ crossRaw)
  have hresidual := norm_euclideanCrossResidual_le_of_basis_bounds
    (latticeAngleVector a1 a2) w0 w1 (X : Real) delta N K (V 0) (V 1)
    (by positivity) hdelta (zero_lt_one.trans_le hN) (zero_lt_one.trans_le hK)
    hpair (hVpos 0).le (hVpos 1).le (hznorm 0) (hznorm 1)
    (hzinner 0) (hzinner 1) hproduct
  have hresidualEq :
      euclideanCrossResidual (latticeAngleVector a1 a2) w0 w1 =
        latticeAngleVector a1 a2 - lambda • intVectorToEuclidean c := by
    rw [intVectorToEuclidean_cross]
    rfl
  refine ⟨c, hc, hnorm, lambda, ?_⟩
  rw [← hresidualEq]
  simpa [w0, w1, c, intVectorToEuclidean_cross] using hresidual

end PrimesRestrictedDigits
