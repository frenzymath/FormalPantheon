import PrimesRestrictedDigits.LatticeEstimates.PulledBackBasisBounds

/-!
# Integral representatives of the pulled-back reduced basis

This turns the pulled-back basis vectors in the repaired proof of
`MAYNARD-PRD-PUBLISHED`, Lemma 14.1, into literal integer triples while
preserving linear independence and the quantitative bounds.
-/

noncomputable section

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/-- The reduced image basis pulls back to two independent integer triples in
the original lattice, with the norm, scalar-product, and product estimates
needed for the cross-product argument. -/
theorem exists_integralPulledBackBasis_with_bounds
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    (delta N K : Real) (hdelta : 0 < delta) (hN : 1 <= N) (hK : 1 <= K)
    (Lambda : RankTwoIntegralLattice)
    (hcard : delta * K * N ^ 2 <=
      ((latticeGeneratingIntegerPoints a1 a2 Lambda delta N).card : Real))
    (hnonlinear : LatticePointsNotContainedInLine
      (latticeGeneratingIntegerPoints a1 a2 Lambda delta N)) :
    exists
      (b : Module.Basis (Fin 2) Int
        (directionallyDilatedLattice Lambda (latticeAngleVector a1 a2)
          (N / delta) (latticeAngleVector_ne_zero hX a1 a2)
          (div_ne_zero (zero_lt_one.trans_le hN).ne' hdelta.ne')))
      (V : Fin 2 -> Real) (z : Fin 2 -> Fin 3 -> Int),
      (forall i, V i = ‖(b i : E)‖) ∧
      (forall i, intVectorToEuclidean (z i) =
        (pulledBackBasisVector Lambda (latticeAngleVector a1 a2)
          (N / delta) (latticeAngleVector_ne_zero hX a1 a2)
          (div_ne_zero (zero_lt_one.trans_le hN).ne' hdelta.ne') b i : E)) ∧
      LinearIndependent Real (fun i => intVectorToEuclidean (z i)) ∧
      (forall i, 0 < V i) ∧
      (forall i, ‖intVectorToEuclidean (z i)‖ <= 28 * V i) ∧
      (forall i, |inner Real (latticeAngleVector a1 a2)
        (intVectorToEuclidean (z i))| <=
          3 * delta * (X : Real) * V i / N) ∧
      V 0 * V 1 <= 900 / (delta * K) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  let A := latticeAngleVector a1 a2
  let hA : A ≠ 0 := latticeAngleVector_ne_zero hX a1 a2
  let t := N / delta
  let ht : t ≠ 0 := div_ne_zero hNpos.ne' hdelta.ne'
  obtain ⟨b, hbpos, _hbupper, hbproduct⟩ :=
    exists_directionallyDilatedBasis_with_bounds
      hX a1 a2 delta N K hdelta hNpos hKpos Lambda hcard hnonlinear
  let w : Fin 2 -> Lambda.carrier := fun i =>
    pulledBackBasisVector Lambda A t hA ht b i
  let V : Fin 2 -> Real := fun i => ‖(b i : E)‖
  let z : Fin 2 -> Fin 3 -> Int := fun i =>
    Classical.choose (Lambda.integral (w i))
  have hz : forall i, intVectorToEuclidean (z i) = (w i : E) := fun i =>
    Classical.choose_spec (Lambda.integral (w i))
  have hbLI : LinearIndependent Real (fun i => (b i : E)) := by
    change LinearIndependent Real
      (integralBasisCoe (directionallyDilatedLattice Lambda A t hA ht) b)
    exact integralBasisCoe_linearIndependent
      (directionallyDilatedLattice Lambda A t hA ht) b
  have hwLI : LinearIndependent Real (fun i => (w i : E)) := by
    have hmapped := hbLI.map'
      (directionalDilation A t hA ht).symm.toLinearMap (by simp)
    have hfamilies :
        (directionalDilation A t hA ht).symm.toLinearMap ∘
            (fun i => (b i : E)) =
          (fun i => (w i : E)) := by
      funext i
      exact (pulledBackBasisVector_coe Lambda A t hA ht b i).symm
    rw [hfamilies] at hmapped
    exact hmapped
  have hzLI : LinearIndependent Real (fun i => intVectorToEuclidean (z i)) := by
    have hfamilies : (fun i => intVectorToEuclidean (z i)) =
        (fun i => (w i : E)) := by
      funext i
      exact hz i
    rw [hfamilies]
    exact hwLI
  have hdeltaN : delta <= 27 * N :=
    delta_le_twenty_seven_mul_of_generatingPoints
      a1 a2 delta N K hdelta hN hK Lambda hcard
  have hnorm : forall i, ‖intVectorToEuclidean (z i)‖ <= 28 * V i := by
    intro i
    rw [hz i]
    simpa [w, V, A, hA, t, ht] using
      (norm_pulledBackBasisVector_le
        hX a1 a2 delta N hdelta hNpos hdeltaN Lambda b i)
  have hinner : forall i, |inner Real A (intVectorToEuclidean (z i))| <=
      3 * delta * (X : Real) * V i / N := by
    intro i
    rw [hz i]
    simpa [w, V, A, hA, t, ht] using
      (abs_inner_pulledBackBasisVector_le
        hX a1 a2 delta N hdelta hNpos Lambda b i)
  refine ⟨b, V, z, ?_, ?_, hzLI, ?_, hnorm, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    simpa [w, A, hA, t, ht] using hz i
  · intro i
    exact hbpos i
  · simpa [A] using hinner
  · simpa [V] using hbproduct

end PrimesRestrictedDigits
