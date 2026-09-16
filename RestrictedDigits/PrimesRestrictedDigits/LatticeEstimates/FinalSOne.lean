import PrimesRestrictedDigits.LatticeEstimates.ExceptionalSum
import PrimesRestrictedDigits.LatticeEstimates.HybridMultiplicity

/-!
# The finite first lattice sum

This file packages the pointwise first sum from Lemma 14.4 into the finite maximum used by the
source and lifts both available pointwise estimates. The final definition records the
corrected common-`S1` product minimum.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- The source `S1`: the maximum over its coprime decade band.  Adjoining zero
makes the definition total while preserving every nonempty source maximum. -/
noncomputable def latticeSOne
    (digit : Fin 10) (length d Q G E : Nat) : Real :=
  let values :=
    insert 0 ((hybridResidualSourceDenominators Q).image fun q =>
      latticeSOneAt digit length d q G E)
  values.sup' (Finset.insert_nonempty 0 _) id

theorem latticeSOneAt_nonneg
    (digit : Fin 10) (length d q G E : Nat) :
    0 <= latticeSOneAt digit length d q G E := by
  unfold latticeSOneAt
  exact Finset.sum_nonneg fun g _ =>
    latticeHybridDenominatorWeight_nonneg digit length E ((q * d) * g)

theorem latticeSTwo_nonneg
    (digit : Fin 10) (length d Q G E : Nat) :
    0 <= latticeSTwo digit length d Q G E := by
  unfold latticeSTwo
  exact Finset.sum_nonneg fun x _ =>
    latticeHybridDenominatorWeight_nonneg digit length E (d * (x.1 * x.2))

theorem latticeSOne_nonneg
    (digit : Fin 10) (length d Q G E : Nat) :
    0 <= latticeSOne digit length d Q G E := by
  unfold latticeSOne
  exact Finset.le_sup' id (Finset.mem_insert_self 0 _)

/-- Every member of the exact source band is bounded by the finite `S1`
maximum. -/
theorem latticeSOneAt_le_latticeSOne
    (digit : Fin 10) (length d Q G E q : Nat)
    (hq : q ∈ hybridResidualSourceDenominators Q) :
    latticeSOneAt digit length d q G E <=
      latticeSOne digit length d Q G E := by
  unfold latticeSOne
  apply Finset.le_sup' id
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨q, hq, rfl⟩

/-- A uniform pointwise majorant, together with its value at the adjoined
zero, bounds the source maximum. -/
theorem latticeSOne_le
    (digit : Fin 10) (length d Q G E : Nat) {B : Real}
    (hB : 0 <= B)
    (hpointwise : ∀ q ∈ hybridResidualSourceDenominators Q,
      latticeSOneAt digit length d q G E <= B) :
    latticeSOne digit length d Q G E <= B := by
  unfold latticeSOne
  apply Finset.sup'_le
  intro value hvalue
  rcases Finset.mem_insert.mp hvalue with rfl | hvalue
  · simpa using hB
  · rcases Finset.mem_image.mp hvalue with ⟨q, hq, rfl⟩
    exact hpointwise q hq

/-- Equation (14.9)'s standard bound, uniformly lifted from each admissible
`q'` to the source maximum. -/
theorem latticeSOne_le_hybridBound
    (digit : Fin 10) (length d D Q G E : Nat)
    (hd : 0 < d) (hG : 0 < G) (hE : 0 < E) (hdD : d <= D) :
    latticeSOne digit length d Q G E <=
      4 * hybridConstant *
        latticeHybridTarget length
          (((D * Q * G ^ 2 : Nat) : Real) * E) := by
  apply latticeSOne_le
  · have hconstant : 0 <= 4 * hybridConstant := by
      norm_num [hybridConstant]
    exact mul_nonneg hconstant (by
      unfold latticeHybridTarget
      positivity)
  · intro q hq
    have hqData := mem_hybridResidualSourceDenominators_iff.mp hq
    exact latticeSOneAt_le_hybridBound digit length d q D Q G E
      hd (lt_of_lt_of_le Nat.zero_lt_one hqData.1) hG hE hdD hqData.2.1

/-- Equation (14.11)'s Alternative Hybrid Bound, uniformly lifted to the
source maximum without changing its exact decade-band endpoints. -/
theorem latticeSOne_le_alternativeHybridBound
    (loss : Nat) (digit : Fin 10)
    {length dLength eLength d u Q G : Nat}
    (hscale : dLength + eLength <= length + loss)
    (hd : 0 < d) (hdD : d <= 10 ^ dLength) (hdvd : d ∣ 10 ^ u) :
    let C : Real := ((10 ^ loss : Nat) : Real)
    let D : Real := ((10 ^ dLength : Nat) : Real)
    let E : Real := ((10 ^ eLength : Nat) : Real)
    let Y : Real := ((10 ^ length : Nat) : Real)
    let L : Real := ((Q * G ^ 2 : Nat) : Real)
    latticeSOne digit length d Q G (10 ^ eLength) <=
      (72000 * largeSieveSamplingConstant ^ 2 * (1 + 2 * C) ^ 2 *
          (1 + C) * (3 + C ^ largeSieveSigma)) *
        ((D * E) ^ largeSieveAlpha * L ^ hybridResidualGrowth +
          E ^ (5 / 6 : Real) * D ^ (3 / 2 : Real) * L /
            Y ^ hybridResidualHalfDecay) := by
  dsimp only
  apply latticeSOne_le
  · positivity
  · intro q hq
    have hqData := mem_hybridResidualSourceDenominators_iff.mp hq
    exact latticeSOneAt_le_alternativeHybridBound loss digit hscale
      (lt_of_lt_of_le Nat.zero_lt_one hqData.1) hd hdD hdvd
      hqData.2.2.2 hqData.2.1

/-- The corrected product minimum in Lemma 14.4.  The common first factor
uses `d0*d1`, whereas both second factors use `d0` alone. -/
noncomputable def latticeExceptionalProductMinimum
    (digit : Fin 10) (length d0 d1 Q G1 G2 E : Nat) : Real :=
  min
    (latticeSOne digit length (d0 * d1) Q G1 E *
      latticeSTwo digit length d0 Q G2 E)
    (latticeSOne digit length (d0 * d1) Q G1 E *
      latticeSThree digit length d0 Q G2 E)

theorem latticeExceptionalProductMinimum_nonneg
    (digit : Fin 10) (length d0 d1 Q G1 G2 E : Nat) :
    0 <= latticeExceptionalProductMinimum digit length d0 d1 Q G1 G2 E := by
  unfold latticeExceptionalProductMinimum
  exact le_min
    (mul_nonneg (latticeSOne_nonneg digit length (d0 * d1) Q G1 E)
      (latticeSTwo_nonneg digit length d0 Q G2 E))
    (mul_nonneg (latticeSOne_nonneg digit length (d0 * d1) Q G1 E)
      (latticeSThree_nonneg digit length d0 Q G2 E))

end

end PrimesRestrictedDigits
