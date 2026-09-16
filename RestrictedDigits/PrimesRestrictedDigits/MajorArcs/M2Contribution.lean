import PrimesRestrictedDigits.MajorArcs.M2PositiveBlocks
import PrimesRestrictedDigits.MajorArcs.M2Subdivision

/-!
# The repaired finite M2 contribution

This combines the reduced-carrier relaxation, the retained zero block, and
the conditional positive-block estimate on published pp. 187--188. The local
progression estimate remains an explicit input.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The original reduced last-prime aggregate is controlled by the relaxation
loss and all subdivision blocks. -/
theorem norm_majorArcActualReduced_signed_le
    {X k m q J : Nat} {a : Fin k -> Real} {delta eta E : Real}
    {b c : Int}
    (hX : 1 < X) (heta : 0 < eta)
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hell : ((k + 1 : Nat) : Real) ≤ 2 / eta)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ eta ^ 2 / 12)
    (hm : 0 < m) (hq : 0 < q) (hJ : 1 < J)
    (hE : 0 ≤ E) (hc0 : c ≠ 0) (hcJ : c.natAbs < J)
    (hweight : projectedPrimeBoxWeightAtProduct X a delta m ≠ 0)
    (herror : ∀ j ∈ Finset.Ico 1 J,
      ∀ r ∈ majorArcReducedResidues q,
        |majorArcPrimeLogResidueSum (X : Real) J m j q r -
          majorArcPositiveBlockMainTerm (X : Real) J m q| ≤
            E * majorArcPositiveBlockErrorScale (X : Real) J m q) :
    ‖∑ r ∈ majorArcReducedResidues q,
      majorArcLastPrimePhaseResidueSum X a delta eta m q r
        ((b : Real) / (q : Real) + (c : Real) / (X : Real))‖ ≤
      Real.log 4 *
          (majorArcM2RelaxationScale (X : Real) delta eta / (m : Real)) +
        (E + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4 + Real.log 4) *
          majorArcBlockLength (X : Real) J m := by
  let theta := (b : Real) / (q : Real) + (c : Real) / (X : Real)
  let actual := ∑ r ∈ majorArcReducedResidues q,
    majorArcLastPrimePhaseResidueSum X a delta eta m q r theta
  let relaxed := ∑ r ∈ majorArcReducedResidues q,
    majorArcRelaxedLastPrimePhaseResidueSum X m q r theta
  let zeroBlock := ∑ r ∈ majorArcReducedResidues q,
    majorArcSignedPrimePhaseResidueSum (X : Real) J m 0 q r b c
  let positiveBlocks := ∑ j ∈ Finset.Ico 1 J,
    ∑ r ∈ majorArcReducedResidues q,
      majorArcSignedPrimePhaseResidueSum (X : Real) J m j q r b c
  let relaxationError := Real.log 4 *
    (majorArcM2RelaxationScale (X : Real) delta eta / (m : Real))
  let positiveCoefficient := E + 1 +
    2 * Real.pi * |(c : Real)| * Real.log 4
  have hXpos : 0 < X := Nat.zero_lt_of_lt hX
  have hrelax : ‖relaxed - actual‖ ≤ relaxationError := by
    exact norm_majorArcRelaxedReduced_sub_actual_le
      hX heta hsum hell hdelta0 hdelta hm hq hweight
  have hsplit : relaxed = zeroBlock + positiveBlocks := by
    dsimp [relaxed, zeroBlock, positiveBlocks, theta]
    exact majorArcRelaxedReduced_signed_eq_zero_add_positive
      hXpos (Nat.zero_lt_of_lt hJ) hm hq
  have hzero : ‖zeroBlock‖ ≤
      Real.log 4 * majorArcBlockLength (X : Real) J m := by
    exact norm_majorArcSignedReducedZeroBlock_le
      (Nat.zero_lt_of_lt hJ) hm hq
  have hpositive : ‖positiveBlocks‖ ≤
      positiveCoefficient * majorArcBlockLength (X : Real) J m := by
    exact norm_sum_majorArcSignedReducedPositiveBlocks_le
      (by exact_mod_cast hXpos) hJ hm hq hE hc0 hcJ herror
  have hrelaxed : ‖relaxed‖ ≤
      Real.log 4 * majorArcBlockLength (X : Real) J m +
        positiveCoefficient * majorArcBlockLength (X : Real) J m := by
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hzero hpositive)
  have hdiff : ‖actual - relaxed‖ = ‖relaxed - actual‖ := by
    rw [show actual - relaxed = -(relaxed - actual) by ring, norm_neg]
  calc
    ‖actual‖ = ‖(actual - relaxed) + relaxed‖ := by ring_nf
    _ ≤ ‖actual - relaxed‖ + ‖relaxed‖ := norm_add_le _ _
    _ = ‖relaxed - actual‖ + ‖relaxed‖ := by rw [hdiff]
    _ ≤ relaxationError +
        (Real.log 4 * majorArcBlockLength (X : Real) J m +
          positiveCoefficient * majorArcBlockLength (X : Real) J m) :=
      add_le_add hrelax hrelaxed
    _ = Real.log 4 *
          (majorArcM2RelaxationScale (X : Real) delta eta / (m : Real)) +
        (E + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4 + Real.log 4) *
          majorArcBlockLength (X : Real) J m := by
      dsimp [relaxationError, positiveCoefficient]
      ring

/--
Under power-of-ten hypotheses, the same estimate controls the global original last-prime phase
sum.
-/
theorem norm_majorArcLastPrimePhaseSum_signed_le
    {X K k m q J : Nat} {a : Fin k -> Real} {delta eta E : Real}
    {b c : Int}
    (hX : 1 < X) (heta : 0 < eta)
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hell : ((k + 1 : Nat) : Real) ≤ 2 / eta)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ eta ^ 2 / 12)
    (hlarge : 5 < (X : Real) ^ (eta / 4))
    (hpower : X = 10 ^ K) (hqdiv : q ∣ X)
    (hm : 0 < m) (hq : 0 < q) (hJ : 1 < J)
    (hE : 0 ≤ E) (hc0 : c ≠ 0) (hcJ : c.natAbs < J)
    (hweight : projectedPrimeBoxWeightAtProduct X a delta m ≠ 0)
    (herror : ∀ j ∈ Finset.Ico 1 J,
      ∀ r ∈ majorArcReducedResidues q,
        |majorArcPrimeLogResidueSum (X : Real) J m j q r -
          majorArcPositiveBlockMainTerm (X : Real) J m q| ≤
            E * majorArcPositiveBlockErrorScale (X : Real) J m q) :
    ‖majorArcLastPrimePhaseSum X a delta eta m
      ((b : Real) / (q : Real) + (c : Real) / (X : Real))‖ ≤
      Real.log 4 *
          (majorArcM2RelaxationScale (X : Real) delta eta / (m : Real)) +
        (E + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4 + Real.log 4) *
          majorArcBlockLength (X : Real) J m := by
  rw [majorArcLastPrimePhaseSum_eq_sum_reducedResidues
    hlarge hpower hqdiv hq m]
  exact norm_majorArcActualReduced_signed_le hX heta hsum hell hdelta0
    hdelta hm hq hJ hE hc0 hcJ hweight herror

/-- The source transform is bounded by the exact projected harmonic mass.
The coefficient `E` is uniform in all supported outer fibers. -/
theorem norm_majorArcRegionWeightedPhaseSum_signed_le_harmonic
    {X K k q J : Nat} {a : Fin k -> Real} {delta eta E : Real}
    {b c : Int}
    (hX : 3 ≤ X) (heta : 0 < eta)
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hell : ((k + 1 : Nat) : Real) ≤ 2 / eta)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ eta ^ 2 / 12)
    (hlarge : 5 < (X : Real) ^ (eta / 4))
    (hpower : X = 10 ^ K) (hqdiv : q ∣ X) (hq : 0 < q)
    (hJ : 1 < J) (hE : 0 ≤ E)
    (hc0 : c ≠ 0) (hcJ : c.natAbs < J)
    (herror : ∀ m ∈ Finset.Ico 1 X,
      projectedPrimeBoxWeightAtProduct X a delta m ≠ 0 ->
      ∀ j ∈ Finset.Ico 1 J,
      ∀ r ∈ majorArcReducedResidues q,
        |majorArcPrimeLogResidueSum (X : Real) J m j q r -
          majorArcPositiveBlockMainTerm (X : Real) J m q| ≤
            E * majorArcPositiveBlockErrorScale (X : Real) J m q) :
    ‖majorArcWeightedPhaseSum (Finset.range X)
      (fun n => (majorArcRegionWeightAtProduct X a delta eta n : Complex))
      ((b : Real) / (q : Real) + (c : Real) / (X : Real))‖ ≤
      (Real.log 4 * majorArcM2RelaxationScale (X : Real) delta eta +
        (E + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4 + Real.log 4) *
          majorArcSubdivisionWidth J * (X : Real)) *
        ∑ m ∈ Finset.Ico 1 X,
          projectedPrimeBoxWeightAtProduct X a delta m / (m : Real) := by
  let W := fun m => projectedPrimeBoxWeightAtProduct X a delta m
  let theta := (b : Real) / (q : Real) + (c : Real) / (X : Real)
  let F := fun m => majorArcLastPrimePhaseSum X a delta eta m theta
  let coefficient := Real.log 4 *
      majorArcM2RelaxationScale (X : Real) delta eta +
    (E + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4 + Real.log 4) *
      majorArcSubdivisionWidth J * (X : Real)
  have hterm (m : Nat) (hmCarrier : m ∈ Finset.Ico 1 X) :
      ‖(W m : Complex) * F m‖ ≤ coefficient * (W m / (m : Real)) := by
    have hm : 0 < m := (Finset.mem_Ico.mp hmCarrier).1
    have hW : 0 ≤ W m := projectedPrimeBoxWeightAtProduct_nonneg X a delta m
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW]
    by_cases hW0 : W m = 0
    · simp [hW0]
    · have hF : ‖F m‖ ≤
          Real.log 4 *
              (majorArcM2RelaxationScale (X : Real) delta eta / (m : Real)) +
            (E + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4 + Real.log 4) *
              majorArcBlockLength (X : Real) J m := by
        dsimp [F, theta]
        exact norm_majorArcLastPrimePhaseSum_signed_le
          (by omega) heta hsum hell hdelta0 hdelta hlarge hpower hqdiv
          hm hq hJ hE hc0 hcJ hW0 (herror m hmCarrier hW0)
      calc
        W m * ‖F m‖ ≤ W m *
            (Real.log 4 *
                (majorArcM2RelaxationScale (X : Real) delta eta / (m : Real)) +
              (E + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4 + Real.log 4) *
                majorArcBlockLength (X : Real) J m) :=
          mul_le_mul_of_nonneg_left hF hW
        _ = coefficient * (W m / (m : Real)) := by
          rw [majorArcBlockLength_eq_width_mul
            (X : Real) (Nat.zero_lt_of_lt hJ) hm]
          dsimp [coefficient]
          ring
  rw [majorArcRegionWeightedPhaseSum_eq_projected_lastPrimeSum
    a delta eta theta (by omega)]
  change ‖∑ m ∈ Finset.Ico 1 X, (W m : Complex) * F m‖ ≤ _
  calc
    ‖∑ m ∈ Finset.Ico 1 X, (W m : Complex) * F m‖ ≤
        ∑ m ∈ Finset.Ico 1 X, ‖(W m : Complex) * F m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Ico 1 X, coefficient * (W m / (m : Real)) := by
      apply Finset.sum_le_sum
      intro m hm
      exact hterm m hm
    _ = coefficient * ∑ m ∈ Finset.Ico 1 X, W m / (m : Real) := by
      rw [Finset.mul_sum]

/-- The projected harmonic estimate gives the explicit finite M2 source
bound used downstream. -/
theorem norm_majorArcRegionWeightedPhaseSum_signed_le
    {X K k q J : Nat} {a : Fin k -> Real} {delta eta E : Real}
    {b c : Int}
    (hX : 3 ≤ X) (heta : 0 < eta)
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hell : ((k + 1 : Nat) : Real) ≤ 2 / eta)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ eta ^ 2 / 12)
    (hlarge : 5 < (X : Real) ^ (eta / 4))
    (hpower : X = 10 ^ K) (hqdiv : q ∣ X) (hq : 0 < q)
    (hJ : 1 < J) (hE : 0 ≤ E)
    (hc0 : c ≠ 0) (hcJ : c.natAbs < J)
    (herror : ∀ m ∈ Finset.Ico 1 X,
      projectedPrimeBoxWeightAtProduct X a delta m ≠ 0 ->
      ∀ j ∈ Finset.Ico 1 J,
      ∀ r ∈ majorArcReducedResidues q,
        |majorArcPrimeLogResidueSum (X : Real) J m j q r -
          majorArcPositiveBlockMainTerm (X : Real) J m q| ≤
            E * majorArcPositiveBlockErrorScale (X : Real) J m q) :
    ‖majorArcWeightedPhaseSum (Finset.range X)
      (fun n => (majorArcRegionWeightAtProduct X a delta eta n : Complex))
      ((b : Real) / (q : Real) + (c : Real) / (X : Real))‖ ≤
      (Real.log 4 * majorArcM2RelaxationScale (X : Real) delta eta +
        (E + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4 + Real.log 4) *
          majorArcSubdivisionWidth J * (X : Real)) *
        (2 * Real.log 4 * Real.log (X : Real)) ^ k := by
  let coefficient := Real.log 4 *
      majorArcM2RelaxationScale (X : Real) delta eta +
    (E + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4 + Real.log 4) *
      majorArcSubdivisionWidth J * (X : Real)
  have hcoefficient : 0 ≤ coefficient := by
    dsimp [coefficient, majorArcM2RelaxationScale, majorArcSubdivisionWidth]
    positivity
  have hsubset : Finset.Ico 1 X ⊆ Finset.range X := by
    intro m hm
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hm).2
  have hharmonic :
      (∑ m ∈ Finset.Ico 1 X,
          projectedPrimeBoxWeightAtProduct X a delta m / (m : Real)) ≤
        (2 * Real.log 4 * Real.log (X : Real)) ^ k := by
    calc
      (∑ m ∈ Finset.Ico 1 X,
          projectedPrimeBoxWeightAtProduct X a delta m / (m : Real)) ≤
        ∑ m ∈ Finset.range X,
          projectedPrimeBoxWeightAtProduct X a delta m / (m : Real) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro m hm hnot
        exact div_nonneg
          (projectedPrimeBoxWeightAtProduct_nonneg X a delta m) (by positivity)
      _ ≤ (2 * Real.log 4 * Real.log (X : Real)) ^ k :=
        sum_projectedPrimeBoxWeight_div_le_log_pow X a delta hX
  exact (norm_majorArcRegionWeightedPhaseSum_signed_le_harmonic
    hX heta hsum hell hdelta0 hdelta hlarge hpower hqdiv hq hJ hE
    hc0 hcJ herror).trans (mul_le_mul_of_nonneg_left hharmonic hcoefficient)

end PrimesRestrictedDigits
