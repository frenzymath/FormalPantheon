import PrimesRestrictedDigits.LatticeEstimates.FinalScaleAggregation
import PrimesRestrictedDigits.LatticeEstimates.Lemma14ThreeLog
import PrimesRestrictedDigits.LatticeEstimates.RationalApproximationSizeSource

/-!
# Proposition 13.3: angles generating lattices

This combines repaired Lemmas 14.2--14.4 with the completed Lemma 14.3 outer decomposition.
The rational carrier uses the `E=0` repair, and the exceptional carrier is the one stated in
the proposition. See `MAYNARD-PRD-PUBLISHED`, Proposition 13.3.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- The exact Proposition 13.3 carrier, represented inside the generating
pair subtype. -/
noncomputable def latticePropositionThirteenThreePairs
    (digit : Fin 10) (length : Nat) (N K delta Q E : Real) :
    Finset (LatticeGeneratingPair length N K delta) := by
  classical
  exact (latticeGeneratingExceptionalPairs digit length N K delta).filter
    fun a =>
      a.val.1 ∈ latticeRationalApproximationBand Q E ∧
        a.val.2 ∈ latticeRationalApproximationBand Q E

theorem mem_latticePropositionThirteenThreePairs_iff
    {digit : Fin 10} {length : Nat} {N K delta Q E : Real}
    {a : LatticeGeneratingPair length N K delta} :
    a ∈ latticePropositionThirteenThreePairs digit length N K delta Q E ↔
      a.val.1 ∈ genericExceptionalFrequencies digit length ∧
      a.val.2 ∈ genericExceptionalFrequencies digit length ∧
      a.val.1 ∈ latticeRationalApproximationBand Q E ∧
      a.val.2 ∈ latticeRationalApproximationBand Q E := by
  classical
  simp [latticePropositionThirteenThreePairs,
    mem_latticeGeneratingExceptionalPairs_iff, and_assoc]

/-- The weighted left side of Proposition 13.3. -/
noncomputable def latticePropositionThirteenThreeMass
    (digit : Fin 10) (length : Nat) (N K delta Q E : Real) : Real :=
  ∑ a ∈ latticePropositionThirteenThreePairs digit length N K delta Q E,
    latticeGeneratingPairWeight digit length a.val

theorem latticePropositionThirteenThreeMass_le_exceptionalMass
    (digit : Fin 10) (length : Nat) (N K delta Q E : Real) :
    latticePropositionThirteenThreeMass digit length N K delta Q E <=
      latticeGeneratingExceptionalMass digit length N K delta := by
  unfold latticePropositionThirteenThreeMass latticeGeneratingExceptionalMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro a ha hnot
    exact latticeGeneratingPairWeight_nonneg digit length a.val

private theorem rationalGeneratingIntersection_nonempty
    {digit : Fin 10} {length : Nat} {N K delta Q E : Real}
    (hnonempty :
      (latticePropositionThirteenThreePairs digit length N K delta Q E).Nonempty) :
    (latticeGeneratingPairs (X := 10 ^ length) N K delta ∩
      (latticeRationalApproximationBand (X := 10 ^ length) Q E ×ˢ
        latticeRationalApproximationBand
          (X := 10 ^ length) Q E)).Nonempty := by
  obtain ⟨a, ha⟩ := hnonempty
  have hdata := mem_latticePropositionThirteenThreePairs_iff.mp ha
  exact ⟨a.val, Finset.mem_inter.mpr
    ⟨a.property, Finset.mem_product.mpr ⟨hdata.2.2.1, hdata.2.2.2⟩⟩⟩

/-- Source-facing quantitative Proposition 13.3 with one comparison constant
chosen before the digit and every analytic parameter. -/
theorem exists_latticePropositionThirteenThree :
    ∃ C : Real, 0 < C ∧
      ∀ (digit : Fin 10) (length : Nat) (N K delta Q E : Real),
        1 <= length ->
        1 <= N ->
        1 <= K ->
        0 < delta ->
        (((10 ^ length : Nat) : Real) ^ (17 / 40 : Real)) <= N * K ->
        N / ((10 ^ length : Nat) : Real) <= delta ->
        1 <= Q ->
        Q <= Real.sqrt ((10 ^ length : Nat) : Real) ->
        0 <= E ->
        E <= 100 * Real.sqrt ((10 ^ length : Nat) : Real) / Q ->
        latticePropositionThirteenThreeMass digit length N K delta Q E <=
          C * Real.log (((10 ^ length : Nat) : Real)) ^ 5 *
            ((10 ^ length : Nat) : Real) /
              ((N * K) * (Q + E) ^ (latticeSumSaving / 4)) := by
  obtain ⟨Cscale, hCscale, hscale⟩ :=
    exists_latticeExceptionalSmoothPairSum_le_propositionScale 19
  let C : Real := latticeLemma14ThreeLogConstant * Cscale
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos latticeLemma14ThreeLogConstant_pos hCscale
  refine ⟨C, hC, ?_⟩
  intro digit length N K delta Q E hlength hN hK hdelta hgrowth
    hdeltaLower hQ hQupper hE hEupper
  let X : Real := ((10 ^ length : Nat) : Real)
  let P : Real := N * K
  have hX : 0 < X := by dsimp only [X]; positivity
  have hP : 0 < P := by
    dsimp only [P]
    exact mul_pos (Real.zero_lt_one.trans_le hN) (Real.zero_lt_one.trans_le hK)
  have hR : 0 < Q + E := by linarith
  have hlog : 0 < Real.log X := by
    apply Real.log_pos
    have htenPower : 10 <= (10 ^ length : Nat) := by
      calc
        10 = 10 ^ 1 := by norm_num
        _ <= 10 ^ length := Nat.pow_le_pow_right (by norm_num) hlength
    dsimp only [X]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < (10 : Nat)) htenPower)
  by_cases hcarrier :
      (latticePropositionThirteenThreePairs digit length N K delta Q E).Nonempty
  · have hsizeRaw := latticeRationalApproximationSize length N K delta Q E
      hN hK hdelta hgrowth hdeltaLower hQ hQupper hE hEupper
      (rationalGeneratingIntersection_nonempty hcarrier)
    have hsize : Q + E <= ((10 ^ 19 : Nat) : Real) * (X / P) ^ 2 := by
      calc
        Q + E <= 1030301000000000000 * (X / P) ^ 2 := by
          simpa only [X, P] using hsizeRaw
        _ <= ((10 ^ 19 : Nat) : Real) * (X / P) ^ 2 := by
          apply mul_le_mul_of_nonneg_right
          · norm_num
          · positivity
    let B : Real := Cscale * X / (P * (Q + E) ^ (latticeSumSaving / 4))
    have hB : 0 <= B := by dsimp only [B]; positivity
    have hmajorant : ∀ key,
        key ∈ LatticeDecompositionScaleKey.admissibleCarrier length P ->
        latticeLemma14ThreeScaleCell digit length P key <= B := by
      intro key hkey
      have hadmissible :=
        LatticeDecompositionScaleKey.mem_admissibleCarrier_iff.mp hkey
      have hsource :
          (((key.errorScale P * key.denominatorScale : Nat) : Real)) <=
            ((10 ^ 19 : Nat) : Real) * X / P := by
        calc
          (((key.errorScale P * key.denominatorScale : Nat) : Real)) <=
              ((10 ^ 12 : Nat) : Real) * X / P := by
            simpa only [X] using hadmissible.1
          _ <= ((10 ^ 19 : Nat) : Real) * X / P := by
            apply div_le_div_of_nonneg_right _ hP.le
            apply mul_le_mul_of_nonneg_right
            · norm_num
            · exact hX.le
      have hG : (key.g1PrimeScale : Real) <=
          ((10 ^ 19 : Nat) : Real) * key.g2Scale := by
        calc
          (key.g1PrimeScale : Real) <=
              ((10 ^ 12 : Nat) : Real) * key.g2Scale := hadmissible.2
          _ <= ((10 ^ 19 : Nat) : Real) * key.g2Scale := by
            apply mul_le_mul_of_nonneg_right
            · norm_num
            · positivity
      have hraw := hscale digit length key.qPrimeIndex.val
        key.g1PrimeIndex.val key.g2Index.val key.d0Index.val key.d1Index.val
        (key.errorScaleIndex P) P Q E hgrowth hsource hG hQ hE hsize
      simpa only [latticeLemma14ThreeScaleCell,
        LatticeDecompositionScaleKey.qPrimeScale,
        LatticeDecompositionScaleKey.g1PrimeScale,
        LatticeDecompositionScaleKey.g2Scale,
        LatticeDecompositionScaleKey.d0Scale,
        LatticeDecompositionScaleKey.d1Scale,
        LatticeDecompositionScaleKey.errorScale,
        LatticeDecompositionScaleKey.denominatorScale, X, P, B] using hraw
    have houter := latticeGeneratingExceptionalMass_le_of_scale_majorant
      digit N K delta B hN hK hdelta (by simpa only [X] using hdeltaLower)
        hB hmajorant
    have hrestricted :=
      latticePropositionThirteenThreeMass_le_exceptionalMass
        digit length N K delta Q E
    have hcover := latticeLemma14Three_coverFactor_le_log hlength
    calc
      latticePropositionThirteenThreeMass digit length N K delta Q E <=
          latticeGeneratingExceptionalMass digit length N K delta := hrestricted
      _ <= ((2 * (length + 7) ^ 5 : Nat) : Real) * B := houter
      _ <= (latticeLemma14ThreeLogConstant * Real.log X ^ 5) * B := by
        exact mul_le_mul_of_nonneg_right (by simpa only [X] using hcover) hB
      _ = C * Real.log X ^ 5 * X /
          (P * (Q + E) ^ (latticeSumSaving / 4)) := by
        dsimp only [B, C]
        ring
      _ = C * Real.log (((10 ^ length : Nat) : Real)) ^ 5 *
          ((10 ^ length : Nat) : Real) /
            ((N * K) * (Q + E) ^ (latticeSumSaving / 4)) := by
        rfl
  · have hempty :
        latticePropositionThirteenThreePairs digit length N K delta Q E = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hcarrier
    unfold latticePropositionThirteenThreeMass
    rw [hempty]
    simp only [Finset.sum_empty]
    positivity

end

end PrimesRestrictedDigits
