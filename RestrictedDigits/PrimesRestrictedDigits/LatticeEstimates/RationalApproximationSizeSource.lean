import PrimesRestrictedDigits.LatticeEstimates.GeneratingPairs
import PrimesRestrictedDigits.LatticeEstimates.RationalApproximationSize
import PrimesRestrictedDigits.LatticeEstimates.SimultaneousApproximation

/-!
# Source-facing rational approximation size estimate

This file combines the direct cross-difference kernel with the repaired Lemma 14.1 to prove
published Lemma 14.2 on its exact finite carriers.
-/

namespace PrimesRestrictedDigits

/-- Explicit all-parameter version of published Lemma 14.2. The growth
hypothesis is retained from Proposition 13.3 even though this stronger proof
does not spend it. -/
theorem latticeRationalApproximationSize
    (length : Nat) (N K delta Q E : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (_hgrowth :
      (((10 ^ length : Nat) : Real) ^ (17 / 40 : Real)) <= N * K)
    (hdeltaLower :
      N / ((10 ^ length : Nat) : Real) <= delta)
    (hQ : 1 <= Q)
    (hQupper : Q <= Real.sqrt ((10 ^ length : Nat) : Real))
    (hE : 0 <= E)
    (hEupper :
      E <= 100 * Real.sqrt ((10 ^ length : Nat) : Real) / Q)
    (hnonempty :
      (latticeGeneratingPairs (X := 10 ^ length) N K delta ∩
        (latticeRationalApproximationBand (X := 10 ^ length) Q E ×ˢ
          latticeRationalApproximationBand
            (X := 10 ^ length) Q E)).Nonempty) :
    Q + E <= 1030301000000000000 *
      (((10 ^ length : Nat) : Real) / (N * K)) ^ 2 := by
  classical
  obtain ⟨a, ha⟩ := hnonempty
  have haData := Finset.mem_inter.mp ha
  have haBand := Finset.mem_product.mp haData.2
  obtain ⟨Lambda, hcard, hnonlinear⟩ :=
    mem_latticeGeneratingPairs_iff.mp haData.1
  obtain ⟨q, hq, hqUpper, b1, b2, herror1, herror2⟩ :=
    latticeSimultaneousApproximation_powerTen
      length a.1 a.2 N K delta Lambda hN hK hdelta hdeltaLower hcard hnonlinear
  have hP : 0 < N * K :=
    mul_pos (zero_lt_one.trans_le hN) (zero_lt_one.trans_le hK)
  have hsize := rationalApproximationSize_of_commonApproximation
    a.1 (P := N * K) (Q := Q) (E := E) (C := 1000000)
      (q := q) (b := b1)
      (Nat.one_le_pow length 10 (by norm_num)) hP (by norm_num)
      hQ hQupper hE hEupper hq hqUpper herror1 haBand.1
  norm_num at hsize ⊢
  exact hsize

/-- The source's implied constant is chosen uniformly before the decimal
scale, every analytic parameter, and the witnessing pair. -/
theorem exists_latticeRationalApproximationSizeConstant :
    ∃ C : Real, 0 < C ∧
      ∀ (length : Nat) (N K delta Q E : Real),
        1 <= N ->
        1 <= K ->
        0 < delta ->
        (((10 ^ length : Nat) : Real) ^ (17 / 40 : Real)) <= N * K ->
        N / ((10 ^ length : Nat) : Real) <= delta ->
        1 <= Q ->
        Q <= Real.sqrt ((10 ^ length : Nat) : Real) ->
        0 <= E ->
        E <= 100 * Real.sqrt ((10 ^ length : Nat) : Real) / Q ->
        (latticeGeneratingPairs (X := 10 ^ length) N K delta ∩
          (latticeRationalApproximationBand (X := 10 ^ length) Q E ×ˢ
            latticeRationalApproximationBand
              (X := 10 ^ length) Q E)).Nonempty ->
        Q + E <= C *
          (((10 ^ length : Nat) : Real) / (N * K)) ^ 2 := by
  refine ⟨1030301000000000000, by norm_num, ?_⟩
  intro length N K delta Q E hN hK hdelta hgrowth hdeltaLower
    hQ hQupper hE hEupper hnonempty
  exact latticeRationalApproximationSize
    length N K delta Q E hN hK hdelta hgrowth hdeltaLower
      hQ hQupper hE hEupper hnonempty

end PrimesRestrictedDigits
