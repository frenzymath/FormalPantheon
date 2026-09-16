import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearCauchyAbsorption

/-!
# Repaired exceptional bilinear sum bound

This proves the source-facing form of Maynard's Lemma 13.1. The reference is
`MAYNARD-PRD-PUBLISHED`, pp. 191--198.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Repaired Lemma 13.1. The comparison constant, logarithmic loss, and
decimal-length threshold are uniform in the excluded digit, all scale
parameters, and all one-bounded coefficient sequences. -/
theorem exists_exceptionalBilinearSumBound :
    ∃ C : Real, 0 < C ∧ ∃ logLoss length0 : Nat,
      ∀ length : Nat, length0 <= length ->
      ∀ (digit : Fin 10) (N M Q E : Real)
        (alpha beta : Nat -> Complex)
        (gamma : Fin (10 ^ length) -> Complex),
        let X : Real := ((10 ^ length : Nat) : Real)
        1 <= N ->
        1 <= M ->
        1 <= Q ->
        0 <= E ->
        X ^ (9 / 25 : Real) <= N ->
        N <= X ^ (17 / 40 : Real) ->
        Q <= Real.sqrt X ->
        N * M <= 1000 * X ->
        E <= 100 * Real.sqrt X / Q ->
        (E = 0 ∨ 1 / X <= E) ->
        (∀ n, ‖alpha n‖ <= 1) ->
        (∀ m, ‖beta m‖ <= 1) ->
        (∀ a, ‖gamma a‖ <= 1) ->
        ‖exceptionalBilinearSum
          digit length N M Q E alpha beta gamma‖ <=
            C * X * Real.log X ^ logLoss /
              (Q + E) ^ (latticeSumSaving / 10) := by
  obtain ⟨C, hC, sliceLength, hslice⟩ :=
    exists_exceptionalBilinearSumOver_magnitudeBand_bound
  refine ⟨C, hC, 5, max sliceLength 1, ?_⟩
  intro length hlength digit N M Q E alpha beta gamma
  dsimp only
  intro hN hM hQ hE hNLower hNUpper hQUpper hNM hEUpper _hEscale
    halpha hbeta hgamma
  let X : Real := ((10 ^ length : Nat) : Real)
  let L : Real := Real.log X
  let R : Real := Q + E
  have hsliceLength : sliceLength <= length :=
    (le_max_left sliceLength 1).trans hlength
  have hlengthOne : 1 <= length :=
    (le_max_right sliceLength 1).trans hlength
  have hlengthPos : 0 < length := Nat.zero_lt_of_lt hlengthOne
  have hX : 0 < X := by dsimp only [X]; positivity
  have hL : 1 <= L := by
    dsimp only [L, X]
    exact one_le_log_decimalScale hlengthOne
  have hR : 0 < R := by dsimp only [R]; linarith
  have htargetNonneg : 0 <=
      C * X * L ^ 4 / R ^ (latticeSumSaving / 10) := by positivity
  have hfiber (j : Nat) :
      ‖exceptionalBilinearSumOver digit length
        (exceptionalRationalMagnitudeBandFrequencies
          digit length Q E j) N M alpha beta gamma‖ <=
        C * X * L ^ 4 / R ^ (latticeSumSaving / 10) := by
    have hbound := hslice length hsliceLength digit j N M Q E
      alpha beta gamma hN hM hNLower hNUpper hQ hQUpper hE hEUpper
        hNM halpha hbeta hgamma
    simpa only [X, L, R] using hbound
  calc
    ‖exceptionalBilinearSum
        digit length N M Q E alpha beta gamma‖ <=
        ∑ j ∈ Finset.range length,
          ‖exceptionalBilinearSumOver digit length
            (exceptionalRationalMagnitudeBandFrequencies
              digit length Q E j) N M alpha beta gamma‖ := by
      exact norm_exceptionalBilinearSum_le_sum_magnitudeBands
        digit hlengthPos N M Q E alpha beta gamma
    _ <= ∑ _j ∈ Finset.range length,
        C * X * L ^ 4 / R ^ (latticeSumSaving / 10) := by
      exact Finset.sum_le_sum fun j hj => hfiber j
    _ = (length : Real) *
        (C * X * L ^ 4 / R ^ (latticeSumSaving / 10)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ <= L * (C * X * L ^ 4 /
        R ^ (latticeSumSaving / 10)) := by
      exact mul_le_mul_of_nonneg_right
        (bilinear_length_cast_le_log_decimalScale hlengthOne)
        htargetNonneg
    _ = C * X * L ^ 5 / R ^ (latticeSumSaving / 10) := by ring

end

end PrimesRestrictedDigits
