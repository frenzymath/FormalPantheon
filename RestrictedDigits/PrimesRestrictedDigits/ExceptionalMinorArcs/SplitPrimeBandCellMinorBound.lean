import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitPrimeBandCellPerronContour
import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitPrimeBandSourceAssembly

/-!
# One-cell bound outside a general major-arc cutoff

For a nonempty canonical rational fiber outside the raw major arcs, its scale satisfies `H < Q
+ E`. Empty fibers give zero strict sums. This replaces the cell denominator by `H` without
charging empty cells.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Every active rational/product cell outside a positive raw-major-arc
cutoff has a uniform strict-sum bound with denominator `H`. -/
theorem exists_splitPrimeBandCellMinorBound :
    ∃ C : Real, 0 < C ∧ ∃ logLoss length0 : Nat,
      ∀ length : Nat, length0 ≤ length →
      ∀ (digit : Fin 10) (k : Nat) (a : Fin k → Real)
        (delta eta mu H : Real) (I : Finset (Fin k))
        (S : Finset (Fin (10 ^ length)))
        (bandKey productKey : Nat × Nat),
        let X : Real := ((10 ^ length : Nat) : Real)
        let A := selectedPrimePerronCoefficientCap (10 ^ length) I
        let B := complementaryPrimePerronCoefficientCap (10 ^ length) I
        0 < H →
        (∀ h ∈ S,
          h.val ∉ majorArcRawFrequencies (10 ^ length) H) →
        0 ≤ delta →
        ((k + 1 : Nat) : Real) * delta + 1 / (length : Real) ≤ mu →
        ((∑ i ∈ I, a i) ∈
            Set.Icc (9 / 25 + mu) (17 / 40 - mu) ∨
          (∑ i ∈ I, a i) ∈
            Set.Icc (23 / 40 + mu) (16 / 25 - mu)) →
        S ⊆ genericExceptionalFrequencies digit length →
        IsActiveSplitPrimeCell length a delta eta I productKey →
        ‖splitPrimeBandCellStrictSum digit length a delta eta I S
            bandKey productKey‖ ≤
          20 * ((exceptionalDirichletBandFiber S bandKey).card : Real) *
              A * B / X +
            30 * A * B *
                (C * X * Real.log X ^ logLoss /
                  H ^ (latticeSumSaving / 10)) *
              Real.log X := by
  obtain ⟨C, hC, logLoss, cellLength, hcell⟩ :=
    exists_activeSplitPrimeBandCellPerronBounds
  refine ⟨C, hC, logLoss, max cellLength 1, ?_⟩
  intro length hlength digit k a delta eta mu H I S bandKey productKey
  dsimp only
  intro hH hminor hdelta hmargin hconvenient hS hactive
  have hcellLength : cellLength ≤ length :=
    (le_max_left cellLength 1).trans hlength
  have hlengthOne : 1 ≤ length :=
    (le_max_right cellLength 1).trans hlength
  have hlengthPos : 0 < length := Nat.zero_lt_of_lt hlengthOne
  let X : Real := ((10 ^ length : Nat) : Real)
  let Q := exceptionalDirichletDenominatorScaleAt
    (10 ^ length) bandKey.1
  let E := exceptionalDirichletErrorScaleAt
    (10 ^ length) bandKey.2
  let A := selectedPrimePerronCoefficientCap (10 ^ length) I
  let B := complementaryPrimePerronCoefficientCap (10 ^ length) I
  have hcellBound := (hcell length hcellLength digit k a delta eta mu I S
    bandKey productKey hdelta hmargin hconvenient hS hactive).2
  by_cases hfiber :
      (exceptionalDirichletBandFiber S bandKey).Nonempty
  · obtain ⟨h, hh⟩ := hfiber
    have hhS : h ∈ S :=
      (mem_exceptionalDirichletBandFiber_iff.mp hh).1
    have hscale : H < Q + E := by
      dsimp only [Q, E]
      exact exceptionalMajorArcCutoff_lt_add_of_mem_fiber
        hlengthPos hh (hminor h hhS)
    have hpow : H ^ (latticeSumSaving / 10) ≤
        (Q + E) ^ (latticeSumSaving / 10) :=
      Real.rpow_le_rpow hH.le hscale.le
        (by positivity [latticeSumSaving_pos])
    have hnumerator :
        0 ≤ C * X * Real.log X ^ logLoss := by
      have hXOne : (1 : Real) < X := by
        dsimp only [X]
        exact_mod_cast Nat.one_lt_pow hlengthPos.ne'
          (by norm_num : 1 < 10)
      have hlog : 0 ≤ Real.log X := (Real.log_pos hXOne).le
      positivity
    have hquotient :
        C * X * Real.log X ^ logLoss /
            (Q + E) ^ (latticeSumSaving / 10) ≤
          C * X * Real.log X ^ logLoss /
            H ^ (latticeSumSaving / 10) :=
      div_le_div_of_nonneg_left hnumerator
        (Real.rpow_pos_of_pos hH _ ) hpow
    have hcontour :
        30 * (A * B *
              (C * X * Real.log X ^ logLoss /
                (Q + E) ^ (latticeSumSaving / 10))) *
            Real.log X ≤
          30 * A * B *
              (C * X * Real.log X ^ logLoss /
                H ^ (latticeSumSaving / 10)) *
            Real.log X := by
      have hXOne : (1 : Real) < X := by
        dsimp only [X]
        exact_mod_cast Nat.one_lt_pow hlengthPos.ne'
          (by norm_num : 1 < 10)
      have hlog : 0 ≤ Real.log X := (Real.log_pos hXOne).le
      have hAPos : 0 < A := by
        dsimp only [A]
        exact selectedPrimePerronCoefficientCap_pos
          (Nat.one_lt_pow hlengthPos.ne' (by norm_num)) I
      have hBPos : 0 < B := by
        dsimp only [B]
        exact complementaryPrimePerronCoefficientCap_pos
          (Nat.one_lt_pow hlengthPos.ne' (by norm_num)) I
      calc
        30 * (A * B *
              (C * X * Real.log X ^ logLoss /
                (Q + E) ^ (latticeSumSaving / 10))) *
            Real.log X =
            (30 * A * B) *
                (C * X * Real.log X ^ logLoss /
                  (Q + E) ^ (latticeSumSaving / 10)) *
              Real.log X := by ring
        _ ≤ (30 * A * B) *
                (C * X * Real.log X ^ logLoss /
                  H ^ (latticeSumSaving / 10)) *
              Real.log X := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hquotient
              (mul_nonneg (mul_nonneg (by norm_num) hAPos.le) hBPos.le))
            hlog
        _ = 30 * A * B *
              (C * X * Real.log X ^ logLoss /
                H ^ (latticeSumSaving / 10)) *
            Real.log X := by ring
    exact hcellBound.trans <| by
      have hadd := add_le_add_left hcontour
        (20 * ((exceptionalDirichletBandFiber S bandKey).card : Real) *
          A * B / X)
      dsimp only [X, A, B, Q, E] at hadd
      simpa only [add_comm] using hadd
  · have hfiberEmpty : exceptionalDirichletBandFiber S bandKey = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hfiber
    rw [splitPrimeBandCellStrictSum_eq_frequencySum, hfiberEmpty]
    simp only [Finset.sum_empty, norm_zero, Finset.card_empty, Nat.cast_zero]
    have hXOne : (1 : Real) < X := by
      dsimp only [X]
      exact_mod_cast Nat.one_lt_pow hlengthPos.ne'
        (by norm_num : 1 < 10)
    have hAPos : 0 < A := by
      dsimp only [A]
      exact selectedPrimePerronCoefficientCap_pos
        (Nat.one_lt_pow hlengthPos.ne' (by norm_num)) I
    have hBPos : 0 < B := by
      dsimp only [B]
      exact complementaryPrimePerronCoefficientCap_pos
        (Nat.one_lt_pow hlengthPos.ne' (by norm_num)) I
    positivity [latticeSumSaving_pos]

end

end PrimesRestrictedDigits
