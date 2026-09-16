import PrimesRestrictedDigits.ExceptionalMinorArcs.LineGeneratingPairs

/-!
# Cardinality of line-generating pairs

This inserts the repaired relation into the completed estimate at the decimal scales of
Proposition 13.4.
-/

namespace PrimesRestrictedDigits

/-- Uniform decimal-scale bound for the exact source line-pair carrier. The
height-below-one case is empty, so no extra height hypothesis is needed. -/
theorem exists_card_lineGeneratingPairs_le_threshold
    (rho : Real) (hrho : 0 < rho) :
    exists length0 : Nat, forall length : Nat, length0 <= length ->
      forall (C : Finset (Fin (10 ^ length))) (delta N K : Real),
        let X : Real := ((10 ^ length : Nat) : Real)
        let H : Real := (C.card : Real)
        let V : Real := 4 * X / (N ^ 2 * K)
        X ^ (9 / 25 : Real) <= N ->
        1 <= K ->
        N <= delta * X ->
        ((lineGeneratingPairs C delta N K).card : Real) <=
          X ^ rho *
            (H ^ (5 / 4 : Real) * V ^ 2 +
              H ^ (3 / 2 : Real) * V ^ 3 /
                X ^ (1 / 2 : Real)) := by
  obtain ⟨lengthScale, hscale⟩ := eventually_two_le_lineCountScale
  obtain ⟨lengthPlane, hplane⟩ :=
    exists_card_lowHeightPlanePairs_le_threshold rho hrho
  refine ⟨max lengthScale lengthPlane, ?_⟩
  intro length hlength C delta N K
  dsimp only
  intro hNlower hK hwidth
  let X : Real := ((10 ^ length : Nat) : Real)
  let H : Real := (C.card : Real)
  let V : Real := 4 * X / (N ^ 2 * K)
  change ((lineGeneratingPairs C delta N K).card : Real) <=
    X ^ rho *
      (H ^ (5 / 4 : Real) * V ^ 2 +
        H ^ (3 / 2 : Real) * V ^ 3 / X ^ (1 / 2 : Real))
  have hlengthScale : lengthScale <= length := by omega
  have hlengthPlane : lengthPlane <= length := by omega
  have hXNat : 0 < 10 ^ length := by positivity
  have hX : 0 < X := by
    dsimp only [X]
    positivity
  have hN : 0 < N :=
    (Real.rpow_pos_of_pos hX (9 / 25 : Real)).trans_le hNlower
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hNdiv : N / X <= delta := by
    apply (div_le_iff₀ hX).2
    simpa [X] using hwidth
  have hdelta : 0 < delta := (div_pos hN hX).trans_le hNdiv
  have hscaleAtLength : 2 <= delta * N ^ 2 * K := by
    exact hscale length hlengthScale N K delta hNlower hK hwidth
  have hV : 0 < V := by
    dsimp only [V]
    positivity
  by_cases hVOne : V < 1
  · have hempty : lineGeneratingPairs C delta N K = Finset.empty := by
      apply lineGeneratingPairs_eq_empty_of_height_lt_one hXNat C
        delta N K hdelta hN hKpos hscaleAtLength
      · simpa only [X] using hwidth
      · simpa only [V, X] using hVOne
    calc
      ((lineGeneratingPairs C delta N K).card : Real) = 0 := by
        rw [hempty]
        norm_num
      _ <= X ^ rho *
          (H ^ (5 / 4 : Real) * V ^ 2 +
            H ^ (3 / 2 : Real) * V ^ 3 /
              X ^ (1 / 2 : Real)) :=
        mul_nonneg (Real.rpow_nonneg hX.le rho) (by positivity)
  · have hVOne' : 1 <= V := le_of_not_gt hVOne
    have hsubset : lineGeneratingPairs C delta N K ⊆
        lowHeightPlanePairs C V := by
      simpa only [V, X] using
        lineGeneratingPairs_subset_lowHeightPlanePairs hXNat C
          delta N K hdelta hN hKpos hscaleAtLength (by
            simpa only [X] using hwidth)
    have hcard : ((lineGeneratingPairs C delta N K).card : Real) <=
        ((lowHeightPlanePairs C V).card : Real) := by
      exact_mod_cast Finset.card_le_card hsubset
    calc
      ((lineGeneratingPairs C delta N K).card : Real) <=
          ((lowHeightPlanePairs C V).card : Real) := hcard
      _ <= X ^ rho *
          (H ^ (5 / 4 : Real) * V ^ 2 +
            H ^ (3 / 2 : Real) * V ^ 3 /
              X ^ (1 / 2 : Real)) := by
        simpa only [X, H] using
          hplane length hlengthPlane C V hVOne'

end PrimesRestrictedDigits
