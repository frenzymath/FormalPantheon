import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitPrimeExceptionalJoin

/-!
# Proposition 9.3: exceptional minor arcs

This is the repaired fixed-length decimal form of Maynard's published Proposition 9.3. It
retains the arbitrary exceptional set and its source cardinality hypothesis.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Natural-logarithmic-power strengthening of Proposition 9.3. The major-arc
exponent is chosen before the fixed convenience margin. -/
theorem exists_exceptionalMinorArcPropositionNatThreshold
    (A : Nat) (eta : Real) (heta : 0 < eta) :
    ∃ D : Nat, 0 < D ∧
      ∀ mu : Real, 0 < mu → ∃ length0 : Nat,
      ∀ length : Nat, length0 ≤ length →
      ∀ (digit : Fin 10) (k : Nat) (a : Fin k → Real)
        (I : Finset (Fin k)) (E : Finset (Fin (10 ^ length))),
        let X : Real := ((10 ^ length : Nat) : Real)
        let delta := majorArcM2LogLogDelta (10 ^ length)
        (∀ i, eta / 2 ≤ a i) →
        (∑ i, a i) < 1 - eta / 2 →
        ((k + 1 : Nat) : Real) ≤ 2 / eta →
        ((∑ i ∈ I, a i) ∈
            Set.Icc (9 / 25 + mu) (17 / 40 - mu) ∨
          (∑ i ∈ I, a i) ∈
            Set.Icc (23 / 40 + mu) (16 / 25 - mu)) →
        (E.card : Real) ≤ X ^ (23 / 40 : Real) →
        ‖∑ h ∈ exceptionalMinorArcFrequencies length D E,
            paddedDigitFourierSum digit length h.val *
              majorArcWeightedPhaseSum (Finset.range (10 ^ length))
                (fun r => (majorArcRegionWeightAtProduct
                  (10 ^ length) a delta eta r : Complex))
                (-((h.val : Real) / X))‖ / X ≤
          3 * ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log X ^ A := by
  obtain ⟨D, joinLength, hD, hjoin⟩ :=
    exists_norm_splitPrimeExceptionalLogSaving A eta heta
  refine ⟨D, hD, ?_⟩
  intro mu hmu
  obtain ⟨marginLength, hmargin⟩ :=
    exists_exceptionalLogLogWidthMarginThreshold eta mu heta hmu
  refine ⟨max joinLength marginLength, ?_⟩
  intro length hlength digit k a I E
  dsimp only
  intro _hanchors _hsum hell hconvenient hcard
  have hjoinLength : joinLength ≤ length :=
    (le_max_left joinLength marginLength).trans hlength
  have hmarginLength : marginLength ≤ length :=
    (le_max_right joinLength marginLength).trans hlength
  have hmarginAt := (hmargin length hmarginLength).2 k hell
  have hdeltaNonneg := (hmargin length hmarginLength).1
  have hbound := hjoin length hjoinLength digit k a
    (majorArcM2LogLogDelta (10 ^ length)) mu I E hcard hell
      hdeltaNonneg hmarginAt hconvenient
  exact hbound

/-- Published real-exponent form of Proposition 9.3. Applying the natural
theorem at `ceil A` preserves the source dependence of the major-arc cutoff. -/
theorem exists_exceptionalMinorArcPropositionThreshold
    (A eta : Real) (hA : 0 < A) (heta : 0 < eta) :
    ∃ D : Nat, 0 < D ∧
      ∀ mu : Real, 0 < mu → ∃ length0 : Nat,
      ∀ length : Nat, length0 ≤ length →
      ∀ (digit : Fin 10) (k : Nat) (a : Fin k → Real)
        (I : Finset (Fin k)) (E : Finset (Fin (10 ^ length))),
        let X : Real := ((10 ^ length : Nat) : Real)
        let delta := majorArcM2LogLogDelta (10 ^ length)
        (∀ i, eta / 2 ≤ a i) →
        (∑ i, a i) < 1 - eta / 2 →
        ((k + 1 : Nat) : Real) ≤ 2 / eta →
        ((∑ i ∈ I, a i) ∈
            Set.Icc (9 / 25 + mu) (17 / 40 - mu) ∨
          (∑ i ∈ I, a i) ∈
            Set.Icc (23 / 40 + mu) (16 / 25 - mu)) →
        (E.card : Real) ≤ X ^ (23 / 40 : Real) →
        ‖∑ h ∈ exceptionalMinorArcFrequencies length D E,
            paddedDigitFourierSum digit length h.val *
              majorArcWeightedPhaseSum (Finset.range (10 ^ length))
                (fun r => (majorArcRegionWeightAtProduct
                  (10 ^ length) a delta eta r : Complex))
                (-((h.val : Real) / X))‖ / X ≤
          3 * ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log X ^ A := by
  let N := Nat.ceil A
  have hNPos : 0 < N := by
    dsimp only [N]
    exact Nat.ceil_pos.mpr hA
  obtain ⟨D, hD, hnat⟩ :=
    exists_exceptionalMinorArcPropositionNatThreshold N eta heta
  refine ⟨D, hD, ?_⟩
  intro mu hmu
  obtain ⟨natLength, hnatLength⟩ := hnat mu hmu
  refine ⟨max natLength 1, ?_⟩
  intro length hlength digit k a I E
  dsimp only
  intro hanchors hsum hell hconvenient hcard
  have hnatLengthAt : natLength ≤ length :=
    (le_max_left natLength 1).trans hlength
  have hlengthOne : 1 ≤ length :=
    (le_max_right natLength 1).trans hlength
  let X : Real := ((10 ^ length : Nat) : Real)
  have hnatBound := hnatLength length hnatLengthAt digit k a I E
    hanchors hsum hell hconvenient hcard
  have hlogOne : 1 ≤ Real.log X := by
    dsimp only [X]
    exact one_le_log_powTen_of_pos (Nat.zero_lt_of_lt hlengthOne)
  have hlogPos : 0 < Real.log X := zero_lt_one.trans_le hlogOne
  have hAceil : A ≤ (N : Real) := by
    dsimp only [N]
    exact Nat.le_ceil A
  have hdenominator : Real.log X ^ A ≤ Real.log X ^ N := by
    calc
      Real.log X ^ A ≤ Real.log X ^ (N : Real) :=
        Real.rpow_le_rpow_of_exponent_le hlogOne hAceil
      _ = Real.log X ^ N := by rw [Real.rpow_natCast]
  have hnumerator :
      0 ≤ 3 * ((paddedRestrictedNumbers digit length).card : Real) := by
    positivity
  have hweaken :
      3 * ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log X ^ N ≤
        3 * ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log X ^ A :=
    div_le_div_of_nonneg_left hnumerator
      (Real.rpow_pos_of_pos hlogPos A) hdenominator
  exact hnatBound.trans <| by
    simpa only [X, N] using hweaken

end

end PrimesRestrictedDigits
