import PrimesRestrictedDigits.ExceptionalMinorArcs.ExceptionalLogAbsorption

/-!
# High-frequency logarithmic saving

This chooses the logarithmic raw-major-arc cutoff and absorbs the two explicit terms in the
arity-uniform exceptional source bound.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The exceptional high-frequency part of the literal source sum has an
arbitrary fixed logarithmic saving after division by the ambient scale. -/
theorem exists_norm_splitPrimeExceptionalHighLogSaving
    (A : Nat) (eta : Real) (heta : 0 < eta) :
    ∃ D length0 : Nat, 0 < D ∧
      ∀ length : Nat, length0 ≤ length →
      ∀ (digit : Fin 10) (k : Nat) (a : Fin k → Real)
        (delta mu : Real) (I : Finset (Fin k))
        (S : Finset (Fin (10 ^ length))),
        let X : Real := ((10 ^ length : Nat) : Real)
        ((k + 1 : Nat) : Real) ≤ 2 / eta →
        (∀ h ∈ S,
          h.val ∉ majorArcRawFrequencies (10 ^ length)
            (Real.log X ^ D)) →
        0 ≤ delta →
        ((k + 1 : Nat) : Real) * delta + 1 / (length : Real) ≤ mu →
        ((∑ i ∈ I, a i) ∈
            Set.Icc (9 / 25 + mu) (17 / 40 - mu) ∨
          (∑ i ∈ I, a i) ∈
            Set.Icc (23 / 40 + mu) (16 / 25 - mu)) →
        S ⊆ genericExceptionalFrequencies digit length →
        ‖∑ h ∈ S,
            paddedDigitFourierSum digit length h.val *
              majorArcWeightedPhaseSum (Finset.range (10 ^ length))
                (fun r => (majorArcRegionWeightAtProduct
                  (10 ^ length) a delta eta r : Complex))
                (-((h.val : Real) / X))‖ / X ≤
          2 * (9 : Real) ^ length / Real.log X ^ A := by
  obtain ⟨C, hC, logLoss, sourceLength, hsource⟩ :=
    exists_norm_splitPrimeExceptionalSource_arity_le
  let L := exceptionalMinorArcArityCeil eta
  let G : Real := Nat.factorial L
  let D := exceptionalMinorArcLogCutoffExponent A logLoss L
  obtain ⟨scalarLength, hscalar⟩ :=
    exists_exceptionalMinorArcLogAbsorptionThreshold
      A logLoss L C G hC.le (by positivity)
  refine ⟨D, max sourceLength scalarLength,
    by exact exceptionalMinorArcLogCutoffExponent_pos A logLoss L, ?_⟩
  intro length hlength digit k a delta mu I S
  dsimp only
  intro hell hminor hdelta hmargin hconvenient hS
  have hsourceLength : sourceLength ≤ length :=
    (le_max_left sourceLength scalarLength).trans hlength
  have hscalarLength : scalarLength ≤ length :=
    (le_max_right sourceLength scalarLength).trans hlength
  let X : Real := ((10 ^ length : Nat) : Real)
  let logX := Real.log X
  have hscalarAt := hscalar length hscalarLength
  have hlogOne : 1 ≤ logX := by
    simpa only [X, logX, D, L, G] using hscalarAt.1
  have hlogPos : 0 < logX := zero_lt_one.trans_le hlogOne
  have hXPos : 0 < X := by dsimp only [X]; positivity
  have hcutoffPos : 0 < logX ^ D := pow_pos hlogPos D
  have herrorScalar :
      80 * G ^ 2 * logX ^ (2 * L + 2) / X ≤
        1 / logX ^ A := by
    simpa only [X, logX, D, L, G] using hscalarAt.2.1
  have hcontourScalar :
      960 * C * G ^ 2 * logX ^ (logLoss + 2 * L + 5) /
          (logX ^ D) ^ (latticeSumSaving / 10) ≤
        1 / logX ^ A := by
    simpa only [X, logX, D, L, G] using hscalarAt.2.2
  have hcardNat : S.card ≤ 10 ^ length := by
    simpa using Finset.card_le_univ S
  have hcard : (S.card : Real) ≤ X := by
    dsimp only [X]
    exact_mod_cast hcardNat
  have hbase := hsource length hsourceLength digit k a delta eta mu
    (logX ^ D) I S heta hell hcutoffPos hminor hdelta hmargin
      hconvenient hS
  have herrorNumerator :
      80 * (S.card : Real) * G ^ 2 * logX ^ (2 * L + 2) ≤
        80 * X * G ^ 2 * logX ^ (2 * L + 2) := by
    gcongr
  have herrorAfterDivision :
      (80 * (S.card : Real) * G ^ 2 *
            logX ^ (2 * L + 2) / X) / X ≤
        1 / logX ^ A := by
    calc
      (80 * (S.card : Real) * G ^ 2 *
            logX ^ (2 * L + 2) / X) / X ≤
          (80 * X * G ^ 2 * logX ^ (2 * L + 2) / X) / X :=
        div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right herrorNumerator hXPos.le) hXPos.le
      _ = 80 * G ^ 2 * logX ^ (2 * L + 2) / X := by
        field_simp [hXPos.ne']
      _ ≤ 1 / logX ^ A := herrorScalar
  have hcontourAfterDivision :
      (960 * C * G ^ 2 * X *
            logX ^ (logLoss + 2 * L + 5) /
          (logX ^ D) ^ (latticeSumSaving / 10)) / X ≤
        1 / logX ^ A := by
    calc
      (960 * C * G ^ 2 * X *
            logX ^ (logLoss + 2 * L + 5) /
          (logX ^ D) ^ (latticeSumSaving / 10)) / X =
          960 * C * G ^ 2 *
              logX ^ (logLoss + 2 * L + 5) /
            (logX ^ D) ^ (latticeSumSaving / 10) := by
        field_simp [hXPos.ne']
      _ ≤ 1 / logX ^ A := hcontourScalar
  let errorTerm : Real :=
    80 * (S.card : Real) * G ^ 2 * logX ^ (2 * L + 2) / X
  let contourTerm : Real :=
    960 * C * G ^ 2 * X * logX ^ (logLoss + 2 * L + 5) /
      (logX ^ D) ^ (latticeSumSaving / 10)
  have hinside :
      (errorTerm + contourTerm) / X ≤ 2 / logX ^ A := by
    calc
      (errorTerm + contourTerm) / X =
          errorTerm / X + contourTerm / X := by ring
      _ ≤ 1 / logX ^ A + 1 / logX ^ A := by
        exact add_le_add
          (by simpa only [errorTerm] using herrorAfterDivision)
          (by simpa only [contourTerm] using hcontourAfterDivision)
      _ = 2 / logX ^ A := by ring
  have hbase' :
      ‖∑ h ∈ S,
          paddedDigitFourierSum digit length h.val *
            majorArcWeightedPhaseSum (Finset.range (10 ^ length))
              (fun r => (majorArcRegionWeightAtProduct
                (10 ^ length) a delta eta r : Complex))
              (-((h.val : Real) / X))‖ ≤
        (9 : Real) ^ length * (errorTerm + contourTerm) := by
    simpa only [X, logX, L, G, D, errorTerm, contourTerm] using hbase
  calc
    ‖∑ h ∈ S,
        paddedDigitFourierSum digit length h.val *
          majorArcWeightedPhaseSum (Finset.range (10 ^ length))
            (fun r => (majorArcRegionWeightAtProduct
              (10 ^ length) a delta eta r : Complex))
            (-((h.val : Real) / X))‖ / X ≤
        ((9 : Real) ^ length * (errorTerm + contourTerm)) / X :=
      div_le_div_of_nonneg_right hbase' hXPos.le
    _ = (9 : Real) ^ length * ((errorTerm + contourTerm) / X) := by ring
    _ ≤ (9 : Real) ^ length * (2 / logX ^ A) :=
      mul_le_mul_of_nonneg_left hinside (by positivity)
    _ = 2 * (9 : Real) ^ length / logX ^ A := by ring

end

end PrimesRestrictedDigits
