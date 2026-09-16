import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitPrimeAggregationScalars

/-!
# Arity-uniform exceptional source bound

This inserts the common arity cap and the logarithmic canonical-key bounds into the exact
minor-cell aggregate. The major-arc cutoff remains a general positive real parameter.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The exact canonical-cell aggregate admits explicit arity-uniform
coefficients `80` and `960`. -/
theorem exists_norm_splitPrimeExceptionalSource_arity_le :
    ∃ C : Real, 0 < C ∧ ∃ logLoss length0 : Nat,
      ∀ length : Nat, length0 ≤ length →
      ∀ (digit : Fin 10) (k : Nat) (a : Fin k → Real)
        (delta eta mu H : Real) (I : Finset (Fin k))
        (S : Finset (Fin (10 ^ length))),
        let X : Real := ((10 ^ length : Nat) : Real)
        let L := exceptionalMinorArcArityCeil eta
        let G : Real := Nat.factorial L
        0 < eta →
        ((k + 1 : Nat) : Real) ≤ 2 / eta →
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
        ‖∑ h ∈ S,
            paddedDigitFourierSum digit length h.val *
              majorArcWeightedPhaseSum (Finset.range (10 ^ length))
                (fun r => (majorArcRegionWeightAtProduct
                  (10 ^ length) a delta eta r : Complex))
                (-((h.val : Real) / X))‖ ≤
          (9 : Real) ^ length *
            (80 * (S.card : Real) * G ^ 2 *
                Real.log X ^ (2 * L + 2) / X +
              960 * C * G ^ 2 * X *
                  Real.log X ^ (logLoss + 2 * L + 5) /
                H ^ (latticeSumSaving / 10)) := by
  obtain ⟨C, hC, logLoss, sourceLength, hsource⟩ :=
    exists_norm_splitPrimeExceptionalSource_le
  refine ⟨C, hC, logLoss, max sourceLength 1, ?_⟩
  intro length hlength digit k a delta eta mu H I S
  dsimp only
  intro heta hell hH hminor hdelta hmargin hconvenient hS
  have hsourceLength : sourceLength ≤ length :=
    (le_max_left sourceLength 1).trans hlength
  have hlengthOne : 1 ≤ length :=
    (le_max_right sourceLength 1).trans hlength
  have hlengthPos : 0 < length := Nat.zero_lt_of_lt hlengthOne
  let X : Real := ((10 ^ length : Nat) : Real)
  let L := exceptionalMinorArcArityCeil eta
  let G : Real := Nat.factorial L
  let A := selectedPrimePerronCoefficientCap (10 ^ length) I
  let B := complementaryPrimePerronCoefficientCap (10 ^ length) I
  let P : Real :=
    (activeSplitPrimeCellKeys length a delta eta I).card
  let R : Real := (exceptionalDirichletBandKeys length).card
  let logX := Real.log X
  have hXFour : 4 ≤ 10 ^ length := by
    have hten : 10 ≤ 10 ^ length := by
      simpa only [pow_one] using
        (pow_le_pow_right₀ (by norm_num : (1 : Nat) ≤ 10) hlengthOne)
    omega
  have hXOne : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow hlengthPos.ne' (by norm_num : 1 < 10)
  have hXPos : 0 < X := zero_lt_one.trans hXOne
  have hlogPos : 0 < logX := by
    dsimp only [logX]
    exact Real.log_pos hXOne
  have hAB : A * B ≤ G ^ 2 * logX ^ (2 * L) := by
    simpa only [X, L, G, A, B, logX] using
      selected_mul_complementaryPerronCaps_le_arityCeil
        hXFour hell I
  have hANonneg : 0 ≤ A := by
    dsimp only [A]
    exact (selectedPrimePerronCoefficientCap_pos
      (Nat.one_lt_pow hlengthPos.ne' (by norm_num)) I).le
  have hBNonneg : 0 ≤ B := by
    dsimp only [B]
    exact (complementaryPrimePerronCoefficientCap_pos
      (Nat.one_lt_pow hlengthPos.ne' (by norm_num)) I).le
  have hABNonneg : 0 ≤ A * B := mul_nonneg hANonneg hBNonneg
  have hGlogNonneg : 0 ≤ G ^ 2 * logX ^ (2 * L) := by positivity
  have hP : P ≤ 4 * logX ^ 2 := by
    simpa only [P, X, logX] using
      card_activeSplitPrimeCellKeys_real_le_log_sq
        hlengthPos a delta eta I
  have hR : R ≤ 8 * logX ^ 2 := by
    simpa only [R, X, logX] using
      card_exceptionalDirichletBandKeys_real_le_log_sq hlengthPos
  have hPNonneg : 0 ≤ P := by dsimp only [P]; positivity
  have hRNonneg : 0 ≤ R := by dsimp only [R]; positivity
  have hSNonneg : 0 ≤ (S.card : Real) := by positivity
  have hPAB : P * (A * B) ≤
      (4 * logX ^ 2) * (G ^ 2 * logX ^ (2 * L)) :=
    mul_le_mul hP hAB hABNonneg (by positivity)
  have herror :
      20 * P * (S.card : Real) * A * B / X ≤
        80 * (S.card : Real) * G ^ 2 *
          logX ^ (2 * L + 2) / X := by
    apply div_le_div_of_nonneg_right
    calc
      20 * P * (S.card : Real) * A * B =
          20 * (S.card : Real) * (P * (A * B)) := by ring
      _ ≤ 20 * (S.card : Real) *
          ((4 * logX ^ 2) * (G ^ 2 * logX ^ (2 * L))) :=
        mul_le_mul_of_nonneg_left hPAB
          (mul_nonneg (by norm_num) hSNonneg)
      _ = 80 * (S.card : Real) * G ^ 2 *
          logX ^ (2 * L + 2) := by
        rw [pow_add]
        ring
    exact hXPos.le
  have hRP : R * P ≤
      (8 * logX ^ 2) * (4 * logX ^ 2) :=
    mul_le_mul hR hP hPNonneg (by positivity)
  have hRPAB : (R * P) * (A * B) ≤
      ((8 * logX ^ 2) * (4 * logX ^ 2)) *
        (G ^ 2 * logX ^ (2 * L)) :=
    mul_le_mul hRP hAB hABNonneg (by positivity)
  have hcutoffPos : 0 < H ^ (latticeSumSaving / 10) :=
    Real.rpow_pos_of_pos hH _
  have hfactorNonneg :
      0 ≤ C * X * logX ^ logLoss /
          H ^ (latticeSumSaving / 10) * logX := by
    positivity
  have hcontour :
      R * P *
          (30 * A * B *
              (C * X * logX ^ logLoss /
                H ^ (latticeSumSaving / 10)) *
            logX) ≤
        960 * C * G ^ 2 * X *
            logX ^ (logLoss + 2 * L + 5) /
          H ^ (latticeSumSaving / 10) := by
    calc
      R * P *
          (30 * A * B *
              (C * X * logX ^ logLoss /
                H ^ (latticeSumSaving / 10)) *
            logX) =
          30 * ((R * P) * (A * B)) *
            (C * X * logX ^ logLoss /
              H ^ (latticeSumSaving / 10) * logX) := by ring
      _ ≤ 30 *
            (((8 * logX ^ 2) * (4 * logX ^ 2)) *
              (G ^ 2 * logX ^ (2 * L))) *
            (C * X * logX ^ logLoss /
              H ^ (latticeSumSaving / 10) * logX) := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hRPAB hfactorNonneg)
            (by norm_num : (0 : Real) ≤ 30)
      _ = 960 * C * G ^ 2 * X *
            logX ^ (logLoss + 2 * L + 5) /
          H ^ (latticeSumSaving / 10) := by
        rw [show logLoss + 2 * L + 5 =
          2 + 2 + 2 * L + logLoss + 1 by omega]
        rw [pow_add, pow_add, pow_add, pow_succ]
        field_simp [hcutoffPos.ne']
        ring
  have hbase := hsource length hsourceLength digit k a delta eta mu H I S
    hH hminor hdelta hmargin hconvenient hS
  have hinside :
      20 * P * (S.card : Real) * A * B / X +
          R * P *
            (30 * A * B *
                (C * X * logX ^ logLoss /
                  H ^ (latticeSumSaving / 10)) *
              logX) ≤
        80 * (S.card : Real) * G ^ 2 *
              logX ^ (2 * L + 2) / X +
          960 * C * G ^ 2 * X *
              logX ^ (logLoss + 2 * L + 5) /
            H ^ (latticeSumSaving / 10) :=
    add_le_add herror hcontour
  exact hbase.trans <| by
    dsimp only [X, L, G, A, B, P, R, logX] at hinside ⊢
    exact mul_le_mul_of_nonneg_left hinside (by positivity)

end

end PrimesRestrictedDigits
