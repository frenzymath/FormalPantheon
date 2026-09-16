import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitPrimeBandCellAggregation
import PrimesRestrictedDigits.GenericMinorArcs.PrimeTupleL2

/-!
# Scalar bounds for exceptional minor-cell aggregation

This removes coordinate-subset and key-carrier dependence from the exact canonical-cell
aggregate using the source arity ceiling and explicit logarithmic key bounds.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Uniform natural upper bound for the source region arity. -/
def exceptionalMinorArcArityCeil (eta : Real) : Nat :=
  Nat.ceil (2 / eta)

/-- The two Perron coefficient caps are bounded by the square of one
arity-ceiling cap. -/
theorem selected_mul_complementaryPerronCaps_le_arityCeil
    {X k : Nat} (hX : 4 ≤ X) {eta : Real}
    (hell : ((k + 1 : Nat) : Real) ≤ 2 / eta)
    (I : Finset (Fin k)) :
    selectedPrimePerronCoefficientCap X I *
        complementaryPrimePerronCoefficientCap X I ≤
      (Nat.factorial (exceptionalMinorArcArityCeil eta) : Real) ^ 2 *
        Real.log (X : Real) ^
          (2 * exceptionalMinorArcArityCeil eta) := by
  have hIcard : I.card ≤ k := by
    simpa using Finset.card_le_univ I
  have hIarity : ((I.card : Nat) : Real) ≤ 2 / eta := by
    have hle : I.card ≤ k + 1 := hIcard.trans (Nat.le_succ k)
    have hleReal : (I.card : Real) ≤ ((k + 1 : Nat) : Real) := by
      exact_mod_cast hle
    exact hleReal.trans hell
  have hComplementCard : Iᶜ.card ≤ k := by
    simpa using Finset.card_le_univ Iᶜ
  have hComplementArity : (((Iᶜ.card + 1 : Nat) : Real)) ≤
      2 / eta := by
    have hle : Iᶜ.card + 1 ≤ k + 1 :=
      Nat.add_le_add_right hComplementCard 1
    have hleReal : ((Iᶜ.card + 1 : Nat) : Real) ≤
        ((k + 1 : Nat) : Real) := by
      exact_mod_cast hle
    exact hleReal.trans hell
  let M := (Nat.factorial (exceptionalMinorArcArityCeil eta) : Real) *
    Real.log (X : Real) ^ exceptionalMinorArcArityCeil eta
  have hA : selectedPrimePerronCoefficientCap X I ≤ M := by
    simpa only [selectedPrimePerronCoefficientCap,
      exceptionalMinorArcArityCeil, M] using
      factorial_mul_log_pow_le_arityCeil hX hIarity
  have hB : complementaryPrimePerronCoefficientCap X I ≤ M := by
    simpa only [complementaryPrimePerronCoefficientCap,
      exceptionalMinorArcArityCeil, M] using
      factorial_mul_log_pow_le_arityCeil hX hComplementArity
  have hANonneg : 0 ≤ selectedPrimePerronCoefficientCap X I := by
    exact (selectedPrimePerronCoefficientCap_pos (by omega) I).le
  have hBNonneg : 0 ≤ complementaryPrimePerronCoefficientCap X I := by
    exact (complementaryPrimePerronCoefficientCap_pos (by omega) I).le
  have hMNonneg : 0 ≤ M := hANonneg.trans hA
  calc
    selectedPrimePerronCoefficientCap X I *
        complementaryPrimePerronCoefficientCap X I ≤
        M * complementaryPrimePerronCoefficientCap X I :=
      mul_le_mul_of_nonneg_right hA hBNonneg
    _ ≤ M * M := mul_le_mul_of_nonneg_left hB hMNonneg
    _ = (Nat.factorial (exceptionalMinorArcArityCeil eta) : Real) ^ 2 *
        Real.log (X : Real) ^
          (2 * exceptionalMinorArcArityCeil eta) := by
      dsimp only [M]
      calc
        (Nat.factorial (exceptionalMinorArcArityCeil eta) : Real) *
              Real.log (X : Real) ^ exceptionalMinorArcArityCeil eta *
            ((Nat.factorial (exceptionalMinorArcArityCeil eta) : Real) *
              Real.log (X : Real) ^ exceptionalMinorArcArityCeil eta) =
            (Nat.factorial (exceptionalMinorArcArityCeil eta) : Real) ^ 2 *
              (Real.log (X : Real) ^
                exceptionalMinorArcArityCeil eta) ^ 2 := by ring
        _ = (Nat.factorial (exceptionalMinorArcArityCeil eta) : Real) ^ 2 *
              Real.log (X : Real) ^
                (2 * exceptionalMinorArcArityCeil eta) := by
          rw [← pow_mul]
          congr 2
          omega

/-- At a positive decimal length, the successor length is bounded by twice
the ambient logarithm. -/
theorem length_succ_le_two_mul_log_powTen
    {length : Nat} (hlength : 0 < length) :
    ((length + 1 : Nat) : Real) ≤
      2 * Real.log ((10 ^ length : Nat) : Real) := by
  have hlogTen : (1 : Real) ≤ Real.log 10 := by
    have hten : (0 : Real) < 10 := by norm_num
    apply (Real.le_log_iff_exp_le hten).2
    exact Real.exp_one_lt_three.le.trans (by norm_num)
  have hlengthOne : (1 : Real) ≤ length := by exact_mod_cast hlength
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_pow]
  have hmul : (length : Real) ≤ (length : Real) * Real.log 10 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg length) (sub_nonneg.mpr hlogTen)]
  nlinarith

/-- Active product cells cost at most two logarithms. -/
theorem card_activeSplitPrimeCellKeys_real_le_log_sq
    {length : Nat} (hlength : 0 < length)
    {k : Nat} (a : Fin k → Real) (delta eta : Real)
    (I : Finset (Fin k)) :
    ((activeSplitPrimeCellKeys length a delta eta I).card : Real) ≤
      4 * Real.log ((10 ^ length : Nat) : Real) ^ 2 := by
  have hcard :
      ((activeSplitPrimeCellKeys length a delta eta I).card : Real) ≤
        (((length + 1) ^ 2 : Nat) : Real) := by
    exact_mod_cast card_activeSplitPrimeCellKeys_le length a delta eta I
  have hlength := length_succ_le_two_mul_log_powTen hlength
  calc
    ((activeSplitPrimeCellKeys length a delta eta I).card : Real) ≤
        (((length + 1) ^ 2 : Nat) : Real) := hcard
    _ = (((length + 1 : Nat) : Real)) ^ 2 := by norm_num
    _ ≤ (2 * Real.log ((10 ^ length : Nat) : Real)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlength 2
    _ = 4 * Real.log ((10 ^ length : Nat) : Real) ^ 2 := by ring

/-- Canonical rational keys also cost at most two logarithms, with the exact
factor two retained. -/
theorem card_exceptionalDirichletBandKeys_real_le_log_sq
    {length : Nat} (hlength : 0 < length) :
    ((exceptionalDirichletBandKeys length).card : Real) ≤
      8 * Real.log ((10 ^ length : Nat) : Real) ^ 2 := by
  have hlength := length_succ_le_two_mul_log_powTen hlength
  rw [card_exceptionalDirichletBandKeys]
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat]
  calc
    ((length : Real) + 1) * (2 * (length : Real) + 2) =
        2 * ((length : Real) + 1) ^ 2 := by ring
    _ ≤ 2 * (2 * Real.log ((10 ^ length : Nat) : Real)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by simpa using hlength) 2)
        (by norm_num)
    _ = 8 * Real.log ((10 ^ length : Nat) : Real) ^ 2 := by ring

end

end PrimesRestrictedDigits
