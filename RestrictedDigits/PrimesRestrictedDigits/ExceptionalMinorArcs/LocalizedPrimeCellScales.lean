import PrimesRestrictedDigits.ExceptionalMinorArcs.PerronBilinearCoefficients
import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitScaleExponents

/-!
# Bilinear scale data from an active split-prime cell

An active cell has one selected/complementary product pair below the Perron cutoff. That
witness supplies all product-scale hypotheses needed by repaired Lemma 13.1.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- One canonical product cell contributes to the original strict cutoff. -/
def IsActiveSplitPrimeCell
    (length : Nat) {k : Nat} (a : Fin k → Real) (delta eta : Real)
    (I : Finset (Fin k)) (key : Nat × Nat) : Prop :=
  ∃ n ∈ splitProductCoordinateFiber length key.1,
    ∃ m ∈ splitProductCoordinateFiber length key.2,
      selectedProjectedPrimeWeightAtProduct
          (10 ^ length) a delta I n ≠ 0 ∧
        complementaryLastPrimeWeightAtProduct
          (10 ^ length) a delta eta I m ≠ 0 ∧
        n * m < 10 ^ length

theorem one_le_splitProductScaleAt (i : Nat) :
    1 ≤ splitProductScaleAt i := by
  unfold splitProductScaleAt
  exact_mod_cast one_le_pow₀ (show 1 ≤ 10 by norm_num)

/-- An active cell inherits the stronger product-scale bound `<100X`. -/
theorem activeSplitPrimeCell_scaleProduct_lt
    {length k : Nat} {a : Fin k → Real} {delta eta : Real}
    {I : Finset (Fin k)} {key : Nat × Nat}
    (hlength : 0 < length)
    (hactive : IsActiveSplitPrimeCell length a delta eta I key) :
    splitProductScaleAt key.1 * splitProductScaleAt key.2 <
      100 * (((10 ^ length : Nat) : Real)) := by
  rcases hactive with ⟨n, hn, m, hm, hnWeight, hmWeight, hnm⟩
  rw [splitProductScaleAt_eq_factorTenScale_of_mem hn,
    splitProductScaleAt_eq_factorTenScale_of_mem hm]
  exact activeSplitFactorTenScales_mul_lt
    hlength hnWeight hmWeight hnm

/--
Under either subset-sum alternative, one active cell scale is convenient for Lemma 13.1.
-/
theorem activeSplitPrimeCell_convenient_dichotomy
    {length k : Nat} {a : Fin k → Real} {delta mu eta : Real}
    {I : Finset (Fin k)} {key : Nat × Nat}
    (hlength : 0 < length) (hdelta : 0 ≤ delta)
    (hmargin : ((k + 1 : Nat) : Real) * delta +
      1 / (length : Real) ≤ mu)
    (ht : (∑ i ∈ I, a i) ∈
          Set.Icc (9 / 25 + mu) (17 / 40 - mu) ∨
        (∑ i ∈ I, a i) ∈
          Set.Icc (23 / 40 + mu) (16 / 25 - mu))
    (hactive : IsActiveSplitPrimeCell length a delta eta I key) :
    (((((10 ^ length : Nat) : Real) ^ (9 / 25 : Real)) ≤
        splitProductScaleAt key.1 ∧
      splitProductScaleAt key.1 ≤
        (((10 ^ length : Nat) : Real) ^ (17 / 40 : Real))) ∨
      ((((10 ^ length : Nat) : Real) ^ (9 / 25 : Real)) ≤
        splitProductScaleAt key.2 ∧
      splitProductScaleAt key.2 ≤
        (((10 ^ length : Nat) : Real) ^ (17 / 40 : Real)))) := by
  rcases hactive with ⟨n, hn, m, hm, hnWeight, hmWeight, hnm⟩
  have hresult := splitFactorTenScale_convenient_dichotomy
    hlength hdelta hmargin ht hnWeight hmWeight hnm
  simpa only [splitProductScaleAt_eq_factorTenScale_of_mem hn,
    splitProductScaleAt_eq_factorTenScale_of_mem hm] using hresult

/-- The active-cell scale product satisfies the weaker source-facing
`1000X` hypothesis of repaired Lemma 13.1. -/
theorem activeSplitPrimeCell_scaleProduct_le_thousand
    {length k : Nat} {a : Fin k → Real} {delta eta : Real}
    {I : Finset (Fin k)} {key : Nat × Nat}
    (hlength : 0 < length)
    (hactive : IsActiveSplitPrimeCell length a delta eta I key) :
    splitProductScaleAt key.1 * splitProductScaleAt key.2 ≤
      1000 * (((10 ^ length : Nat) : Real)) := by
  have hstrict := activeSplitPrimeCell_scaleProduct_lt hlength hactive
  have hX : (0 : Real) < (10 ^ length : Nat) := by positivity
  linarith

end

end PrimesRestrictedDigits
