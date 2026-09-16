import PrimesRestrictedDigits.MajorArcs.PartitionCardinality

/-!
# Real bounds for major-arc cardinalities

This converts the exact ceiling polynomials into the explicit real cubic and quadratic
estimates.
-/

namespace PrimesRestrictedDigits

private theorem majorArcCubicPolynomial_cast_le
    {Q : Real} (hQ : 1 <= Q) :
    ((Nat.ceil Q * (3 * Nat.ceil Q + 1) *
        (2 * Nat.ceil Q + 1) : Nat) : Real) <= 70 * Q ^ 3 := by
  have hQNonneg : (0 : Real) <= Q := by linarith
  have hceil : (Nat.ceil Q : Real) <= 2 * Q := by
    have hceilLt := Nat.ceil_lt_add_one hQNonneg
    linarith
  have hthree : 3 * (Nat.ceil Q : Real) + 1 <= 7 * Q := by
    linarith
  have htwo : 2 * (Nat.ceil Q : Real) + 1 <= 5 * Q := by
    linarith
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  calc
    (Nat.ceil Q : Real) * (3 * Nat.ceil Q + 1) *
        (2 * Nat.ceil Q + 1) <= (2 * Q) * (7 * Q) * (5 * Q) := by
      gcongr
    _ = 70 * Q ^ 3 := by ring

private theorem majorArcQuadraticPolynomial_cast_le
    {Q : Real} (hQ : 1 <= Q) :
    ((Nat.ceil Q * (3 * Nat.ceil Q + 1) : Nat) : Real) <=
      14 * Q ^ 2 := by
  have hQNonneg : (0 : Real) <= Q := by linarith
  have hceil : (Nat.ceil Q : Real) <= 2 * Q := by
    have hceilLt := Nat.ceil_lt_add_one hQNonneg
    linarith
  have hthree : 3 * (Nat.ceil Q : Real) + 1 <= 7 * Q := by
    linarith
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  calc
    (Nat.ceil Q : Real) * (3 * Nat.ceil Q + 1) <=
        (2 * Q) * (7 * Q) := by
      gcongr
    _ = 14 * Q ^ 2 := by ring

theorem majorArcRawFrequencies_card_real_le
    {X : Nat} {Q : Real} (hQ : 1 <= Q) (hQX : Q <= (X : Real)) :
    ((majorArcRawFrequencies X Q).card : Real) <= 70 * Q ^ 3 := by
  have hXReal : (0 : Real) < X := by
    exact zero_lt_one.trans_le (hQ.trans hQX)
  have hX : 0 < X := Nat.cast_pos.mp hXReal
  exact (Nat.cast_le.mpr (majorArcRawFrequencies_card_le hX hQX)).trans
    (majorArcCubicPolynomial_cast_le hQ)

theorem majorArcClassOneFrequencies_card_real_le
    {X : Nat} {Q : Real} (hQ : 1 <= Q) (hQX : Q <= (X : Real)) :
    ((majorArcClassOneFrequencies X Q).card : Real) <= 70 * Q ^ 3 := by
  have hsubset := Finset.card_le_card
    (majorArcClassOneFrequencies_subset_raw X Q)
  exact (Nat.cast_le.mpr hsubset).trans
    (majorArcRawFrequencies_card_real_le hQ hQX)

theorem majorArcClassTwoFrequencies_card_real_le
    {X : Nat} {Q : Real} (hQ : 1 <= Q) (hQX : Q <= (X : Real)) :
    ((majorArcClassTwoFrequencies X Q).card : Real) <= 70 * Q ^ 3 := by
  have hsubset := Finset.card_le_card
    (majorArcClassTwoFrequencies_subset_raw X Q)
  exact (Nat.cast_le.mpr hsubset).trans
    (majorArcRawFrequencies_card_real_le hQ hQX)

theorem majorArcClassThreeFrequencies_card_real_le
    {X : Nat} {Q : Real} (hQ : 1 <= Q) (hQX : Q <= (X : Real)) :
    ((majorArcClassThreeFrequencies X Q).card : Real) <= 14 * Q ^ 2 := by
  have hXReal : (0 : Real) < X := by
    exact zero_lt_one.trans_le (hQ.trans hQX)
  have hX : 0 < X := Nat.cast_pos.mp hXReal
  exact (Nat.cast_le.mpr (majorArcClassThreeFrequencies_card_le hX hQX)).trans
    (majorArcQuadraticPolynomial_cast_le hQ)

end PrimesRestrictedDigits
