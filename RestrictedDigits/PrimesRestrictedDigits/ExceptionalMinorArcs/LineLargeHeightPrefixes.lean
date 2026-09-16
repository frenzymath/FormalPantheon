import PrimesRestrictedDigits.ExceptionalMinorArcs.LineSmallHeightPrefixes
import Mathlib.Tactic.GCongr

/-!
# Outer key for the large primitive-height count

This reorders only the first cross-coefficient prefix in the large-height argument before
equation `(15.5)` of `MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 212--213. All later prefixes are
reused.
-/

namespace PrimesRestrictedDigits

/-- The three fields fixed before counting the affine `(b3,b4)` fiber. -/
@[ext]
structure LineLargeHeightKey (X : Nat) where
  /-- Unprimed second member. -/
  a2 : Fin X
  /-- Primed second member, used as the affine modulus. -/
  a2Prime : Fin X
  /-- Unprimed-member cross coefficient. -/
  b1 : Int
  deriving DecidableEq

/-- Project normalized data to the large-height outer key. -/
def lineLargeHeightKeyOfData {X : Nat}
    (data : LineNormalizedSecondMomentData X) : LineLargeHeightKey X :=
  { a2 := data.a2
    a2Prime := data.a2Prime
    b1 := (lineNormalizedCrossData data).b1 }

/-- Forget the remaining cross coefficients from the existing cross prefix. -/
def LineSmallHeightCrossFactor.toLineLargeHeightKey {X : Nat}
    (item : LineSmallHeightCrossFactor X) : LineLargeHeightKey X :=
  { a2 := item.a2
    a2Prime := item.a2Prime
    b1 := item.b1 }

@[simp]
theorem lineSmallHeightCrossFactorOfData_toLargeHeightKey {X : Nat}
    (data : LineNormalizedSecondMomentData X) :
    (lineSmallHeightCrossFactorOfData data).toLineLargeHeightKey =
      lineLargeHeightKeyOfData data :=
  rfl

/-- Outer-key image of one oriented normalized class. -/
noncomputable def lineLargeHeightKeyClass
    (length : Nat) (C D : Finset (Fin (10 ^ length))) (V : Real)
    (j : Fin (length + 1)) : Finset (LineLargeHeightKey (10 ^ length)) :=
  (orientedLineNormalizedSecondMomentClass length C D V j).image
    lineLargeHeightKeyOfData

/-- Ambient product box for the large-height outer key. -/
noncomputable def lineLargeHeightOuterKeyBox
    {X : Nat} (D : Finset (Fin X)) (W : Real) :
    Finset (LineLargeHeightKey X) :=
  (D.product (D.product (lineCoefficientBox W))).image fun item =>
    { a2 := item.1
      a2Prime := item.2.1
      b1 := item.2.2 }

/-- The outer key has at most two class factors and one cross-coefficient box. -/
theorem lineLargeHeightKeyClass_card_real_le
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V : Real)
    (j : Fin (length + 1)) (hV : 1 ≤ V) :
    ((lineLargeHeightKeyClass length C D V j).card : Real) ≤
      (D.card : Real) ^ 2 *
        (6 * ((10 ^ j.val : Nat) : Real) * V) := by
  classical
  let U : Real := ((10 ^ j.val : Nat) : Real)
  let W : Real := 2 * U * V
  let outer := lineLargeHeightOuterKeyBox D W
  have hU : 1 ≤ U := by
    dsimp only [U]
    rw [Nat.cast_pow]
    exact one_le_pow₀ (by norm_num)
  have hW : 1 ≤ W := by
    dsimp only [W]
    nlinarith [mul_le_mul hU hV (by norm_num : (0 : Real) ≤ 1)
      (zero_le_one.trans hU)]
  have hsubset : lineLargeHeightKeyClass length C D V j ⊆ outer := by
    intro key hkey
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hkey
    have hfull := (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
    have hvalid := mem_lineNormalizedSecondMomentClass_isValid hfull
    have hboxes :=
      mem_orientedLineNormalizedSecondMomentClass_cross_mem_boxes hdata hV
    apply Finset.mem_image.mpr
    refine ⟨(data.a2, (data.a2Prime,
      (lineNormalizedCrossData data).b1)), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨hvalid.a2_mem,
      Finset.mem_product.mpr ⟨hvalid.a2Prime_mem, hboxes.1⟩⟩
  have houter : (outer.card : Real) ≤
      (D.card : Real) ^ 2 * ((lineCoefficientBox W).card : Real) := by
    have hcard : outer.card ≤
        (D.product (D.product (lineCoefficientBox W))).card :=
      Finset.card_image_le
    have hcast : (outer.card : Real) ≤
        ((D.product (D.product (lineCoefficientBox W))).card : Real) := by
      exact_mod_cast hcard
    rw [Finset.product_eq_sprod, Finset.card_product,
      Finset.product_eq_sprod, Finset.card_product] at hcast
    push_cast at hcast
    calc
      (outer.card : Real) ≤
          (D.card : Real) *
            ((D.card : Real) * ((lineCoefficientBox W).card : Real)) := hcast
      _ = (D.card : Real) ^ 2 *
          ((lineCoefficientBox W).card : Real) := by ring
  have hbox : ((lineCoefficientBox W).card : Real) ≤ 6 * U * V := by
    calc
      ((lineCoefficientBox W).card : Real) ≤ 3 * W :=
        card_lineCoefficientBox_real_le hW
      _ = 6 * U * V := by simp only [W]; ring
  calc
    ((lineLargeHeightKeyClass length C D V j).card : Real) ≤
        (outer.card : Real) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ (D.card : Real) ^ 2 *
        ((lineCoefficientBox W).card : Real) := houter
    _ ≤ (D.card : Real) ^ 2 * (6 * U * V) := by gcongr
    _ = (D.card : Real) ^ 2 *
        (6 * ((10 ^ j.val : Nat) : Real) * V) := rfl

end PrimesRestrictedDigits
