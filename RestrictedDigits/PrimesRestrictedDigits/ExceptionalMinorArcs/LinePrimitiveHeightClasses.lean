import PrimesRestrictedDigits.ExceptionalMinorArcs.FactorTenLocalization
import PrimesRestrictedDigits.ExceptionalMinorArcs.LineSecondMomentCarrier
import PrimesRestrictedDigits.ExceptionalMinorArcs.LineSignedGcdCrossRelation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Primitive first-coefficient height classes

This implements the corrected factor-ten localization following `N_2` in
`MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 211--212. The classes retain the top
decimal bin and give the valid strict range `d * V1 < 10 * V`.
-/

namespace PrimesRestrictedDigits

/-- Canonical signed primitive sup height of a pair of relation witnesses. -/
def lineSecondMomentPrimitiveHeight {X : Nat}
    (pair : LowHeightPlaneWitness X × LowHeightPlaneWitness X) : Nat :=
  linePrimitiveFirstCoefficientHeight
    (pair.1.v 0) (pair.2.v 0)

/-- Witness pairs with one prescribed factor-ten primitive-height index. -/
noncomputable def linePrimitiveHeightWitnessClass
    (length : Nat) (C D : Finset (Fin (10 ^ length))) (V : Real)
    (j : Fin (length + 1)) :
    Finset (LowHeightPlaneWitness (10 ^ length) ×
      LowHeightPlaneWitness (10 ^ length)) := by
  classical
  exact (lineSecondMomentWitnessPairs C D V).filter fun pair =>
    Nat.clog 10 (lineSecondMomentPrimitiveHeight pair) = j.val

@[simp]
theorem mem_linePrimitiveHeightWitnessClass
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {pair : LowHeightPlaneWitness (10 ^ length) ×
      LowHeightPlaneWitness (10 ^ length)} :
    pair ∈ linePrimitiveHeightWitnessClass length C D V j ↔
      And (pair ∈ lineSecondMomentWitnessPairs C D V)
        (Nat.clog 10 (lineSecondMomentPrimitiveHeight pair) = j.val) := by
  classical
  simp [linePrimitiveHeightWitnessClass]

theorem lineSecondMomentPrimitiveHeight_pos
    {X : Nat} {C D : Finset (Fin X)} {V : Real}
    {pair : LowHeightPlaneWitness X × LowHeightPlaneWitness X}
    (hpair : pair ∈ lineSecondMomentWitnessPairs C D V) :
    0 < lineSecondMomentPrimitiveHeight pair := by
  have hp := mem_lineSecondMomentWitnessPairs.mp hpair
  have hw := mem_positiveAllNonzeroPlaneWitnesses.mp hp.1
  exact linePrimitiveFirstCoefficientHeight_pos (hw.2.2.1 0)

/-- The positive gcd times primitive height is bounded by the original
coefficient height. -/
theorem lineSecondMomentGcdMulPrimitiveHeight_real_le
    {X : Nat} {C D : Finset (Fin X)} {V : Real}
    {pair : LowHeightPlaneWitness X × LowHeightPlaneWitness X}
    (hpair : pair ∈ lineSecondMomentWitnessPairs C D V) :
    (Int.gcd (pair.1.v 0) (pair.2.v 0) : Real) *
        (lineSecondMomentPrimitiveHeight pair : Real) ≤ V := by
  have hp := mem_lineSecondMomentWitnessPairs.mp hpair
  have hw := mem_positiveAllNonzeroPlaneWitnesses.mp hp.1
  have hw' := mem_positiveAllNonzeroPlaneWitnesses.mp hp.2.1
  rw [← Nat.cast_mul, lineSecondMomentPrimitiveHeight,
    gcd_mul_linePrimitiveFirstCoefficientHeight, Nat.cast_max]
  apply max_le
  · rw [Nat.cast_natAbs, Int.cast_abs]
    exact hw.2.1.2.1 0
  · rw [Nat.cast_natAbs, Int.cast_abs]
    exact hw'.2.1.2.1 0

theorem lineSecondMomentPrimitiveHeight_real_le
    {X : Nat} {C D : Finset (Fin X)} {V : Real}
    {pair : LowHeightPlaneWitness X × LowHeightPlaneWitness X}
    (hpair : pair ∈ lineSecondMomentWitnessPairs C D V) :
    (lineSecondMomentPrimitiveHeight pair : Real) ≤ V := by
  have hp := mem_lineSecondMomentWitnessPairs.mp hpair
  have hw := mem_positiveAllNonzeroPlaneWitnesses.mp hp.1
  have hd : 0 < Int.gcd (pair.1.v 0) (pair.2.v 0) :=
    linePrimitiveFirstCoefficients_gcd_pos (hw.2.2.1 0)
  have hnat : lineSecondMomentPrimitiveHeight pair ≤
      Int.gcd (pair.1.v 0) (pair.2.v 0) *
        lineSecondMomentPrimitiveHeight pair :=
    Nat.le_mul_of_pos_left _ hd
  calc
    (lineSecondMomentPrimitiveHeight pair : Real) ≤
        ((Int.gcd (pair.1.v 0) (pair.2.v 0) *
          lineSecondMomentPrimitiveHeight pair : Nat) : Real) := by
      exact_mod_cast hnat
    _ = (Int.gcd (pair.1.v 0) (pair.2.v 0) : Real) *
        (lineSecondMomentPrimitiveHeight pair : Real) := by
      rw [Nat.cast_mul]
    _ ≤ V := lineSecondMomentGcdMulPrimitiveHeight_real_le hpair

theorem lineSecondMomentPrimitiveHeight_lt_scale
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {pair : LowHeightPlaneWitness (10 ^ length) ×
      LowHeightPlaneWitness (10 ^ length)}
    (hVX : V < ((10 ^ length : Nat) : Real))
    (hpair : pair ∈ lineSecondMomentWitnessPairs C D V) :
    lineSecondMomentPrimitiveHeight pair < 10 ^ length := by
  have hreal : (lineSecondMomentPrimitiveHeight pair : Real) <
      ((10 ^ length : Nat) : Real) :=
    (lineSecondMomentPrimitiveHeight_real_le hpair).trans_lt hVX
  exact_mod_cast hreal

theorem mem_linePrimitiveHeightWitnessClass_index
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {pair : LowHeightPlaneWitness (10 ^ length) ×
      LowHeightPlaneWitness (10 ^ length)}
    (hVX : V < ((10 ^ length : Nat) : Real))
    (hpair : pair ∈ lineSecondMomentWitnessPairs C D V) :
    pair ∈ linePrimitiveHeightWitnessClass length C D V
      (decimalFactorTenIndex length
        (lineSecondMomentPrimitiveHeight pair)
        (lineSecondMomentPrimitiveHeight_lt_scale hVX hpair)) := by
  apply mem_linePrimitiveHeightWitnessClass.mpr
  exact ⟨hpair, rfl⟩

theorem biUnion_linePrimitiveHeightWitnessClass_eq
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V : Real)
    (hVX : V < ((10 ^ length : Nat) : Real)) :
    Finset.univ.biUnion
        (linePrimitiveHeightWitnessClass length C D V) =
      lineSecondMomentWitnessPairs C D V := by
  classical
  ext pair
  constructor
  · intro hpair
    obtain ⟨j, _hj, hpj⟩ := Finset.mem_biUnion.mp hpair
    exact (mem_linePrimitiveHeightWitnessClass.mp hpj).1
  · intro hpair
    apply Finset.mem_biUnion.mpr
    refine ⟨decimalFactorTenIndex length
      (lineSecondMomentPrimitiveHeight pair)
      (lineSecondMomentPrimitiveHeight_lt_scale hVX hpair), by simp, ?_⟩
    exact mem_linePrimitiveHeightWitnessClass_index hVX hpair

theorem disjoint_linePrimitiveHeightWitnessClass_of_ne
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V : Real)
    {j k : Fin (length + 1)} (hjk : j ≠ k) :
    Disjoint (linePrimitiveHeightWitnessClass length C D V j)
      (linePrimitiveHeightWitnessClass length C D V k) := by
  classical
  rw [Finset.disjoint_left]
  intro pair hpj hpk
  have hj := (mem_linePrimitiveHeightWitnessClass.mp hpj).2
  have hk := (mem_linePrimitiveHeightWitnessClass.mp hpk).2
  apply hjk
  apply Fin.ext
  exact hj.symm.trans hk

theorem pairwiseDisjoint_linePrimitiveHeightWitnessClass
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V : Real) :
    ((Finset.univ : Finset (Fin (length + 1))) :
      Set (Fin (length + 1))).PairwiseDisjoint
        (linePrimitiveHeightWitnessClass length C D V) := by
  intro j _ k _ hjk
  exact disjoint_linePrimitiveHeightWitnessClass_of_ne C D V hjk

theorem card_lineSecondMomentWitnessPairs_eq_sum_heightClasses
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V : Real)
    (hVX : V < ((10 ^ length : Nat) : Real)) :
    (lineSecondMomentWitnessPairs C D V).card =
      ∑ j : Fin (length + 1),
        (linePrimitiveHeightWitnessClass length C D V j).card := by
  classical
  calc
    (lineSecondMomentWitnessPairs C D V).card =
        (Finset.univ.biUnion
          (linePrimitiveHeightWitnessClass length C D V)).card := by
      rw [biUnion_linePrimitiveHeightWitnessClass_eq C D V hVX]
    _ = ∑ j ∈ (Finset.univ : Finset (Fin (length + 1))),
        (linePrimitiveHeightWitnessClass length C D V j).card :=
      Finset.card_biUnion
        (pairwiseDisjoint_linePrimitiveHeightWitnessClass C D V)
    _ = ∑ j : Fin (length + 1),
        (linePrimitiveHeightWitnessClass length C D V j).card := by
      simp

theorem mem_linePrimitiveHeightWitnessClass_band
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {pair : LowHeightPlaneWitness (10 ^ length) ×
      LowHeightPlaneWitness (10 ^ length)}
    (hpair : pair ∈ linePrimitiveHeightWitnessClass length C D V j) :
    And (((10 ^ j.val : Nat) : Real) / 10 <
        (lineSecondMomentPrimitiveHeight pair : Real))
      (And ((lineSecondMomentPrimitiveHeight pair : Real) ≤
          ((10 ^ j.val : Nat) : Real))
        (10 ^ j.val ≤ 10 ^ length)) := by
  have hp := mem_linePrimitiveHeightWitnessClass.mp hpair
  have hband := factorTenScale_band
    (lineSecondMomentPrimitiveHeight pair)
    (lineSecondMomentPrimitiveHeight_pos hp.1)
  have hscale : factorTenScale (lineSecondMomentPrimitiveHeight pair) =
      10 ^ j.val := by
    simp [factorTenScale, factorTenIndex, hp.2]
  rw [hscale] at hband
  exact ⟨hband.1, hband.2,
    Nat.pow_le_pow_right (by norm_num) j.is_le⟩

theorem mem_linePrimitiveHeightWitnessClass_primitive_spec
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {pair : LowHeightPlaneWitness (10 ^ length) ×
      LowHeightPlaneWitness (10 ^ length)}
    (hpair : pair ∈ linePrimitiveHeightWitnessClass length C D V j) :
    let primitive := linePrimitiveFirstCoefficients
      (pair.1.v 0) (pair.2.v 0)
    let d := Int.gcd (pair.1.v 0) (pair.2.v 0)
    And (primitive.1 ≠ 0) (And (primitive.2 ≠ 0)
      (And (Int.gcd primitive.1 primitive.2 = 1)
        (And ((d : Int) * primitive.1 = pair.1.v 0)
          (And ((d : Int) * primitive.2 = pair.2.v 0)
            (And (abs ((primitive.1 : Int) : Real) ≤
                (lineSecondMomentPrimitiveHeight pair : Real))
              (abs ((primitive.2 : Int) : Real) ≤
                (lineSecondMomentPrimitiveHeight pair : Real))))))) := by
  have hp := (mem_linePrimitiveHeightWitnessClass.mp hpair).1
  have hpairData := mem_lineSecondMomentWitnessPairs.mp hp
  have hw := mem_positiveAllNonzeroPlaneWitnesses.mp hpairData.1
  have hw' := mem_positiveAllNonzeroPlaneWitnesses.mp hpairData.2.1
  dsimp only
  exact ⟨linePrimitiveFirstCoefficients_fst_ne_zero (hw.2.2.1 0),
    linePrimitiveFirstCoefficients_snd_ne_zero (hw'.2.2.1 0),
    linePrimitiveFirstCoefficients_gcd_eq_one (hw.2.2.1 0),
    gcd_mul_linePrimitiveFirstCoefficients_fst _ _,
    gcd_mul_linePrimitiveFirstCoefficients_snd _ _,
    linePrimitiveFirstCoefficients_fst_abs_le_height _ _,
    linePrimitiveFirstCoefficients_snd_abs_le_height _ _⟩

theorem mem_linePrimitiveHeightWitnessClass_gcd_scale_lt
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {pair : LowHeightPlaneWitness (10 ^ length) ×
      LowHeightPlaneWitness (10 ^ length)}
    (hpair : pair ∈ linePrimitiveHeightWitnessClass length C D V j) :
    (Int.gcd (pair.1.v 0) (pair.2.v 0) : Real) *
        ((10 ^ j.val : Nat) : Real) < 10 * V := by
  have hp := (mem_linePrimitiveHeightWitnessClass.mp hpair).1
  have hpairData := mem_lineSecondMomentWitnessPairs.mp hp
  have hw := mem_positiveAllNonzeroPlaneWitnesses.mp hpairData.1
  have hdNat : 0 < Int.gcd (pair.1.v 0) (pair.2.v 0) :=
    linePrimitiveFirstCoefficients_gcd_pos (hw.2.2.1 0)
  have hd : (0 : Real) < Int.gcd (pair.1.v 0) (pair.2.v 0) := by
    exact_mod_cast hdNat
  have hband := mem_linePrimitiveHeightWitnessClass_band hpair
  have hscale : ((10 ^ j.val : Nat) : Real) <
      10 * (lineSecondMomentPrimitiveHeight pair : Real) := by
    linarith
  calc
    (Int.gcd (pair.1.v 0) (pair.2.v 0) : Real) *
        ((10 ^ j.val : Nat) : Real) <
        (Int.gcd (pair.1.v 0) (pair.2.v 0) : Real) *
          (10 * (lineSecondMomentPrimitiveHeight pair : Real)) :=
      mul_lt_mul_of_pos_left hscale hd
    _ = 10 * ((Int.gcd (pair.1.v 0) (pair.2.v 0) : Real) *
        (lineSecondMomentPrimitiveHeight pair : Real)) := by ring
    _ ≤ 10 * V := by
      exact mul_le_mul_of_nonneg_left
        (lineSecondMomentGcdMulPrimitiveHeight_real_le hp) (by norm_num)

end PrimesRestrictedDigits
