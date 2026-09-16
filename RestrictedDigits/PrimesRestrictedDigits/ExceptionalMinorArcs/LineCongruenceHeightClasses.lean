import PrimesRestrictedDigits.ExceptionalMinorArcs.FactorTenLocalization
import PrimesRestrictedDigits.ExceptionalMinorArcs.LineCongruenceMinimum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Prod

/-!
# Finite source congruence height classes

This is the source-facing two-parameter factor-ten partition `C(A,M)` from
`MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 211--212, after the source's separate removal of
zero. Its height coordinate uses the repaired sup minimum, rather than the paper's Euclidean
minimum.
-/

namespace PrimesRestrictedDigits

/-- All modulus/minimum factor-ten index pairs at decimal length `length`. -/
def decimalFactorTenIndexPairs (length : Nat) :
    Finset (Prod (Fin (length + 1)) (Fin (length + 1))) :=
  Finset.univ.product Finset.univ

@[simp]
theorem card_decimalFactorTenIndexPairs (length : Nat) :
    (decimalFactorTenIndexPairs length).card = (length + 1) ^ 2 := by
  simp [decimalFactorTenIndexPairs, pow_two]

/-- The positive members of `C` with prescribed modulus and minimum bands. -/
noncomputable def lineCongruenceHeightClass
    (length : Nat) (C : Finset (Fin (10 ^ length)))
    (j : Prod (Fin (length + 1)) (Fin (length + 1))) :
    Finset (Fin (10 ^ length)) := by
  classical
  exact C.filter fun a =>
    And (0 < a.val)
      (And (Nat.clog 10 a.val = j.1.val)
        (Nat.clog 10 (lineCongruenceMinimum (10 ^ length) a.val) =
          j.2.val))

@[simp]
theorem mem_lineCongruenceHeightClass
    {length : Nat} {C : Finset (Fin (10 ^ length))}
    {j : Prod (Fin (length + 1)) (Fin (length + 1))}
    {a : Fin (10 ^ length)} :
    a ∈ lineCongruenceHeightClass length C j ↔
      And (a ∈ C)
        (And (0 < a.val)
          (And (Nat.clog 10 a.val = j.1.val)
            (Nat.clog 10
              (lineCongruenceMinimum (10 ^ length) a.val) = j.2.val))) := by
  classical
  simp [lineCongruenceHeightClass]

/-- The canonical pair of source class indices for a positive member. -/
noncomputable def lineCongruenceHeightClassIndex
    (length : Nat) (a : Fin (10 ^ length)) (ha : 0 < a.val) :
    Prod (Fin (length + 1)) (Fin (length + 1)) :=
  (decimalFactorTenIndex length a.val a.isLt,
    decimalFactorTenIndex length
      (lineCongruenceMinimum (10 ^ length) a.val)
      (lineCongruenceMinimum_lt_scale
        (10 ^ length) a.val ha a.isLt))

theorem mem_lineCongruenceHeightClass_index
    {length : Nat} {C : Finset (Fin (10 ^ length))}
    {a : Fin (10 ^ length)} (haC : a ∈ C) (ha : 0 < a.val) :
    a ∈ lineCongruenceHeightClass length C
      (lineCongruenceHeightClassIndex length a ha) := by
  classical
  simp [lineCongruenceHeightClassIndex, haC, ha]

theorem mem_biUnion_lineCongruenceHeightClass
    {length : Nat} {C : Finset (Fin (10 ^ length))}
    {a : Fin (10 ^ length)} :
    a ∈ (decimalFactorTenIndexPairs length).biUnion
        (lineCongruenceHeightClass length C) ↔
      And (a ∈ C) (0 < a.val) := by
  classical
  constructor
  · intro ha
    obtain ⟨j, _hj, haj⟩ := Finset.mem_biUnion.mp ha
    have hdata := mem_lineCongruenceHeightClass.mp haj
    exact ⟨hdata.1, hdata.2.1⟩
  · rintro ⟨haC, ha⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨lineCongruenceHeightClassIndex length a ha, ?_, ?_⟩
    · simp [decimalFactorTenIndexPairs]
    · exact mem_lineCongruenceHeightClass_index haC ha

/-- The class union is exactly the positive part of `C`. -/
theorem biUnion_lineCongruenceHeightClass_eq_filter
    (length : Nat) (C : Finset (Fin (10 ^ length))) :
    (decimalFactorTenIndexPairs length).biUnion
        (lineCongruenceHeightClass length C) =
      C.filter fun a => 0 < a.val := by
  classical
  ext a
  rw [mem_biUnion_lineCongruenceHeightClass]
  simp

theorem disjoint_lineCongruenceHeightClass_of_ne
    {length : Nat} (C : Finset (Fin (10 ^ length)))
    {j k : Prod (Fin (length + 1)) (Fin (length + 1))}
    (hjk : Not (j = k)) :
    Disjoint (lineCongruenceHeightClass length C j)
      (lineCongruenceHeightClass length C k) := by
  classical
  rw [Finset.disjoint_left]
  intro a haj hak
  have hj := mem_lineCongruenceHeightClass.mp haj
  have hk := mem_lineCongruenceHeightClass.mp hak
  apply hjk
  apply Prod.ext
  · apply Fin.ext
    exact hj.2.2.1.symm.trans hk.2.2.1
  · apply Fin.ext
    exact hj.2.2.2.symm.trans hk.2.2.2

theorem mem_lineCongruenceHeightClass_modulus_band
    {length : Nat} {C : Finset (Fin (10 ^ length))}
    {j : Prod (Fin (length + 1)) (Fin (length + 1))}
    {a : Fin (10 ^ length)}
    (ha : a ∈ lineCongruenceHeightClass length C j) :
    And (((10 ^ j.1.val : Nat) : Real) / 10 < (a.val : Real))
      (And ((a.val : Real) <= ((10 ^ j.1.val : Nat) : Real))
        (10 ^ j.1.val <= 10 ^ length)) := by
  have hdata := mem_lineCongruenceHeightClass.mp ha
  have hband := factorTenScale_band a.val hdata.2.1
  have hscale : factorTenScale a.val = 10 ^ j.1.val := by
    simp [factorTenScale, factorTenIndex, hdata.2.2.1]
  rw [hscale] at hband
  exact ⟨hband.1, hband.2,
    Nat.pow_le_pow_right (by norm_num) j.1.is_le⟩

theorem mem_lineCongruenceHeightClass_minimum_band
    {length : Nat} {C : Finset (Fin (10 ^ length))}
    {j : Prod (Fin (length + 1)) (Fin (length + 1))}
    {a : Fin (10 ^ length)}
    (ha : a ∈ lineCongruenceHeightClass length C j) :
    And (((10 ^ j.2.val : Nat) : Real) / 10 <
        (lineCongruenceMinimum (10 ^ length) a.val : Real))
      (And
        ((lineCongruenceMinimum (10 ^ length) a.val : Real) <=
          ((10 ^ j.2.val : Nat) : Real))
        (10 ^ j.2.val <= 10 ^ length)) := by
  have hdata := mem_lineCongruenceHeightClass.mp ha
  have hband := factorTenScale_band
    (lineCongruenceMinimum (10 ^ length) a.val)
    (lineCongruenceMinimum_pos (10 ^ length) a.val)
  have hscale :
      factorTenScale (lineCongruenceMinimum (10 ^ length) a.val) =
        10 ^ j.2.val := by
    simp [factorTenScale, factorTenIndex, hdata.2.2.2]
  rw [hscale] at hband
  exact ⟨hband.1, hband.2,
    Nat.pow_le_pow_right (by norm_num) j.2.is_le⟩

end PrimesRestrictedDigits
