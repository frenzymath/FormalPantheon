import BoundedGaps.Maynard.MaynardArithmeticBounds

/-!
# Cardinality bounds for Maynard divisor support

This module specializes the positive product-tuple envelope to the concrete
finite support in Maynard2013v3, Proposition `MainProp` (source lines
202--216).
-/

namespace BoundedGaps.Maynard

theorem maynardDivisorTupleSupport_subset_positiveProductTuples
    (H : Finset ℕ) (R W : ℕ) :
    maynardDivisorTupleSupport H R W ⊆ positiveProductTuples H R := by
  classical
  intro d hd
  have hmem := mem_maynardDivisorTupleSupport_iff.mp hd
  have hbox := mem_maynardDivisorTupleBox_iff.mp hmem.1
  rw [mem_positiveProductTuples_iff]
  exact ⟨fun h => Finset.mem_Icc.mpr ⟨(hbox h).1, (hbox h).2.le⟩,
    hmem.2.1.le⟩

theorem maynardDivisorTupleSupport_card_le_log
    (H : Finset ℕ) (R W : ℕ) :
    ((maynardDivisorTupleSupport H R W).card : ℝ) ≤
      (R : ℝ) * (1 + Real.log R) ^ Fintype.card H := by
  have hcard : (maynardDivisorTupleSupport H R W).card ≤
      (positiveProductTuples H R).card :=
    Finset.card_le_card
      (maynardDivisorTupleSupport_subset_positiveProductTuples H R W)
  have hcardReal : ((maynardDivisorTupleSupport H R W).card : ℝ) ≤
      ((positiveProductTuples H R).card : ℝ) := by
    exact_mod_cast hcard
  exact hcardReal.trans (card_positiveProductTuples_le_one_add_log H R)

end BoundedGaps.Maynard
