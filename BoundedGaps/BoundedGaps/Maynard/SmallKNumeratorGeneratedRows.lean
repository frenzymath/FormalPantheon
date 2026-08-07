import BoundedGaps.Maynard.SmallKNumeratorGeneratedCertificate

/-! # Chunked exact row evaluation for the scaled numerator table -/

namespace BoundedGaps.Maynard

def smallKNumeratorGeneratedRow (b : ℕ) : ℚ :=
  ∑ c ∈ Finset.range 11,
    (smallKNumeratorGeneratedCoefficientDigits.getD (b * 11 + c) 0 : ℚ) *
      smallKSimplexMoment104 b c * (105 : ℚ) /
        (smallKFaceScale : ℚ) ^ 2

def smallKNumeratorGeneratedRowIndex (offset : ℕ) (i : Fin 5)
    (h : offset + 5 ≤ 25) : Fin 25 :=
  ⟨offset + i.1, by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem smallK_numeratorGeneratedRows_0 (i : Fin 5) :
    smallKNumeratorGeneratedRow (smallKNumeratorGeneratedRowIndex 0 i (by omega)) =
      smallKNumeratorGeneratedRowValues.getD i.1 0 := by
  fin_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [smallKNumeratorGeneratedRow, smallKNumeratorGeneratedRowIndex,
        smallKNumeratorGeneratedCoefficientDigits, smallKSimplexMoment104,
        smallKG104, smallKFaceScale, smallKNumeratorGeneratedRowValues,
        Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem smallK_numeratorGeneratedRows_5 (i : Fin 5) :
    smallKNumeratorGeneratedRow (smallKNumeratorGeneratedRowIndex 5 i (by omega)) =
      smallKNumeratorGeneratedRowValues.getD (5 + i.1) 0 := by
  fin_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [smallKNumeratorGeneratedRow, smallKNumeratorGeneratedRowIndex,
        smallKNumeratorGeneratedCoefficientDigits, smallKSimplexMoment104,
        smallKG104, smallKFaceScale, smallKNumeratorGeneratedRowValues,
        Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem smallK_numeratorGeneratedRows_10 (i : Fin 5) :
    smallKNumeratorGeneratedRow (smallKNumeratorGeneratedRowIndex 10 i (by omega)) =
      smallKNumeratorGeneratedRowValues.getD (10 + i.1) 0 := by
  fin_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [smallKNumeratorGeneratedRow, smallKNumeratorGeneratedRowIndex,
        smallKNumeratorGeneratedCoefficientDigits, smallKSimplexMoment104,
        smallKG104, smallKFaceScale, smallKNumeratorGeneratedRowValues,
        Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem smallK_numeratorGeneratedRows_15 (i : Fin 5) :
    smallKNumeratorGeneratedRow (smallKNumeratorGeneratedRowIndex 15 i (by omega)) =
      smallKNumeratorGeneratedRowValues.getD (15 + i.1) 0 := by
  fin_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [smallKNumeratorGeneratedRow, smallKNumeratorGeneratedRowIndex,
        smallKNumeratorGeneratedCoefficientDigits, smallKSimplexMoment104,
        smallKG104, smallKFaceScale, smallKNumeratorGeneratedRowValues,
        Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem smallK_numeratorGeneratedRows_20 (i : Fin 5) :
    smallKNumeratorGeneratedRow (smallKNumeratorGeneratedRowIndex 20 i (by omega)) =
      smallKNumeratorGeneratedRowValues.getD (20 + i.1) 0 := by
  fin_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [smallKNumeratorGeneratedRow, smallKNumeratorGeneratedRowIndex,
        smallKNumeratorGeneratedCoefficientDigits, smallKSimplexMoment104,
        smallKG104, smallKFaceScale, smallKNumeratorGeneratedRowValues,
        Finset.sum_range_succ]

end BoundedGaps.Maynard
