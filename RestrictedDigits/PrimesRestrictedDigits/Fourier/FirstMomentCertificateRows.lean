import PrimesRestrictedDigits.Fourier.FirstMomentCachedEdge
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateData
import PrimesRestrictedDigits.Fourier.DigitWindowEncoding
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.IrreducibleDef

/-!
# Indexed rows for the exact first-moment certificates

Each proposition is a ten-branch natural inequality. Reflection of the
25,000 lower-half rows supplies the other 25,000 representative rows.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

/-- The unscaled incoming weighted sum in one indexed certificate row. -/
def firstMomentIndexedRowSum (a : Fin 5) (future : Fin 10000) : Nat :=
  ∑ first : Fin 10,
    firstMomentPairedPoweredNumerator firstMomentCertificateDenominator
        (firstMomentRepresentativeDigit a)
        (10000 * first.val + future.val) *
      firstMomentVectorNumerator a
        (firstMomentIncomingPreviousIndex first future)

/-- Exact natural subeigenvector inequality for one representative and future
state. The definition is irreducible outside explicit checker proofs. -/
irreducible_def firstMomentIndexedRow (a : Fin 5) (future : Fin 10000) : Prop :=
  firstMomentCertificateGrowthDenominator *
      firstMomentIndexedRowSum a future <=
    firstMomentCertificateDenominator *
      firstMomentCertificateGrowthNumerator *
        firstMomentVectorNumerator a future

/-- Reflection of a four-digit decimal state about `9999`. -/
def firstMomentReflectedFuture (future : Fin 10000) : Fin 10000 :=
  ⟨9999 - future.val, by omega⟩

private theorem firstMomentIncomingPreviousIndex_rev_reflect
    (first : Fin 10) (future : Fin 10000) :
    firstMomentIncomingPreviousIndex first.rev
        (firstMomentReflectedFuture future) =
      ⟨9999 - (firstMomentIncomingPreviousIndex first future).val,
        by omega⟩ := by
  apply Fin.ext
  unfold firstMomentIncomingPreviousIndex firstMomentReflectedFuture
  dsimp only [Fin.val_mk]
  rw [Fin.val_rev]
  have hfirst := first.isLt
  have hfuture := future.isLt
  omega

private theorem firstMomentIncomingEdge_rev_reflect
    (first : Fin 10) (future : Fin 10000) :
    10000 * first.rev.val + (firstMomentReflectedFuture future).val =
      99999 - (10000 * first.val + future.val) := by
  rw [Fin.val_rev]
  unfold firstMomentReflectedFuture
  dsimp only [Fin.val_mk]
  have hfirst := first.isLt
  have hfuture := future.isLt
  omega

private theorem firstMomentIndexedRowTerm_rev_reflect
    (a : Fin 5) (first : Fin 10) (future : Fin 10000) :
    firstMomentPairedPoweredNumerator firstMomentCertificateDenominator
          (firstMomentRepresentativeDigit a)
          (10000 * first.rev.val + (firstMomentReflectedFuture future).val) *
        firstMomentVectorNumerator a
          (firstMomentIncomingPreviousIndex first.rev
            (firstMomentReflectedFuture future)) =
      firstMomentPairedPoweredNumerator firstMomentCertificateDenominator
          (firstMomentRepresentativeDigit a)
          (10000 * first.val + future.val) *
        firstMomentVectorNumerator a
          (firstMomentIncomingPreviousIndex first future) := by
  rw [firstMomentIncomingEdge_rev_reflect,
    firstMomentPairedPoweredNumerator_reflect,
    firstMomentIncomingPreviousIndex_rev_reflect,
    firstMomentVectorNumerator_reflect]
  have hfirst := first.isLt
  have hfuture := future.isLt
  omega

theorem firstMomentIndexedRowSum_reflect
    (a : Fin 5) (future : Fin 10000) :
    firstMomentIndexedRowSum a (firstMomentReflectedFuture future) =
      firstMomentIndexedRowSum a future := by
  rw [firstMomentIndexedRowSum, ← Equiv.sum_comp Fin.revPerm]
  simp only [Fin.revPerm_apply]
  apply Finset.sum_congr rfl
  intro first hfirst
  exact firstMomentIndexedRowTerm_rev_reflect a first future

theorem firstMomentIndexedRow_reflect
    (a : Fin 5) (future : Fin 10000) :
    firstMomentIndexedRow a (firstMomentReflectedFuture future) ↔
      firstMomentIndexedRow a future := by
  rw [firstMomentIndexedRow_def, firstMomentIndexedRow_def]
  rw [firstMomentIndexedRowSum_reflect]
  unfold firstMomentReflectedFuture
  rw [firstMomentVectorNumerator_reflect]

theorem firstMomentIndexedRow_of_lowerHalf
    (a : Fin 5)
    (hlower : forall future : Fin 5000,
      firstMomentIndexedRow a
        ⟨future.val, lt_trans future.isLt (by omega)⟩) :
    forall future : Fin 10000, firstMomentIndexedRow a future := by
  intro future
  by_cases hfuture : future.val < 5000
  · exact hlower ⟨future.val, hfuture⟩
  · have hreflected : (firstMomentReflectedFuture future).val < 5000 := by
      unfold firstMomentReflectedFuture
      dsimp only [Fin.val_mk]
      have hlt := future.isLt
      omega
    exact (firstMomentIndexedRow_reflect a future).mp
      (hlower ⟨(firstMomentReflectedFuture future).val, hreflected⟩)

end PrimesRestrictedDigits
