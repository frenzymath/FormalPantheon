import PrimesRestrictedDigits.Fourier.Moment235CachedPairedEdge
import PrimesRestrictedDigits.Fourier.Moment235CertificateMinimum
import PrimesRestrictedDigits.Fourier.DigitWindowEncoding
import PrimesRestrictedDigits.Fourier.Moment235PairedSymmetry
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.IrreducibleDef

/-!
# Indexed rows for the exact fractional-moment certificates

Each proposition is a ten-branch arbitrary-precision natural inequality. The
finite checker modules prove these propositions by ordinary kernel reduction.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

def moment235IndexedRowSum (a : Fin 5) (future : Fin 10000) : Nat :=
  ∑ first : Fin 10,
    moment235PairedPoweredNumerator moment235CertificateDenominator
        (moment235RepresentativeDigit a)
        (10000 * first.val + future.val) *
      moment235VectorNumerator a
        (moment235IncomingPreviousIndex first future)

irreducible_def moment235IndexedRow (a : Fin 5) (future : Fin 10000) : Prop :=
  moment235CertificateGrowthDenominator * moment235IndexedRowSum a future <=
    moment235CertificateDenominator *
      moment235CertificateGrowthNumerator *
        moment235VectorNumerator a future

def moment235ReflectedFuture (future : Fin 10000) : Fin 10000 :=
  ⟨9999 - future.val, by omega⟩

private theorem moment235IncomingPreviousIndex_rev_reflect
    (first : Fin 10) (future : Fin 10000) :
    moment235IncomingPreviousIndex first.rev
        (moment235ReflectedFuture future) =
      ⟨9999 - (moment235IncomingPreviousIndex first future).val, by omega⟩ := by
  apply Fin.ext
  unfold moment235IncomingPreviousIndex moment235ReflectedFuture
  dsimp only [Fin.val_mk]
  rw [Fin.val_rev]
  have hfirst := first.isLt
  have hfuture := future.isLt
  omega

private theorem moment235IncomingEdge_rev_reflect
    (first : Fin 10) (future : Fin 10000) :
    10000 * first.rev.val + (moment235ReflectedFuture future).val =
      99999 - (10000 * first.val + future.val) := by
  rw [Fin.val_rev]
  unfold moment235ReflectedFuture
  dsimp only [Fin.val_mk]
  have hfirst := first.isLt
  have hfuture := future.isLt
  omega

private theorem moment235IndexedRowTerm_rev_reflect
    (a : Fin 5) (first : Fin 10) (future : Fin 10000) :
    moment235PairedPoweredNumerator moment235CertificateDenominator
          (moment235RepresentativeDigit a)
          (10000 * first.rev.val + (moment235ReflectedFuture future).val) *
        moment235VectorNumerator a
          (moment235IncomingPreviousIndex first.rev
            (moment235ReflectedFuture future)) =
      moment235PairedPoweredNumerator moment235CertificateDenominator
          (moment235RepresentativeDigit a)
          (10000 * first.val + future.val) *
        moment235VectorNumerator a
          (moment235IncomingPreviousIndex first future) := by
  rw [moment235IncomingEdge_rev_reflect,
    moment235PairedPoweredNumerator_reflect,
    moment235IncomingPreviousIndex_rev_reflect,
    moment235VectorNumerator_reflect]
  have hfirst := first.isLt
  have hfuture := future.isLt
  omega

theorem moment235IndexedRowSum_reflect
    (a : Fin 5) (future : Fin 10000) :
    moment235IndexedRowSum a (moment235ReflectedFuture future) =
      moment235IndexedRowSum a future := by
  rw [moment235IndexedRowSum, ← Equiv.sum_comp Fin.revPerm]
  simp only [Fin.revPerm_apply]
  apply Finset.sum_congr rfl
  intro first hfirst
  exact moment235IndexedRowTerm_rev_reflect a first future

theorem moment235IndexedRow_reflect
    (a : Fin 5) (future : Fin 10000) :
    moment235IndexedRow a (moment235ReflectedFuture future) ↔
      moment235IndexedRow a future := by
  rw [moment235IndexedRow_def, moment235IndexedRow_def]
  rw [moment235IndexedRowSum_reflect]
  unfold moment235ReflectedFuture
  rw [moment235VectorNumerator_reflect]

theorem moment235IndexedRow_of_lowerHalf
    (a : Fin 5)
    (hlower : forall future : Fin 5000,
      moment235IndexedRow a ⟨future.val, lt_trans future.isLt (by omega)⟩) :
    forall future : Fin 10000, moment235IndexedRow a future := by
  intro future
  by_cases hfuture : future.val < 5000
  · exact hlower ⟨future.val, hfuture⟩
  · have hreflected : (moment235ReflectedFuture future).val < 5000 := by
      unfold moment235ReflectedFuture
      dsimp only [Fin.val_mk]
      have hlt := future.isLt
      omega
    exact (moment235IndexedRow_reflect a future).mp
      (hlower ⟨(moment235ReflectedFuture future).val, hreflected⟩)

end PrimesRestrictedDigits
