import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateCells
import Mathlib.Algebra.BigOperators.Fin
/-! # SectionSixFirstHighCentralSmallQuadrupleCertificateShardBase -/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-! Each 64-cell sum is partitioned into eight 8-cell sums. -/

def sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero
    (shard : Fin 32) : Real :=
  ∑ j : Fin 32,
    (sectionSixFirstHighCentralSmallQuadrupleCertificateCell
      (shard, Fin.castAdd 32 j)).weight

def sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne
    (shard : Fin 32) : Real :=
  ∑ j : Fin 32,
    (sectionSixFirstHighCentralSmallQuadrupleCertificateCell
      (shard, Fin.natAdd 32 j)).weight

def sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0
    (shard : Fin 32) : Real :=
  ∑ j : Fin 8, (sectionSixFirstHighCentralSmallQuadrupleCertificateCell
    (shard, Fin.castAdd 32 (Fin.castAdd 24 j))).weight

def sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1
    (shard : Fin 32) : Real :=
  ∑ j : Fin 8, (sectionSixFirstHighCentralSmallQuadrupleCertificateCell
    (shard, Fin.castAdd 32 (Fin.castAdd 16 (Fin.natAdd 8 j)))).weight

def sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2
    (shard : Fin 32) : Real :=
  ∑ j : Fin 8, (sectionSixFirstHighCentralSmallQuadrupleCertificateCell
    (shard, Fin.castAdd 32 (Fin.castAdd 8 (Fin.natAdd 16 j)))).weight

def sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3
    (shard : Fin 32) : Real :=
  ∑ j : Fin 8, (sectionSixFirstHighCentralSmallQuadrupleCertificateCell
    (shard, Fin.castAdd 32 (Fin.natAdd 24 j))).weight

def sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0
    (shard : Fin 32) : Real :=
  ∑ j : Fin 8, (sectionSixFirstHighCentralSmallQuadrupleCertificateCell
    (shard, Fin.natAdd 32 (Fin.castAdd 24 j))).weight

def sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1
    (shard : Fin 32) : Real :=
  ∑ j : Fin 8, (sectionSixFirstHighCentralSmallQuadrupleCertificateCell
    (shard, Fin.natAdd 32 (Fin.castAdd 16 (Fin.natAdd 8 j)))).weight

def sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2
    (shard : Fin 32) : Real :=
  ∑ j : Fin 8, (sectionSixFirstHighCentralSmallQuadrupleCertificateCell
    (shard, Fin.natAdd 32 (Fin.castAdd 8 (Fin.natAdd 16 j)))).weight

def sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3
    (shard : Fin 32) : Real :=
  ∑ j : Fin 8, (sectionSixFirstHighCentralSmallQuadrupleCertificateCell
    (shard, Fin.natAdd 32 (Fin.natAdd 24 j))).weight

def sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum
    (shard : Fin 32) : Real :=
  ∑ j : Fin 64,
    (sectionSixFirstHighCentralSmallQuadrupleCertificateCell (shard, j)).weight

private theorem sectionSixFirstHighCentralSmallQuadrupleCertificate_sum_four
    {α : Type} [AddCommMonoid α] (f : Fin 32 → α) :
    (∑ i : Fin 32, f i) =
      (∑ i : Fin 8, f (Fin.castAdd 24 i)) +
        (∑ i : Fin 8, f (Fin.castAdd 16 (Fin.natAdd 8 i))) +
        (∑ i : Fin 8, f (Fin.castAdd 8 (Fin.natAdd 16 i))) +
        (∑ i : Fin 8, f (Fin.natAdd 24 i)) := by
  change (∑ i : Fin (8 + 24), f i) = _
  rw [Fin.sum_univ_add]
  change (∑ i : Fin 8, f (Fin.castAdd 24 i)) +
      (∑ i : Fin (8 + 16), f (Fin.natAdd 8 i)) = _
  rw [Fin.sum_univ_add]
  change (∑ i : Fin 8, f (Fin.castAdd 24 i)) +
      ((∑ i : Fin 8, f (Fin.castAdd 16 (Fin.natAdd 8 i))) +
        (∑ i : Fin (8 + 8), f (Fin.natAdd 16 i))) = _
  rw [Fin.sum_univ_add]
  change (∑ i : Fin 8, f (Fin.castAdd 24 i)) +
      ((∑ i : Fin 8, f (Fin.castAdd 16 (Fin.natAdd 8 i))) +
        ((∑ i : Fin 8, f (Fin.castAdd 8 (Fin.natAdd 16 i))) +
          (∑ i : Fin 8, f (Fin.natAdd 24 i)))) = _
  ac_rfl

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks
    (shard : Fin 32) :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero shard =
      sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 shard +
        sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 shard +
        sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 shard +
        sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 shard := by
  unfold sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificate_sum_four]
  rfl

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks
    (shard : Fin 32) :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne shard =
      sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 shard +
        sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 shard +
        sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 shard +
        sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 shard := by
  unfold sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificate_sum_four]
  rfl

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves
    (shard : Fin 32) :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum shard =
      sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero shard +
        sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne shard := by
  unfold sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne
  rw [Fin.sum_univ_add (a := 32) (b := 32) (fun j =>
    (sectionSixFirstHighCentralSmallQuadrupleCertificateCell (shard, j)).weight)]

end
end PrimesRestrictedDigits
