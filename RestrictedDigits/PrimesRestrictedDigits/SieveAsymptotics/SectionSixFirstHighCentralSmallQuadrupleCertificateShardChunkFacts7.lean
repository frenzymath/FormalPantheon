import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateShardBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstHighCentralSmallQuadrupleCertificateShardChunkFacts7 -/

namespace PrimesRestrictedDigits

noncomputable section

local macro "close_i9_h0_chunk0" : tactic =>
  `(tactic|
    norm_num [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0,
      sectionSixFirstHighCentralSmallQuadrupleCertificateCell,
      SectionSixFirstHighCentralSmallQuadrupleCertificateCell.weight,
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogLower,
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogUpper,
      sectionSixFirstHighCentralSmallQuadrupleCertificateBeta,
      sectionSixFirstHighCentralSmallQuadrupleCertificateGap,
      sectionSixFirstHighCentralSmallQuadrupleCertificateC,
      sectionSixFirstHighCentralSmallQuadrupleCertificateTail,
      cayleyLogSeriesUpper, uniformRealGridLower, uniformRealGridUpper,
      finProdFinEquiv, Fin.sum_univ_succ, Finset.sum_range_succ])

local macro "close_i9_h1_chunk0" : tactic =>
  `(tactic|
    norm_num [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0,
      sectionSixFirstHighCentralSmallQuadrupleCertificateCell,
      SectionSixFirstHighCentralSmallQuadrupleCertificateCell.weight,
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogLower,
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogUpper,
      sectionSixFirstHighCentralSmallQuadrupleCertificateBeta,
      sectionSixFirstHighCentralSmallQuadrupleCertificateGap,
      sectionSixFirstHighCentralSmallQuadrupleCertificateC,
      sectionSixFirstHighCentralSmallQuadrupleCertificateTail,
      cayleyLogSeriesUpper, uniformRealGridLower, uniformRealGridUpper,
      finProdFinEquiv, Fin.sum_univ_succ, Finset.sum_range_succ])

local macro "close_i9_h0_chunk1" : tactic =>
  `(tactic|
    norm_num [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1,
      sectionSixFirstHighCentralSmallQuadrupleCertificateCell,
      SectionSixFirstHighCentralSmallQuadrupleCertificateCell.weight,
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogLower,
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogUpper,
      sectionSixFirstHighCentralSmallQuadrupleCertificateBeta,
      sectionSixFirstHighCentralSmallQuadrupleCertificateGap,
      sectionSixFirstHighCentralSmallQuadrupleCertificateC,
      sectionSixFirstHighCentralSmallQuadrupleCertificateTail,
      cayleyLogSeriesUpper, uniformRealGridLower, uniformRealGridUpper,
      finProdFinEquiv, Fin.sum_univ_succ, Finset.sum_range_succ])

local macro "close_i9_h1_chunk1" : tactic =>
  `(tactic|
    norm_num [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1,
      sectionSixFirstHighCentralSmallQuadrupleCertificateCell,
      SectionSixFirstHighCentralSmallQuadrupleCertificateCell.weight,
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogLower,
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogUpper,
      sectionSixFirstHighCentralSmallQuadrupleCertificateBeta,
      sectionSixFirstHighCentralSmallQuadrupleCertificateGap,
      sectionSixFirstHighCentralSmallQuadrupleCertificateC,
      sectionSixFirstHighCentralSmallQuadrupleCertificateTail,
      cayleyLogSeriesUpper, uniformRealGridLower, uniformRealGridUpper,
      finProdFinEquiv, Fin.sum_univ_succ, Finset.sum_range_succ])

local macro "close_i9_h0_chunk2" : tactic =>
  `(tactic|
    norm_num [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2,
      sectionSixFirstHighCentralSmallQuadrupleCertificateCell,
      SectionSixFirstHighCentralSmallQuadrupleCertificateCell.weight,
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogLower,
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogUpper,
      sectionSixFirstHighCentralSmallQuadrupleCertificateBeta,
      sectionSixFirstHighCentralSmallQuadrupleCertificateGap,
      sectionSixFirstHighCentralSmallQuadrupleCertificateC,
      sectionSixFirstHighCentralSmallQuadrupleCertificateTail,
      cayleyLogSeriesUpper, uniformRealGridLower, uniformRealGridUpper,
      finProdFinEquiv, Fin.sum_univ_succ, Finset.sum_range_succ])

local macro "close_i9_h1_chunk2" : tactic =>
  `(tactic|
    norm_num [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2,
      sectionSixFirstHighCentralSmallQuadrupleCertificateCell,
      SectionSixFirstHighCentralSmallQuadrupleCertificateCell.weight,
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogLower,
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogUpper,
      sectionSixFirstHighCentralSmallQuadrupleCertificateBeta,
      sectionSixFirstHighCentralSmallQuadrupleCertificateGap,
      sectionSixFirstHighCentralSmallQuadrupleCertificateC,
      sectionSixFirstHighCentralSmallQuadrupleCertificateTail,
      cayleyLogSeriesUpper, uniformRealGridLower, uniformRealGridUpper,
      finProdFinEquiv, Fin.sum_univ_succ, Finset.sum_range_succ])

local macro "close_i9_h0_chunk3" : tactic =>
  `(tactic|
    norm_num [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3,
      sectionSixFirstHighCentralSmallQuadrupleCertificateCell,
      SectionSixFirstHighCentralSmallQuadrupleCertificateCell.weight,
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogLower,
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogUpper,
      sectionSixFirstHighCentralSmallQuadrupleCertificateBeta,
      sectionSixFirstHighCentralSmallQuadrupleCertificateGap,
      sectionSixFirstHighCentralSmallQuadrupleCertificateC,
      sectionSixFirstHighCentralSmallQuadrupleCertificateTail,
      cayleyLogSeriesUpper, uniformRealGridLower, uniformRealGridUpper,
      finProdFinEquiv, Fin.sum_univ_succ, Finset.sum_range_succ])

local macro "close_i9_h1_chunk3" : tactic =>
  `(tactic|
    norm_num [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3,
      sectionSixFirstHighCentralSmallQuadrupleCertificateCell,
      SectionSixFirstHighCentralSmallQuadrupleCertificateCell.weight,
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogLower,
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogUpper,
      sectionSixFirstHighCentralSmallQuadrupleCertificateBeta,
      sectionSixFirstHighCentralSmallQuadrupleCertificateGap,
      sectionSixFirstHighCentralSmallQuadrupleCertificateC,
      sectionSixFirstHighCentralSmallQuadrupleCertificateTail,
      cayleyLogSeriesUpper, uniformRealGridLower, uniformRealGridUpper,
      finProdFinEquiv, Fin.sum_univ_succ, Finset.sum_range_succ])

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_28_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 28 <
      (21975 : Real) / 10000000000 := by
  close_i9_h0_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_28_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 28 <
      (21048 : Real) / 10000000000 := by
  close_i9_h0_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_28_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 28 <
      (20145 : Real) / 10000000000 := by
  close_i9_h0_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_28_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 28 <
      (19267 : Real) / 10000000000 := by
  close_i9_h0_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_28_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 28 <
      (18414 : Real) / 10000000000 := by
  close_i9_h1_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_28_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 28 <
      (17584 : Real) / 10000000000 := by
  close_i9_h1_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_28_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 28 <
      (16779 : Real) / 10000000000 := by
  close_i9_h1_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_28_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 28 <
      (15996 : Real) / 10000000000 := by
  close_i9_h1_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_28_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 28 <
      (1513 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_28_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_28_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_28_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_28_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_28_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_28_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_28_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_28_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_29_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 29 <
      (15238 : Real) / 10000000000 := by
  close_i9_h0_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_29_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 29 <
      (14502 : Real) / 10000000000 := by
  close_i9_h0_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_29_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 29 <
      (13789 : Real) / 10000000000 := by
  close_i9_h0_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_29_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 29 <
      (13098 : Real) / 10000000000 := by
  close_i9_h0_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_29_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 29 <
      (12430 : Real) / 10000000000 := by
  close_i9_h1_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_29_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 29 <
      (11783 : Real) / 10000000000 := by
  close_i9_h1_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_29_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 29 <
      (11158 : Real) / 10000000000 := by
  close_i9_h1_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_29_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 29 <
      (10555 : Real) / 10000000000 := by
  close_i9_h1_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_29_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 29 <
      (1026 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_29_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_29_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_29_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_29_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_29_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_29_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_29_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_29_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_30_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 30 <
      (9972 : Real) / 10000000000 := by
  close_i9_h0_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_30_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 30 <
      (9411 : Real) / 10000000000 := by
  close_i9_h0_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_30_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 30 <
      (8869 : Real) / 10000000000 := by
  close_i9_h0_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_30_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 30 <
      (8348 : Real) / 10000000000 := by
  close_i9_h0_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_30_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 30 <
      (7847 : Real) / 10000000000 := by
  close_i9_h1_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_30_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 30 <
      (7366 : Real) / 10000000000 := by
  close_i9_h1_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_30_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 30 <
      (6903 : Real) / 10000000000 := by
  close_i9_h1_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_30_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 30 <
      (6460 : Real) / 10000000000 := by
  close_i9_h1_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_30_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 30 <
      (652 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_30_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_30_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_30_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_30_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_30_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_30_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_30_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_30_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_31_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 31 <
      (6035 : Real) / 10000000000 := by
  close_i9_h0_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_31_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 31 <
      (5628 : Real) / 10000000000 := by
  close_i9_h0_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_31_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 31 <
      (5240 : Real) / 10000000000 := by
  close_i9_h0_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_31_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 31 <
      (4868 : Real) / 10000000000 := by
  close_i9_h0_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_31_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 31 <
      (4515 : Real) / 10000000000 := by
  close_i9_h1_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_31_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 31 <
      (4178 : Real) / 10000000000 := by
  close_i9_h1_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_31_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 31 <
      (3857 : Real) / 10000000000 := by
  close_i9_h1_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_31_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 31 <
      (3553 : Real) / 10000000000 := by
  close_i9_h1_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_31_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 31 <
      (379 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_31_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_31_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_31_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_31_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_31_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_31_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_31_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_31_lt]

end
end PrimesRestrictedDigits
