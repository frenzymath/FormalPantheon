import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateShardBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstHighCentralSmallQuadrupleCertificateShardChunkFacts6 -/

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

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_24_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 24 <
      (66078 : Real) / 10000000000 := by
  close_i9_h0_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_24_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 24 <
      (64243 : Real) / 10000000000 := by
  close_i9_h0_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_24_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 24 <
      (62439 : Real) / 10000000000 := by
  close_i9_h0_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_24_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 24 <
      (60667 : Real) / 10000000000 := by
  close_i9_h0_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_24_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 24 <
      (58925 : Real) / 10000000000 := by
  close_i9_h1_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_24_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 24 <
      (57215 : Real) / 10000000000 := by
  close_i9_h1_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_24_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 24 <
      (55534 : Real) / 10000000000 := by
  close_i9_h1_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_24_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 24 <
      (53885 : Real) / 10000000000 := by
  close_i9_h1_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_24_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 24 <
      (4790 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_24_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_24_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_24_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_24_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_24_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_24_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_24_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_24_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_25_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 25 <
      (52265 : Real) / 10000000000 := by
  close_i9_h0_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_25_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 25 <
      (50676 : Real) / 10000000000 := by
  close_i9_h0_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_25_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 25 <
      (49116 : Real) / 10000000000 := by
  close_i9_h0_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_25_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 25 <
      (47587 : Real) / 10000000000 := by
  close_i9_h0_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_25_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 25 <
      (46086 : Real) / 10000000000 := by
  close_i9_h1_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_25_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 25 <
      (44615 : Real) / 10000000000 := by
  close_i9_h1_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_25_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 25 <
      (43174 : Real) / 10000000000 := by
  close_i9_h1_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_25_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 25 <
      (41761 : Real) / 10000000000 := by
  close_i9_h1_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_25_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 25 <
      (3753 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_25_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_25_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_25_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_25_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_25_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_25_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_25_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_25_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_26_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 26 <
      (40377 : Real) / 10000000000 := by
  close_i9_h0_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_26_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 26 <
      (39021 : Real) / 10000000000 := by
  close_i9_h0_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_26_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 26 <
      (37694 : Real) / 10000000000 := by
  close_i9_h0_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_26_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 26 <
      (36395 : Real) / 10000000000 := by
  close_i9_h0_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_26_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 26 <
      (35124 : Real) / 10000000000 := by
  close_i9_h1_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_26_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 26 <
      (33881 : Real) / 10000000000 := by
  close_i9_h1_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_26_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 26 <
      (32665 : Real) / 10000000000 := by
  close_i9_h1_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_26_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 26 <
      (31477 : Real) / 10000000000 := by
  close_i9_h1_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_26_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 26 <
      (2867 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_26_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_26_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_26_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_26_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_26_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_26_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_26_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_26_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_27_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 27 <
      (30316 : Real) / 10000000000 := by
  close_i9_h0_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_27_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 27 <
      (29181 : Real) / 10000000000 := by
  close_i9_h0_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_27_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 27 <
      (28074 : Real) / 10000000000 := by
  close_i9_h0_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_27_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 27 <
      (26992 : Real) / 10000000000 := by
  close_i9_h0_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_27_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 27 <
      (25937 : Real) / 10000000000 := by
  close_i9_h1_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_27_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 27 <
      (24908 : Real) / 10000000000 := by
  close_i9_h1_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_27_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 27 <
      (23905 : Real) / 10000000000 := by
  close_i9_h1_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_27_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 27 <
      (22928 : Real) / 10000000000 := by
  close_i9_h1_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_27_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 27 <
      (2123 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_27_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_27_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_27_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_27_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_27_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_27_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_27_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_27_lt]

end
end PrimesRestrictedDigits
