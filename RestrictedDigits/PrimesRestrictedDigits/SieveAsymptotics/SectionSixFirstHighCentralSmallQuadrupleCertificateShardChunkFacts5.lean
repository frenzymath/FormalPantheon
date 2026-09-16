import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateShardBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstHighCentralSmallQuadrupleCertificateShardChunkFacts5 -/

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

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_20_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 20 <
      (142196 : Real) / 10000000000 := by
  close_i9_h0_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_20_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 20 <
      (139284 : Real) / 10000000000 := by
  close_i9_h0_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_20_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 20 <
      (136408 : Real) / 10000000000 := by
  close_i9_h0_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_20_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 20 <
      (133567 : Real) / 10000000000 := by
  close_i9_h0_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_20_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 20 <
      (130762 : Real) / 10000000000 := by
  close_i9_h1_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_20_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 20 <
      (127992 : Real) / 10000000000 := by
  close_i9_h1_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_20_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 20 <
      (125257 : Real) / 10000000000 := by
  close_i9_h1_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_20_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 20 <
      (122557 : Real) / 10000000000 := by
  close_i9_h1_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_20_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 20 <
      (10581 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_20_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_20_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_20_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_20_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_20_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_20_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_20_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_20_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_21_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 21 <
      (119892 : Real) / 10000000000 := by
  close_i9_h0_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_21_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 21 <
      (117262 : Real) / 10000000000 := by
  close_i9_h0_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_21_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 21 <
      (114666 : Real) / 10000000000 := by
  close_i9_h0_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_21_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 21 <
      (112105 : Real) / 10000000000 := by
  close_i9_h0_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_21_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 21 <
      (109579 : Real) / 10000000000 := by
  close_i9_h1_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_21_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 21 <
      (107087 : Real) / 10000000000 := by
  close_i9_h1_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_21_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 21 <
      (104629 : Real) / 10000000000 := by
  close_i9_h1_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_21_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 21 <
      (102205 : Real) / 10000000000 := by
  close_i9_h1_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_21_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 21 <
      (8875 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_21_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_21_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_21_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_21_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_21_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_21_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_21_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_21_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_22_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 22 <
      (99815 : Real) / 10000000000 := by
  close_i9_h0_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_22_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 22 <
      (97459 : Real) / 10000000000 := by
  close_i9_h0_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_22_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 22 <
      (95137 : Real) / 10000000000 := by
  close_i9_h0_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_22_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 22 <
      (92848 : Real) / 10000000000 := by
  close_i9_h0_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_22_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 22 <
      (90592 : Real) / 10000000000 := by
  close_i9_h1_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_22_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 22 <
      (88370 : Real) / 10000000000 := by
  close_i9_h1_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_22_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 22 <
      (86181 : Real) / 10000000000 := by
  close_i9_h1_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_22_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 22 <
      (84024 : Real) / 10000000000 := by
  close_i9_h1_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_22_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 22 <
      (7345 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_22_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_22_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_22_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_22_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_22_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_22_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_22_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_22_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_23_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 23 <
      (81901 : Real) / 10000000000 := by
  close_i9_h0_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_23_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 23 <
      (79810 : Real) / 10000000000 := by
  close_i9_h0_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_23_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 23 <
      (77752 : Real) / 10000000000 := by
  close_i9_h0_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_23_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 23 <
      (75726 : Real) / 10000000000 := by
  close_i9_h0_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_23_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 23 <
      (73733 : Real) / 10000000000 := by
  close_i9_h1_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_23_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 23 <
      (71771 : Real) / 10000000000 := by
  close_i9_h1_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_23_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 23 <
      (69842 : Real) / 10000000000 := by
  close_i9_h1_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_23_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 23 <
      (67944 : Real) / 10000000000 := by
  close_i9_h1_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_23_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 23 <
      (5985 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_23_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_23_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_23_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_23_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_23_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_23_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_23_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_23_lt]

end
end PrimesRestrictedDigits
