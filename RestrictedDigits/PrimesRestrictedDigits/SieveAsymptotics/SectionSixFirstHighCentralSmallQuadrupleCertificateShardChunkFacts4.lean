import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateShardBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstHighCentralSmallQuadrupleCertificateShardChunkFacts4 -/

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

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_16_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 16 <
      (254813 : Real) / 10000000000 := by
  close_i9_h0_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_16_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 16 <
      (250708 : Real) / 10000000000 := by
  close_i9_h0_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_16_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 16 <
      (246641 : Real) / 10000000000 := by
  close_i9_h0_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_16_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 16 <
      (242613 : Real) / 10000000000 := by
  close_i9_h0_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_16_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 16 <
      (238624 : Real) / 10000000000 := by
  close_i9_h1_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_16_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 16 <
      (234673 : Real) / 10000000000 := by
  close_i9_h1_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_16_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 16 <
      (230760 : Real) / 10000000000 := by
  close_i9_h1_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_16_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 16 <
      (226886 : Real) / 10000000000 := by
  close_i9_h1_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_16_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 16 <
      (19258 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_16_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_16_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_16_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_16_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_16_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_16_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_16_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_16_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_17_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 17 <
      (223049 : Real) / 10000000000 := by
  close_i9_h0_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_17_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 17 <
      (219251 : Real) / 10000000000 := by
  close_i9_h0_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_17_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 17 <
      (215491 : Real) / 10000000000 := by
  close_i9_h0_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_17_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 17 <
      (211769 : Real) / 10000000000 := by
  close_i9_h0_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_17_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 17 <
      (208084 : Real) / 10000000000 := by
  close_i9_h1_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_17_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 17 <
      (204438 : Real) / 10000000000 := by
  close_i9_h1_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_17_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 17 <
      (200829 : Real) / 10000000000 := by
  close_i9_h1_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_17_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 17 <
      (197257 : Real) / 10000000000 := by
  close_i9_h1_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_17_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 17 <
      (16802 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_17_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_17_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_17_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_17_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_17_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_17_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_17_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_17_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_18_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 18 <
      (193723 : Real) / 10000000000 := by
  close_i9_h0_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_18_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 18 <
      (190226 : Real) / 10000000000 := by
  close_i9_h0_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_18_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 18 <
      (186767 : Real) / 10000000000 := by
  close_i9_h0_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_18_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 18 <
      (183345 : Real) / 10000000000 := by
  close_i9_h0_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_18_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 18 <
      (179960 : Real) / 10000000000 := by
  close_i9_h1_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_18_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 18 <
      (176612 : Real) / 10000000000 := by
  close_i9_h1_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_18_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 18 <
      (173301 : Real) / 10000000000 := by
  close_i9_h1_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_18_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 18 <
      (170026 : Real) / 10000000000 := by
  close_i9_h1_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_18_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 18 <
      (14540 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_18_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_18_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_18_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_18_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_18_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_18_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_18_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_18_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_19_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 19 <
      (166789 : Real) / 10000000000 := by
  close_i9_h0_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_19_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 19 <
      (163588 : Real) / 10000000000 := by
  close_i9_h0_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_19_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 19 <
      (160423 : Real) / 10000000000 := by
  close_i9_h0_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_19_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 19 <
      (157295 : Real) / 10000000000 := by
  close_i9_h0_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_19_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 19 <
      (154203 : Real) / 10000000000 := by
  close_i9_h1_chunk0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_19_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 19 <
      (151147 : Real) / 10000000000 := by
  close_i9_h1_chunk1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_19_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 19 <
      (148128 : Real) / 10000000000 := by
  close_i9_h1_chunk2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_19_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 19 <
      (145144 : Real) / 10000000000 := by
  close_i9_h1_chunk3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_19_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 19 <
      (12468 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_19_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_19_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_19_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_19_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_19_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_19_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_19_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_19_lt]

end
end PrimesRestrictedDigits
