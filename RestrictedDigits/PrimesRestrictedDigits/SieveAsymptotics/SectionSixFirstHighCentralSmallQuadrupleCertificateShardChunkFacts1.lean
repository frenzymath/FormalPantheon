import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateShardBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstHighCentralSmallQuadrupleCertificateShardChunkFacts1 -/

namespace PrimesRestrictedDigits

noncomputable section

local macro "close_i9_z0" : tactic =>
  `(tactic|
    norm_num [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0,
      sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0,
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

local macro "close_i9_z1" : tactic =>
  `(tactic|
    norm_num [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1,
      sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1,
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

local macro "close_i9_z2" : tactic =>
  `(tactic|
    norm_num [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2,
      sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2,
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

local macro "close_i9_z3" : tactic =>
  `(tactic|
    norm_num [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3,
      sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3,
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

local macro "close_i9_o0" : tactic =>
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

local macro "close_i9_o1" : tactic =>
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

local macro "close_i9_o2" : tactic =>
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

local macro "close_i9_o3" : tactic =>
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

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_04_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 4 <
      (838665 : Real) / 10000000000 := by
  close_i9_z0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_04_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 4 <
      (830567 : Real) / 10000000000 := by
  close_i9_z1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_04_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 4 <
      (822513 : Real) / 10000000000 := by
  close_i9_z2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_04_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 4 <
      (814503 : Real) / 10000000000 := by
  close_i9_z3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_04_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 4 <
      (806537 : Real) / 10000000000 := by
  close_i9_o0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_04_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 4 <
      (798614 : Real) / 10000000000 := by
  close_i9_o1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_04_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 4 <
      (790735 : Real) / 10000000000 := by
  close_i9_o2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_04_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 4 <
      (782899 : Real) / 10000000000 := by
  close_i9_o3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_04_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 4 <
      (64851 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_04_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_04_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_04_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_04_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_04_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_04_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_04_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_04_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_05_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 5 <
      (775108 : Real) / 10000000000 := by
  close_i9_z0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_05_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 5 <
      (767359 : Real) / 10000000000 := by
  close_i9_z1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_05_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 5 <
      (759655 : Real) / 10000000000 := by
  close_i9_z2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_05_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 5 <
      (751994 : Real) / 10000000000 := by
  close_i9_z3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_05_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 5 <
      (744376 : Real) / 10000000000 := by
  close_i9_o0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_05_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 5 <
      (736802 : Real) / 10000000000 := by
  close_i9_o1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_05_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 5 <
      (729271 : Real) / 10000000000 := by
  close_i9_o2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_05_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 5 <
      (721783 : Real) / 10000000000 := by
  close_i9_o3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_05_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 5 <
      (59864 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_05_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_05_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_05_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_05_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_05_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_05_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_05_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_05_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_06_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 6 <
      (714339 : Real) / 10000000000 := by
  close_i9_z0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_06_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 6 <
      (706938 : Real) / 10000000000 := by
  close_i9_z1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_06_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 6 <
      (699580 : Real) / 10000000000 := by
  close_i9_z2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_06_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 6 <
      (692265 : Real) / 10000000000 := by
  close_i9_z3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_06_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 6 <
      (684993 : Real) / 10000000000 := by
  close_i9_o0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_06_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 6 <
      (677765 : Real) / 10000000000 := by
  close_i9_o1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_06_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 6 <
      (670579 : Real) / 10000000000 := by
  close_i9_o2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_06_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 6 <
      (663437 : Real) / 10000000000 := by
  close_i9_o3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_06_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 6 <
      (55099 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_06_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_06_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_06_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_06_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_06_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_06_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_06_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_06_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_07_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 7 <
      (656337 : Real) / 10000000000 := by
  close_i9_z0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_07_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 7 <
      (649280 : Real) / 10000000000 := by
  close_i9_z1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_07_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 7 <
      (642267 : Real) / 10000000000 := by
  close_i9_z2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_07_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 7 <
      (635296 : Real) / 10000000000 := by
  close_i9_z3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_07_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 7 <
      (628367 : Real) / 10000000000 := by
  close_i9_o0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_07_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 7 <
      (621482 : Real) / 10000000000 := by
  close_i9_o1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_07_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 7 <
      (614639 : Real) / 10000000000 := by
  close_i9_o2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_07_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 7 <
      (607839 : Real) / 10000000000 := by
  close_i9_o3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_07_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 7 <
      (50556 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_07_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_07_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_07_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_07_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_07_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_07_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_07_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_07_lt]

end
end PrimesRestrictedDigits
