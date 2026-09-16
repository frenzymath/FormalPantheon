import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateShardBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstHighCentralSmallQuadrupleCertificateShardChunkFacts3 -/

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

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_12_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 12 <
      (407030 : Real) / 10000000000 := by
  close_i9_z0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_12_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 12 <
      (401650 : Real) / 10000000000 := by
  close_i9_z1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_12_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 12 <
      (396311 : Real) / 10000000000 := by
  close_i9_z2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_12_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 12 <
      (391013 : Real) / 10000000000 := by
  close_i9_z3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_12_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 12 <
      (385755 : Real) / 10000000000 := by
  close_i9_o0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_12_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 12 <
      (380538 : Real) / 10000000000 := by
  close_i9_o1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_12_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 12 <
      (375362 : Real) / 10000000000 := by
  close_i9_o2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_12_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 12 <
      (370226 : Real) / 10000000000 := by
  close_i9_o3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_12_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 12 <
      (31079 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_12_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_12_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_12_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_12_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_12_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_12_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_12_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_12_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_13_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 13 <
      (365130 : Real) / 10000000000 := by
  close_i9_z0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_13_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 13 <
      (360075 : Real) / 10000000000 := by
  close_i9_z1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_13_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 13 <
      (355060 : Real) / 10000000000 := by
  close_i9_z2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_13_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 13 <
      (350086 : Real) / 10000000000 := by
  close_i9_z3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_13_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 13 <
      (345152 : Real) / 10000000000 := by
  close_i9_o0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_13_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 13 <
      (340258 : Real) / 10000000000 := by
  close_i9_o1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_13_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 13 <
      (335404 : Real) / 10000000000 := by
  close_i9_o2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_13_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 13 <
      (330590 : Real) / 10000000000 := by
  close_i9_o3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_13_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 13 <
      (27818 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_13_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_13_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_13_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_13_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_13_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_13_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_13_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_13_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_14_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 14 <
      (325816 : Real) / 10000000000 := by
  close_i9_z0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_14_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 14 <
      (321082 : Real) / 10000000000 := by
  close_i9_z1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_14_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 14 <
      (316388 : Real) / 10000000000 := by
  close_i9_z2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_14_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 14 <
      (311734 : Real) / 10000000000 := by
  close_i9_z3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_14_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 14 <
      (307119 : Real) / 10000000000 := by
  close_i9_o0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_14_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 14 <
      (302544 : Real) / 10000000000 := by
  close_i9_o1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_14_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 14 <
      (298008 : Real) / 10000000000 := by
  close_i9_o2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_14_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 14 <
      (293512 : Real) / 10000000000 := by
  close_i9_o3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_14_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 14 <
      (24763 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_14_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_14_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_14_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_14_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_14_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_14_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_14_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_14_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_15_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 15 <
      (289056 : Real) / 10000000000 := by
  close_i9_z0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_15_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 15 <
      (284638 : Real) / 10000000000 := by
  close_i9_z1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_15_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 15 <
      (280260 : Real) / 10000000000 := by
  close_i9_z2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_15_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 15 <
      (275922 : Real) / 10000000000 := by
  close_i9_z3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_15_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 15 <
      (271622 : Real) / 10000000000 := by
  close_i9_o0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_15_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 15 <
      (267361 : Real) / 10000000000 := by
  close_i9_o1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_15_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 15 <
      (263140 : Real) / 10000000000 := by
  close_i9_o2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_15_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 15 <
      (258957 : Real) / 10000000000 := by
  close_i9_o3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_15_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 15 <
      (21910 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_15_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_15_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_15_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_15_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_15_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_15_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_15_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_15_lt]

end
end PrimesRestrictedDigits
