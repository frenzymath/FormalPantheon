import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateShardBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstHighCentralSmallQuadrupleCertificateShardChunkFacts2 -/

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

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_08_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 8 <
      (601081 : Real) / 10000000000 := by
  close_i9_z0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_08_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 8 <
      (594366 : Real) / 10000000000 := by
  close_i9_z1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_08_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 8 <
      (587693 : Real) / 10000000000 := by
  close_i9_z2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_08_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 8 <
      (581063 : Real) / 10000000000 := by
  close_i9_z3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_08_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 8 <
      (574475 : Real) / 10000000000 := by
  close_i9_o0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_08_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 8 <
      (567930 : Real) / 10000000000 := by
  close_i9_o1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_08_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 8 <
      (561426 : Real) / 10000000000 := by
  close_i9_o2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_08_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 8 <
      (554966 : Real) / 10000000000 := by
  close_i9_o3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_08_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 8 <
      (46230 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_08_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_08_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_08_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_08_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_08_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_08_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_08_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_08_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_09_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 9 <
      (548547 : Real) / 10000000000 := by
  close_i9_z0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_09_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 9 <
      (542170 : Real) / 10000000000 := by
  close_i9_z1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_09_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 9 <
      (535836 : Real) / 10000000000 := by
  close_i9_z2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_09_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 9 <
      (529544 : Real) / 10000000000 := by
  close_i9_z3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_09_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 9 <
      (523293 : Real) / 10000000000 := by
  close_i9_o0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_09_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 9 <
      (517085 : Real) / 10000000000 := by
  close_i9_o1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_09_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 9 <
      (510918 : Real) / 10000000000 := by
  close_i9_o2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_09_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 9 <
      (504794 : Real) / 10000000000 := by
  close_i9_o3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_09_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 9 <
      (42122 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_09_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_09_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_09_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_09_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_09_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_09_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_09_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_09_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_10_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 10 <
      (498711 : Real) / 10000000000 := by
  close_i9_z0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_10_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 10 <
      (492670 : Real) / 10000000000 := by
  close_i9_z1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_10_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 10 <
      (486671 : Real) / 10000000000 := by
  close_i9_z2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_10_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 10 <
      (480713 : Real) / 10000000000 := by
  close_i9_z3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_10_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 10 <
      (474797 : Real) / 10000000000 := by
  close_i9_o0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_10_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 10 <
      (468922 : Real) / 10000000000 := by
  close_i9_o1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_10_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 10 <
      (463089 : Real) / 10000000000 := by
  close_i9_o2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_10_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 10 <
      (457298 : Real) / 10000000000 := by
  close_i9_o3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_10_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 10 <
      (38229 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_10_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_10_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_10_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_10_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_10_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_10_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_10_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_10_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_11_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 11 <
      (451548 : Real) / 10000000000 := by
  close_i9_z0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_11_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 11 <
      (445839 : Real) / 10000000000 := by
  close_i9_z1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_11_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 11 <
      (440172 : Real) / 10000000000 := by
  close_i9_z2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_11_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 11 <
      (434545 : Real) / 10000000000 := by
  close_i9_z3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_11_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 11 <
      (428960 : Real) / 10000000000 := by
  close_i9_o0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_11_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 11 <
      (423416 : Real) / 10000000000 := by
  close_i9_o1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_11_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 11 <
      (417913 : Real) / 10000000000 := by
  close_i9_o2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_11_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 11 <
      (412451 : Real) / 10000000000 := by
  close_i9_o3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_11_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 11 <
      (34549 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_11_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_11_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_11_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_11_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_11_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_11_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_11_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_11_lt]

end
end PrimesRestrictedDigits
