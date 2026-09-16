import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateShardBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstHighCentralSmallQuadrupleCertificateShardChunkFacts0 -/

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

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_00_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 0 <
      (1121189 : Real) / 10000000000 := by
  close_i9_z0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_00_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 0 <
      (1111667 : Real) / 10000000000 := by
  close_i9_z1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_00_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 0 <
      (1102190 : Real) / 10000000000 := by
  close_i9_z2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_00_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 0 <
      (1092759 : Real) / 10000000000 := by
  close_i9_z3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_00_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 0 <
      (1083372 : Real) / 10000000000 := by
  close_i9_o0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_00_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 0 <
      (1074030 : Real) / 10000000000 := by
  close_i9_o1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_00_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 0 <
      (1064733 : Real) / 10000000000 := by
  close_i9_o2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_00_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 0 <
      (1055481 : Real) / 10000000000 := by
  close_i9_o3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_00_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 0 <
      (87055 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_00_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_00_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_00_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_00_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_00_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_00_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_00_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_00_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_01_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 1 <
      (1046274 : Real) / 10000000000 := by
  close_i9_z0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_01_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 1 <
      (1037112 : Real) / 10000000000 := by
  close_i9_z1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_01_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 1 <
      (1027995 : Real) / 10000000000 := by
  close_i9_z2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_01_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 1 <
      (1018922 : Real) / 10000000000 := by
  close_i9_z3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_01_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 1 <
      (1009894 : Real) / 10000000000 := by
  close_i9_o0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_01_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 1 <
      (1000911 : Real) / 10000000000 := by
  close_i9_o1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_01_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 1 <
      (991972 : Real) / 10000000000 := by
  close_i9_o2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_01_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 1 <
      (983078 : Real) / 10000000000 := by
  close_i9_o3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_01_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 1 <
      (81162 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_01_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_01_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_01_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_01_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_01_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_01_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_01_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_01_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_02_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 2 <
      (974229 : Real) / 10000000000 := by
  close_i9_z0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_02_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 2 <
      (965424 : Real) / 10000000000 := by
  close_i9_z1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_02_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 2 <
      (956663 : Real) / 10000000000 := by
  close_i9_z2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_02_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 2 <
      (947947 : Real) / 10000000000 := by
  close_i9_z3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_02_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 2 <
      (939275 : Real) / 10000000000 := by
  close_i9_o0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_02_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 2 <
      (930648 : Real) / 10000000000 := by
  close_i9_o1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_02_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 2 <
      (922065 : Real) / 10000000000 := by
  close_i9_o2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_02_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 2 <
      (913527 : Real) / 10000000000 := by
  close_i9_o3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_02_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 2 <
      (75498 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_02_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_02_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_02_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_02_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_02_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_02_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_02_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_02_lt]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_03_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0 3 <
      (905032 : Real) / 10000000000 := by
  close_i9_z0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_03_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1 3 <
      (896582 : Real) / 10000000000 := by
  close_i9_z1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_03_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2 3 <
      (888176 : Real) / 10000000000 := by
  close_i9_z2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_03_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3 3 <
      (879814 : Real) / 10000000000 := by
  close_i9_z3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_03_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0 3 <
      (871496 : Real) / 10000000000 := by
  close_i9_o0

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_03_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1 3 <
      (863223 : Real) / 10000000000 := by
  close_i9_o1

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_03_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2 3 <
      (854993 : Real) / 10000000000 := by
  close_i9_o2

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_03_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3 3 <
      (846807 : Real) / 10000000000 := by
  close_i9_o3

theorem sectionSixFirstHighCentralSmallQuadrupleCertificateShard_03_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum 3 <
      (70062 : Real) / 100000000 := by
  rw [sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum_eq_halves,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZero_eq_chunks,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOne_eq_chunks]
  linarith [sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk0_03_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk1_03_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk2_03_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfZeroChunk3_03_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk0_03_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk1_03_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk2_03_lt, sectionSixFirstHighCentralSmallQuadrupleCertificateShardHalfOneChunk3_03_lt]

end
end PrimesRestrictedDigits
