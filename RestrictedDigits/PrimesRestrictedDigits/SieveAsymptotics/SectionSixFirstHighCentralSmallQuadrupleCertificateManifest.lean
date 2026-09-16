import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateShardChunkFacts0
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateShardChunkFacts1
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateShardChunkFacts2
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateShardChunkFacts3
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateShardChunkFacts4
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateShardChunkFacts5
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateShardChunkFacts6
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateShardChunkFacts7
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstHighCentralSmallQuadrupleCertificateManifest -/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def highCentralSmallShardSum (shard : Fin 32) : Real :=
  sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum shard

private def highCentralSmallShardUpper (shard : Fin 32) : Real :=
  if shard = 0 then 87055 / 100000000
  else if shard = 1 then 81162 / 100000000
  else if shard = 2 then 75498 / 100000000
  else if shard = 3 then 70062 / 100000000
  else if shard = 4 then 64851 / 100000000
  else if shard = 5 then 59864 / 100000000
  else if shard = 6 then 55099 / 100000000
  else if shard = 7 then 50556 / 100000000
  else if shard = 8 then 46230 / 100000000
  else if shard = 9 then 42122 / 100000000
  else if shard = 10 then 38229 / 100000000
  else if shard = 11 then 34549 / 100000000
  else if shard = 12 then 31079 / 100000000
  else if shard = 13 then 27818 / 100000000
  else if shard = 14 then 24763 / 100000000
  else if shard = 15 then 21910 / 100000000
  else if shard = 16 then 19258 / 100000000
  else if shard = 17 then 16802 / 100000000
  else if shard = 18 then 14540 / 100000000
  else if shard = 19 then 12468 / 100000000
  else if shard = 20 then 10581 / 100000000
  else if shard = 21 then 8875 / 100000000
  else if shard = 22 then 7345 / 100000000
  else if shard = 23 then 5985 / 100000000
  else if shard = 24 then 4790 / 100000000
  else if shard = 25 then 3753 / 100000000
  else if shard = 26 then 2867 / 100000000
  else if shard = 27 then 2123 / 100000000
  else if shard = 28 then 1513 / 100000000
  else if shard = 29 then 1026 / 100000000
  else if shard = 30 then 652 / 100000000
  else 379 / 100000000

private theorem highCentralSmallShard_lt (shard : Fin 32) :
    highCentralSmallShardSum shard < highCentralSmallShardUpper shard := by
  fin_cases shard
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_00_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_01_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_02_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_03_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_04_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_05_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_06_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_07_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_08_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_09_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_10_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_11_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_12_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_13_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_14_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_15_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_16_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_17_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_18_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_19_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_20_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_21_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_22_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_23_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_24_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_25_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_26_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_27_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_28_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_29_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_30_lt
  · simpa [highCentralSmallShardSum, highCentralSmallShardUpper] using
      sectionSixFirstHighCentralSmallQuadrupleCertificateShard_31_lt

private theorem highCentralSmallWeightSum_eq_shards :
    (∑ index : Fin 32 × Fin 64,
      (sectionSixFirstHighCentralSmallQuadrupleCertificateCell index).weight) =
      ∑ shard : Fin 32, highCentralSmallShardSum shard := by
  simp [highCentralSmallShardSum,
    sectionSixFirstHighCentralSmallQuadrupleCertificateShardSum,
    Fintype.sum_prod_type]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificate_weight_sum_lt_raw :
    (∑ index : Fin 32 × Fin 64,
      (sectionSixFirstHighCentralSmallQuadrupleCertificateCell index).weight) <
      (923804 : Real) / 100000000 := by
  rw [highCentralSmallWeightSum_eq_shards]
  have hne : (Finset.univ : Finset (Fin 32)).Nonempty := by simp
  have hsum := Finset.sum_lt_sum_of_nonempty hne (fun shard _ =>
    highCentralSmallShard_lt shard)
  have huppersum : (∑ shard : Fin 32, highCentralSmallShardUpper shard) =
      (923804 : Real) / 100000000 := by
    simp [highCentralSmallShardUpper, Fin.sum_univ_succ]
    norm_num
  rw [huppersum] at hsum
  exact hsum

def sectionSixFirstHighCentralSmallQuadrupleCertificateMiddleBoxCorrection : Real :=
  (sectionSixFirstHighCentralSmallQuadrupleCertificateMiddle -
      sectionSixFirstHighCentralSmallQuadrupleCertificateTail) *
    (17500001 / 250000000 : Real) ^ 4 /
      (240 * sectionSixFirstHighCentralSmallQuadrupleCertificateBeta *
        (9 / 100 : Real) ^ 4)

theorem sectionSixFirstHighCentralSmallQuadrupleCertificate_middle_box_lt :
    sectionSixFirstHighCentralSmallQuadrupleCertificateMiddleBoxCorrection <
      (991 : Real) / 100000000 := by
  norm_num [sectionSixFirstHighCentralSmallQuadrupleCertificateMiddleBoxCorrection,
    sectionSixFirstHighCentralSmallQuadrupleCertificateMiddle,
    sectionSixFirstHighCentralSmallQuadrupleCertificateTail,
    sectionSixFirstHighCentralSmallQuadrupleCertificateBeta]

theorem sectionSixFirstHighCentralSmallQuadrupleCertificate_weight_sum_lt :
    (∑ index : Fin 32 × Fin 64,
      (sectionSixFirstHighCentralSmallQuadrupleCertificateCell index).weight) +
        sectionSixFirstHighCentralSmallQuadrupleCertificateMiddleBoxCorrection <
      (925 : Real) / 100000 := by
  rw [highCentralSmallWeightSum_eq_shards]
  calc
    (∑ shard : Fin 32, highCentralSmallShardSum shard) +
          sectionSixFirstHighCentralSmallQuadrupleCertificateMiddleBoxCorrection <
        (∑ shard : Fin 32, highCentralSmallShardUpper shard) +
          sectionSixFirstHighCentralSmallQuadrupleCertificateMiddleBoxCorrection := by
      have hne : (Finset.univ : Finset (Fin 32)).Nonempty := by simp
      have hsum := Finset.sum_lt_sum_of_nonempty hne (fun shard _ =>
        highCentralSmallShard_lt shard)
      simpa [add_comm] using add_lt_add_left hsum
        sectionSixFirstHighCentralSmallQuadrupleCertificateMiddleBoxCorrection
    _ < (923804 : Real) / 100000000 + (991 : Real) / 100000000 := by
      have hsum : (∑ shard : Fin 32, highCentralSmallShardUpper shard) =
          (923804 : Real) / 100000000 := by
        simp [highCentralSmallShardUpper, Fin.sum_univ_succ]
        norm_num
      rw [hsum]
      simpa [add_comm] using add_lt_add_left
        sectionSixFirstHighCentralSmallQuadrupleCertificate_middle_box_lt
        ((923804 : Real) / 100000000)
    _ < (925 : Real) / 100000 := by norm_num

end
end PrimesRestrictedDigits
