import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighFarCertificateCells
import PrimesRestrictedDigits.BasicEstimates.CayleyLogUpper
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstHighFarCertificateManifest -/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def highFarShardSum (branch : Fin 2) (block : Fin 10) : Real :=
  ∑ offset : Fin 16,
    (sectionSixFirstHighFarCertificateCell
      (branch, finProdFinEquiv (block, offset))).weight

private theorem highFarShard00 :
    highFarShardSum 0 0 < 749960 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard01 :
    highFarShardSum 0 1 < 772068 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard02 :
    highFarShardSum 0 2 < 794563 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard03 :
    highFarShardSum 0 3 < 817461 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard04 :
    highFarShardSum 0 4 < 840784 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard05 :
    highFarShardSum 0 5 < 864549 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard06 :
    highFarShardSum 0 6 < 888779 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard07 :
    highFarShardSum 0 7 < 913494 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard08 :
    highFarShardSum 0 8 < 938718 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard09 :
    highFarShardSum 0 9 < 964475 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard10 :
    highFarShardSum 1 0 < 1137430 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard11 :
    highFarShardSum 1 1 < 1178403 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard12 :
    highFarShardSum 1 2 < 1221427 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard13 :
    highFarShardSum 1 3 < 1266658 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard14 :
    highFarShardSum 1 4 < 1314265 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard15 :
    highFarShardSum 1 5 < 1364433 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard16 :
    highFarShardSum 1 6 < 1417371 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard17 :
    highFarShardSum 1 7 < 1473305 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard18 :
    highFarShardSum 1 8 < 1532490 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private theorem highFarShard19 :
    highFarShardSum 1 9 < 1595208 / 100000000 := by
  norm_num [highFarShardSum, sectionSixFirstHighFarCertificateCell,
    SectionSixFirstHighFarCertificateCell.weight, cayleyLogSeriesUpper,
    uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
    Fin.sum_univ_succ]

private def highFarShardIndexEquiv :
    Fin 2 × (Fin 10 × Fin 16) ≃ Fin 2 × Fin 160 :=
  Equiv.prodCongr (Equiv.refl _) finProdFinEquiv

private def highFarShardUpper (branch : Fin 2) (block : Fin 10) : Real :=
  if branch = 0 then
    if block = 0 then 749960 / 100000000
    else if block = 1 then 772068 / 100000000
    else if block = 2 then 794563 / 100000000
    else if block = 3 then 817461 / 100000000
    else if block = 4 then 840784 / 100000000
    else if block = 5 then 864549 / 100000000
    else if block = 6 then 888779 / 100000000
    else if block = 7 then 913494 / 100000000
    else if block = 8 then 938718 / 100000000
    else 964475 / 100000000
  else
    if block = 0 then 1137430 / 100000000
    else if block = 1 then 1178403 / 100000000
    else if block = 2 then 1221427 / 100000000
    else if block = 3 then 1266658 / 100000000
    else if block = 4 then 1314265 / 100000000
    else if block = 5 then 1364433 / 100000000
    else if block = 6 then 1417371 / 100000000
    else if block = 7 then 1473305 / 100000000
    else if block = 8 then 1532490 / 100000000
    else 1595208 / 100000000

private theorem highFarShard_lt (branch : Fin 2) (block : Fin 10) :
    highFarShardSum branch block < highFarShardUpper branch block := by
  fin_cases branch <;> fin_cases block
  · simpa [highFarShardUpper] using highFarShard00
  · simpa [highFarShardUpper] using highFarShard01
  · simpa [highFarShardUpper] using highFarShard02
  · simpa [highFarShardUpper] using highFarShard03
  · simpa [highFarShardUpper] using highFarShard04
  · simpa [highFarShardUpper] using highFarShard05
  · simpa [highFarShardUpper] using highFarShard06
  · simpa [highFarShardUpper] using highFarShard07
  · simpa [highFarShardUpper] using highFarShard08
  · simpa [highFarShardUpper] using highFarShard09
  · simpa [highFarShardUpper] using highFarShard10
  · simpa [highFarShardUpper] using highFarShard11
  · simpa [highFarShardUpper] using highFarShard12
  · simpa [highFarShardUpper] using highFarShard13
  · simpa [highFarShardUpper] using highFarShard14
  · simpa [highFarShardUpper] using highFarShard15
  · simpa [highFarShardUpper] using highFarShard16
  · simpa [highFarShardUpper] using highFarShard17
  · simpa [highFarShardUpper] using highFarShard18
  · simpa [highFarShardUpper] using highFarShard19

private theorem highFarWeightSum_eq_shards :
    (∑ index : Fin 2 × Fin 160,
      (sectionSixFirstHighFarCertificateCell index).weight) =
      ∑ branch : Fin 2, ∑ block : Fin 10, highFarShardSum branch block := by
  calc
    _ = ∑ index : Fin 2 × (Fin 10 × Fin 16),
        (sectionSixFirstHighFarCertificateCell
          (highFarShardIndexEquiv index)).weight :=
      (highFarShardIndexEquiv.sum_comp
        (fun index => (sectionSixFirstHighFarCertificateCell index).weight)).symm
    _ = _ := by
      simp [highFarShardIndexEquiv, highFarShardSum, Fintype.sum_prod_type]

theorem sectionSixFirstHighFarCertificate_weight_sum_lt_exact :
    (∑ index : Fin 2 × Fin 160,
      (sectionSixFirstHighFarCertificateCell index).weight) <
        (22045841 : Real) / 100000000 := by
  rw [highFarWeightSum_eq_shards]
  calc
    _ < ∑ branch : Fin 2, ∑ block : Fin 10,
        highFarShardUpper branch block := by
      apply Finset.sum_lt_sum_of_nonempty (by simp)
      intro branch _
      apply Finset.sum_lt_sum_of_nonempty (by simp)
      intro block _
      exact highFarShard_lt branch block
    _ = (22045841 : Real) / 100000000 := by
      simp [highFarShardUpper, Fin.sum_univ_succ]
      norm_num

theorem sectionSixFirstHighFarCertificate_weight_sum_lt :
    (∑ index : Fin 2 × Fin 160,
      (sectionSixFirstHighFarCertificateCell index).weight) <
        (689 : Real) / 3125 := by
  exact lt_of_lt_of_le
    sectionSixFirstHighFarCertificate_weight_sum_lt_exact (by norm_num)

theorem sectionSixFirstHighFarCertificate_weight_sum_lt_old_cap :
    (∑ index : Fin 2 × Fin 160,
      (sectionSixFirstHighFarCertificateCell index).weight) <
        (221 : Real) / 1000 := by
  exact lt_of_lt_of_le sectionSixFirstHighFarCertificate_weight_sum_lt (by norm_num)

end
end PrimesRestrictedDigits
