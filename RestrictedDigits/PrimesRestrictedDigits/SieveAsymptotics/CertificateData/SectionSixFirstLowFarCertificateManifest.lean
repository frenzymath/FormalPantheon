import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowFarCertificateCells
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstLowFarCertificateManifest -/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def lowFarShardIndexEquiv :
    Fin 2 × ((Fin 6 × Fin 10) × Fin 5) ≃ Fin 2 × (Fin 60 × Fin 5) :=
  Equiv.prodCongr (Equiv.refl _) <|
    Equiv.prodCongr finProdFinEquiv (Equiv.refl _)

private def lowFarShardSum (branch : Fin 2) (block : Fin 6) : Real :=
  ∑ offset : Fin 10 × Fin 5,
    (sectionSixFirstLowFarCertificateCell
      (branch, finProdFinEquiv (block, offset.1), offset.2)).weight

private def lowFarShardUpper (branch : Fin 2) (block : Fin 6) : Real :=
  if branch = 0 then
    if block = 0 then 67472 / 100000000
    else if block = 1 then 190038 / 100000000
    else if block = 2 then 312686 / 100000000
    else if block = 3 then 435724 / 100000000
    else if block = 4 then 559451 / 100000000
    else 684170 / 100000000
  else
    if block = 0 then 227579 / 100000000
    else if block = 1 then 185726 / 100000000
    else if block = 2 then 144266 / 100000000
    else if block = 3 then 103183 / 100000000
    else if block = 4 then 62460 / 100000000
    else 22081 / 100000000

private theorem lowFarShard00 :
    lowFarShardSum 0 0 < 67472 / 100000000 := by
  norm_num [lowFarShardSum, sectionSixFirstLowFarCertificateCell,
    SectionSixFirstLowFarCertificateCell.weight, uniformRealGridLower,
    uniformRealGridUpper, finProdFinEquiv, Fintype.sum_prod_type,
    Fin.sum_univ_succ]

private theorem lowFarShard01 :
    lowFarShardSum 0 1 < 190038 / 100000000 := by
  norm_num [lowFarShardSum, sectionSixFirstLowFarCertificateCell,
    SectionSixFirstLowFarCertificateCell.weight, uniformRealGridLower,
    uniformRealGridUpper, finProdFinEquiv, Fintype.sum_prod_type,
    Fin.sum_univ_succ]

private theorem lowFarShard02 :
    lowFarShardSum 0 2 < 312686 / 100000000 := by
  norm_num [lowFarShardSum, sectionSixFirstLowFarCertificateCell,
    SectionSixFirstLowFarCertificateCell.weight, uniformRealGridLower,
    uniformRealGridUpper, finProdFinEquiv, Fintype.sum_prod_type,
    Fin.sum_univ_succ]

private theorem lowFarShard03 :
    lowFarShardSum 0 3 < 435724 / 100000000 := by
  norm_num [lowFarShardSum, sectionSixFirstLowFarCertificateCell,
    SectionSixFirstLowFarCertificateCell.weight, uniformRealGridLower,
    uniformRealGridUpper, finProdFinEquiv, Fintype.sum_prod_type,
    Fin.sum_univ_succ]

private theorem lowFarShard04 :
    lowFarShardSum 0 4 < 559451 / 100000000 := by
  norm_num [lowFarShardSum, sectionSixFirstLowFarCertificateCell,
    SectionSixFirstLowFarCertificateCell.weight, uniformRealGridLower,
    uniformRealGridUpper, finProdFinEquiv, Fintype.sum_prod_type,
    Fin.sum_univ_succ]

private theorem lowFarShard05 :
    lowFarShardSum 0 5 < 684170 / 100000000 := by
  norm_num [lowFarShardSum, sectionSixFirstLowFarCertificateCell,
    SectionSixFirstLowFarCertificateCell.weight, uniformRealGridLower,
    uniformRealGridUpper, finProdFinEquiv, Fintype.sum_prod_type,
    Fin.sum_univ_succ]

private theorem lowFarShard10 :
    lowFarShardSum 1 0 < 227579 / 100000000 := by
  norm_num [lowFarShardSum, sectionSixFirstLowFarCertificateCell,
    SectionSixFirstLowFarCertificateCell.weight, uniformRealGridLower,
    uniformRealGridUpper, finProdFinEquiv, Fintype.sum_prod_type,
    Fin.sum_univ_succ]

private theorem lowFarShard11 :
    lowFarShardSum 1 1 < 185726 / 100000000 := by
  norm_num [lowFarShardSum, sectionSixFirstLowFarCertificateCell,
    SectionSixFirstLowFarCertificateCell.weight, uniformRealGridLower,
    uniformRealGridUpper, finProdFinEquiv, Fintype.sum_prod_type,
    Fin.sum_univ_succ]

private theorem lowFarShard12 :
    lowFarShardSum 1 2 < 144266 / 100000000 := by
  norm_num [lowFarShardSum, sectionSixFirstLowFarCertificateCell,
    SectionSixFirstLowFarCertificateCell.weight, uniformRealGridLower,
    uniformRealGridUpper, finProdFinEquiv, Fintype.sum_prod_type,
    Fin.sum_univ_succ]

private theorem lowFarShard13 :
    lowFarShardSum 1 3 < 103183 / 100000000 := by
  norm_num [lowFarShardSum, sectionSixFirstLowFarCertificateCell,
    SectionSixFirstLowFarCertificateCell.weight, uniformRealGridLower,
    uniformRealGridUpper, finProdFinEquiv, Fintype.sum_prod_type,
    Fin.sum_univ_succ]

private theorem lowFarShard14 :
    lowFarShardSum 1 4 < 62460 / 100000000 := by
  norm_num [lowFarShardSum, sectionSixFirstLowFarCertificateCell,
    SectionSixFirstLowFarCertificateCell.weight, uniformRealGridLower,
    uniformRealGridUpper, finProdFinEquiv, Fintype.sum_prod_type,
    Fin.sum_univ_succ]

private theorem lowFarShard15 :
    lowFarShardSum 1 5 < 22081 / 100000000 := by
  norm_num [lowFarShardSum, sectionSixFirstLowFarCertificateCell,
    SectionSixFirstLowFarCertificateCell.weight, uniformRealGridLower,
    uniformRealGridUpper, finProdFinEquiv, Fintype.sum_prod_type,
    Fin.sum_univ_succ]

private theorem lowFarShard_lt (branch : Fin 2) (block : Fin 6) :
    lowFarShardSum branch block < lowFarShardUpper branch block := by
  fin_cases branch <;> fin_cases block
  · simpa [lowFarShardUpper] using lowFarShard00
  · simpa [lowFarShardUpper] using lowFarShard01
  · simpa [lowFarShardUpper] using lowFarShard02
  · simpa [lowFarShardUpper] using lowFarShard03
  · simpa [lowFarShardUpper] using lowFarShard04
  · simpa [lowFarShardUpper] using lowFarShard05
  · simpa [lowFarShardUpper] using lowFarShard10
  · simpa [lowFarShardUpper] using lowFarShard11
  · simpa [lowFarShardUpper] using lowFarShard12
  · simpa [lowFarShardUpper] using lowFarShard13
  · simpa [lowFarShardUpper] using lowFarShard14
  · simpa [lowFarShardUpper] using lowFarShard15

private theorem lowFarWeightSum_eq_shards :
    (∑ index : Fin 2 × Fin 60 × Fin 5,
      (sectionSixFirstLowFarCertificateCell index).weight) =
      ∑ branch : Fin 2, ∑ block : Fin 6, lowFarShardSum branch block := by
  calc
    _ = ∑ index : Fin 2 × ((Fin 6 × Fin 10) × Fin 5),
        (sectionSixFirstLowFarCertificateCell
          (lowFarShardIndexEquiv index)).weight :=
      (lowFarShardIndexEquiv.sum_comp
        (fun index => (sectionSixFirstLowFarCertificateCell index).weight)).symm
    _ = _ := by
      simp [lowFarShardIndexEquiv, lowFarShardSum, Fintype.sum_prod_type]

theorem sectionSixFirstLowFarCertificate_weight_sum_lt :
    (∑ index : Fin 2 × Fin 60 × Fin 5,
      (sectionSixFirstLowFarCertificateCell index).weight) <
        (599 : Real) / 20000 := by
  rw [lowFarWeightSum_eq_shards]
  calc
    _ < ∑ branch : Fin 2, ∑ block : Fin 6,
        lowFarShardUpper branch block := by
      apply Finset.sum_lt_sum_of_nonempty (by simp)
      intro branch _
      apply Finset.sum_lt_sum_of_nonempty (by simp)
      intro block _
      exact lowFarShard_lt branch block
    _ < (599 : Real) / 20000 := by
      rw [Fin.sum_univ_two, Fin.sum_univ_six, Fin.sum_univ_six]
      change
        ((67472 / 100000000 + 190038 / 100000000 +
            312686 / 100000000 + 435724 / 100000000 +
            559451 / 100000000 + 684170 / 100000000 : Real) +
          (227579 / 100000000 + 185726 / 100000000 +
            144266 / 100000000 + 103183 / 100000000 +
            62460 / 100000000 + 22081 / 100000000 : Real)) <
          599 / 20000
      norm_num

end

end PrimesRestrictedDigits
