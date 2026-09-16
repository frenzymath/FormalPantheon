import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBelowCertificateNodes
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstLowCentralLargeBelowCertificateManifest -/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def lowCentralLargeBelowShardIndexEquiv :
    ((Fin 10 × Fin 20) ⊕ Fin 3) ≃ Fin 29 × Fin 7 :=
  ((Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans
    finSumFinEquiv).trans (@finProdFinEquiv 29 7).symm

private def lowCentralLargeBelowShardSum
    (branch : Fin 2) (block : Fin 10) : Real :=
  ∑ offset : Fin 20,
    sectionSixFirstLowCentralLargeBelowCertificateNode
      (branch, lowCentralLargeBelowShardIndexEquiv (Sum.inl (block, offset)))

private def lowCentralLargeBelowTailSum (branch : Fin 2) : Real :=
  ∑ offset : Fin 3,
    sectionSixFirstLowCentralLargeBelowCertificateNode
      (branch, lowCentralLargeBelowShardIndexEquiv (Sum.inr offset))

local macro "close_lowCentralLargeBelowShard" : tactic =>
  `(tactic|
    norm_num [lowCentralLargeBelowShardSum, lowCentralLargeBelowTailSum,
      lowCentralLargeBelowShardIndexEquiv,
      sectionSixFirstLowCentralLargeBelowCertificateNode,
      sectionSixFirstLowCentralLargeBelowTransformedIntegrand,
      cayleyLogSeriesUpper, finProdFinEquiv, finSumFinEquiv,
      Fin.sum_univ_succ])

private theorem lowCentralLargeBelow_sum_univ_ten (f : Fin 10 -> Real) :
    (∑ i, f i) =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  change (∑ i : Fin (8 + 2), f i) = _
  rw [Fin.sum_univ_add, Fin.sum_univ_eight, Fin.sum_univ_two]
  rw [show Fin.castAdd 2 (0 : Fin 8) = (0 : Fin 10) by apply Fin.ext; rfl,
    show Fin.castAdd 2 (1 : Fin 8) = (1 : Fin 10) by apply Fin.ext; rfl,
    show Fin.castAdd 2 (2 : Fin 8) = (2 : Fin 10) by apply Fin.ext; rfl,
    show Fin.castAdd 2 (3 : Fin 8) = (3 : Fin 10) by apply Fin.ext; rfl,
    show Fin.castAdd 2 (4 : Fin 8) = (4 : Fin 10) by apply Fin.ext; rfl,
    show Fin.castAdd 2 (5 : Fin 8) = (5 : Fin 10) by apply Fin.ext; rfl,
    show Fin.castAdd 2 (6 : Fin 8) = (6 : Fin 10) by apply Fin.ext; rfl,
    show Fin.castAdd 2 (7 : Fin 8) = (7 : Fin 10) by apply Fin.ext; rfl,
    show Fin.natAdd 8 (0 : Fin 2) = (8 : Fin 10) by apply Fin.ext; rfl,
    show Fin.natAdd 8 (1 : Fin 2) = (9 : Fin 10) by apply Fin.ext; rfl]
  ring

private theorem lowCentralLargeBelowShard0_00 :
    lowCentralLargeBelowShardSum 0 0 < 6613181 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard0_01 :
    lowCentralLargeBelowShardSum 0 1 < 63516985 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard0_02 :
    lowCentralLargeBelowShardSum 0 2 < 185726807 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard0_03 :
    lowCentralLargeBelowShardSum 0 3 < 372182406 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard0_04 :
    lowCentralLargeBelowShardSum 0 4 < 621999407 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard0_05 :
    lowCentralLargeBelowShardSum 0 5 < 934023837 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard0_06 :
    lowCentralLargeBelowShardSum 0 6 < 1375762030 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard0_07 :
    lowCentralLargeBelowShardSum 0 7 < 1932288379 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard0_08 :
    lowCentralLargeBelowShardSum 0 8 < 2490163884 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard0_09 :
    lowCentralLargeBelowShardSum 0 9 < 2741695426 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard0_10 :
    lowCentralLargeBelowTailSum 0 < 190790547 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard1_00 :
    lowCentralLargeBelowShardSum 1 0 < 2229104 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard1_01 :
    lowCentralLargeBelowShardSum 1 1 < 21651538 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard1_02 :
    lowCentralLargeBelowShardSum 1 2 < 62244709 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard1_03 :
    lowCentralLargeBelowShardSum 1 3 < 121486395 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard1_04 :
    lowCentralLargeBelowShardSum 1 4 < 196913789 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard1_05 :
    lowCentralLargeBelowShardSum 1 5 < 286007548 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard1_06 :
    lowCentralLargeBelowShardSum 1 6 < 416582435 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard1_07 :
    lowCentralLargeBelowShardSum 1 7 < 600077083 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard1_08 :
    lowCentralLargeBelowShardSum 1 8 < 773729620 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard1_09 :
    lowCentralLargeBelowShardSum 1 9 < 812331302 / 1000000000000 := by close_lowCentralLargeBelowShard
private theorem lowCentralLargeBelowShard1_10 :
    lowCentralLargeBelowTailSum 1 < 29520657 / 1000000000000 := by close_lowCentralLargeBelowShard

private theorem lowCentralLargeBelowBranch0_lt :
    (∑ block : Fin 10, lowCentralLargeBelowShardSum 0 block) +
        lowCentralLargeBelowTailSum 0 <
      (10914762889 : Real) / 1000000000000 := by
  rw [lowCentralLargeBelow_sum_univ_ten]
  linarith [
    lowCentralLargeBelowShard0_00, lowCentralLargeBelowShard0_01, lowCentralLargeBelowShard0_02,
    lowCentralLargeBelowShard0_03, lowCentralLargeBelowShard0_04, lowCentralLargeBelowShard0_05,
    lowCentralLargeBelowShard0_06, lowCentralLargeBelowShard0_07, lowCentralLargeBelowShard0_08,
    lowCentralLargeBelowShard0_09, lowCentralLargeBelowShard0_10
  ]

private theorem lowCentralLargeBelowBranch1_lt :
    (∑ block : Fin 10, lowCentralLargeBelowShardSum 1 block) +
        lowCentralLargeBelowTailSum 1 <
      (3322774180 : Real) / 1000000000000 := by
  rw [lowCentralLargeBelow_sum_univ_ten]
  linarith [
    lowCentralLargeBelowShard1_00, lowCentralLargeBelowShard1_01, lowCentralLargeBelowShard1_02,
    lowCentralLargeBelowShard1_03, lowCentralLargeBelowShard1_04, lowCentralLargeBelowShard1_05,
    lowCentralLargeBelowShard1_06, lowCentralLargeBelowShard1_07, lowCentralLargeBelowShard1_08,
    lowCentralLargeBelowShard1_09, lowCentralLargeBelowShard1_10
  ]

private theorem lowCentralLargeBelowNodeSum_eq_shards :
    (∑ index : Fin 2 × Fin 29 × Fin 7,
      sectionSixFirstLowCentralLargeBelowCertificateNode index) =
      ∑ branch : Fin 2,
        ((∑ block : Fin 10, lowCentralLargeBelowShardSum branch block) +
          lowCentralLargeBelowTailSum branch) := by
  calc
    _ = ∑ branch : Fin 2, ∑ coordinate : Fin 29 × Fin 7,
        sectionSixFirstLowCentralLargeBelowCertificateNode
          (branch, coordinate) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ branch : Fin 2,
        ∑ position : (Fin 10 × Fin 20) ⊕ Fin 3,
          sectionSixFirstLowCentralLargeBelowCertificateNode
            (branch, lowCentralLargeBelowShardIndexEquiv position) := by
      apply Finset.sum_congr rfl
      intro branch _
      exact (lowCentralLargeBelowShardIndexEquiv.sum_comp
        (fun coordinate =>
          sectionSixFirstLowCentralLargeBelowCertificateNode
            (branch, coordinate))).symm
    _ = _ := by
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type,
        lowCentralLargeBelowShardSum, lowCentralLargeBelowTailSum]

theorem sectionSixFirstLowCentralLargeBelowCertificate_node_sum_lt :
    (∑ index : Fin 2 × Fin 29 × Fin 7,
      sectionSixFirstLowCentralLargeBelowCertificateNode index) <
        (14237537080 : Real) / 1000000000000 := by
  rw [lowCentralLargeBelowNodeSum_eq_shards, Fin.sum_univ_two]
  linarith [lowCentralLargeBelowBranch0_lt, lowCentralLargeBelowBranch1_lt]

end

end PrimesRestrictedDigits
