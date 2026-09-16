import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeTerminalCertificateCells
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstLowCentralLargeTerminalCertificateManifest -/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def lowCentralLargeTerminalShardIndexEquiv :
    Fin 2 × ((Fin 5 × Fin 8) × Fin 20) ≃ Fin 2 × Fin 800 :=
  Equiv.prodCongr (Equiv.refl _) <|
    (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv

private def lowCentralLargeTerminalShardSum
    (branch : Fin 2) (major : Fin 5) (minor : Fin 8) : Real :=
  ∑ offset : Fin 20,
    (sectionSixFirstLowCentralLargeTerminalCertificateCell
      (branch, finProdFinEquiv (finProdFinEquiv (major, minor), offset))).weight

local macro "close_lowCentralLargeTerminalShard" : tactic =>
  `(tactic|
    norm_num [lowCentralLargeTerminalShardSum,
      sectionSixFirstLowCentralLargeTerminalCertificateCell,
      SectionSixFirstLowCentralLargeTerminalCertificateCell.weight,
      cayleyLogSeriesUpper, Finset.sum_range_succ,
      uniformRealGridLower, uniformRealGridUpper, finProdFinEquiv,
      Fin.sum_univ_succ])

private theorem lowCentralLargeTerminalShard0_00 :
    lowCentralLargeTerminalShardSum 0 0 0 < 10332 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_01 :
    lowCentralLargeTerminalShardSum 0 0 1 < 29832 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_02 :
    lowCentralLargeTerminalShardSum 0 0 2 < 49077 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_03 :
    lowCentralLargeTerminalShardSum 0 0 3 < 68075 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_04 :
    lowCentralLargeTerminalShardSum 0 0 4 < 86836 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_05 :
    lowCentralLargeTerminalShardSum 0 0 5 < 105368 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_06 :
    lowCentralLargeTerminalShardSum 0 0 6 < 123679 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_07 :
    lowCentralLargeTerminalShardSum 0 0 7 < 141778 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_08 :
    lowCentralLargeTerminalShardSum 0 1 0 < 159672 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_09 :
    lowCentralLargeTerminalShardSum 0 1 1 < 177368 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_10 :
    lowCentralLargeTerminalShardSum 0 1 2 < 194875 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_11 :
    lowCentralLargeTerminalShardSum 0 1 3 < 212198 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_12 :
    lowCentralLargeTerminalShardSum 0 1 4 < 229346 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_13 :
    lowCentralLargeTerminalShardSum 0 1 5 < 246325 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_14 :
    lowCentralLargeTerminalShardSum 0 1 6 < 263140 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_15 :
    lowCentralLargeTerminalShardSum 0 1 7 < 279799 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_16 :
    lowCentralLargeTerminalShardSum 0 2 0 < 296308 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_17 :
    lowCentralLargeTerminalShardSum 0 2 1 < 312672 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_18 :
    lowCentralLargeTerminalShardSum 0 2 2 < 328898 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_19 :
    lowCentralLargeTerminalShardSum 0 2 3 < 344991 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_20 :
    lowCentralLargeTerminalShardSum 0 2 4 < 360957 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_21 :
    lowCentralLargeTerminalShardSum 0 2 5 < 376801 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_22 :
    lowCentralLargeTerminalShardSum 0 2 6 < 392528 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_23 :
    lowCentralLargeTerminalShardSum 0 2 7 < 408144 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_24 :
    lowCentralLargeTerminalShardSum 0 3 0 < 423654 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_25 :
    lowCentralLargeTerminalShardSum 0 3 1 < 439062 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_26 :
    lowCentralLargeTerminalShardSum 0 3 2 < 454374 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_27 :
    lowCentralLargeTerminalShardSum 0 3 3 < 469593 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_28 :
    lowCentralLargeTerminalShardSum 0 3 4 < 484726 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_29 :
    lowCentralLargeTerminalShardSum 0 3 5 < 499776 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_30 :
    lowCentralLargeTerminalShardSum 0 3 6 < 514748 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_31 :
    lowCentralLargeTerminalShardSum 0 3 7 < 529646 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_32 :
    lowCentralLargeTerminalShardSum 0 4 0 < 544475 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_33 :
    lowCentralLargeTerminalShardSum 0 4 1 < 559239 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_34 :
    lowCentralLargeTerminalShardSum 0 4 2 < 573942 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_35 :
    lowCentralLargeTerminalShardSum 0 4 3 < 588588 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_36 :
    lowCentralLargeTerminalShardSum 0 4 4 < 603182 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_37 :
    lowCentralLargeTerminalShardSum 0 4 5 < 617727 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_38 :
    lowCentralLargeTerminalShardSum 0 4 6 < 632227 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard0_39 :
    lowCentralLargeTerminalShardSum 0 4 7 < 646688 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_00 :
    lowCentralLargeTerminalShardSum 1 0 0 < 636397 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_01 :
    lowCentralLargeTerminalShardSum 1 0 1 < 631512 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_02 :
    lowCentralLargeTerminalShardSum 1 0 2 < 626668 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_03 :
    lowCentralLargeTerminalShardSum 1 0 3 < 621865 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_04 :
    lowCentralLargeTerminalShardSum 1 0 4 < 617101 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_05 :
    lowCentralLargeTerminalShardSum 1 0 5 < 612376 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_06 :
    lowCentralLargeTerminalShardSum 1 0 6 < 607687 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_07 :
    lowCentralLargeTerminalShardSum 1 0 7 < 603035 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_08 :
    lowCentralLargeTerminalShardSum 1 1 0 < 598418 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_09 :
    lowCentralLargeTerminalShardSum 1 1 1 < 593834 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_10 :
    lowCentralLargeTerminalShardSum 1 1 2 < 589284 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_11 :
    lowCentralLargeTerminalShardSum 1 1 3 < 584766 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_12 :
    lowCentralLargeTerminalShardSum 1 1 4 < 580278 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_13 :
    lowCentralLargeTerminalShardSum 1 1 5 < 575821 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_14 :
    lowCentralLargeTerminalShardSum 1 1 6 < 571393 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_15 :
    lowCentralLargeTerminalShardSum 1 1 7 < 566992 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_16 :
    lowCentralLargeTerminalShardSum 1 2 0 < 562619 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_17 :
    lowCentralLargeTerminalShardSum 1 2 1 < 558272 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_18 :
    lowCentralLargeTerminalShardSum 1 2 2 < 553950 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_19 :
    lowCentralLargeTerminalShardSum 1 2 3 < 549653 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_20 :
    lowCentralLargeTerminalShardSum 1 2 4 < 545379 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_21 :
    lowCentralLargeTerminalShardSum 1 2 5 < 541128 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_22 :
    lowCentralLargeTerminalShardSum 1 2 6 < 536898 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_23 :
    lowCentralLargeTerminalShardSum 1 2 7 < 532689 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_24 :
    lowCentralLargeTerminalShardSum 1 3 0 < 528500 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_25 :
    lowCentralLargeTerminalShardSum 1 3 1 < 524330 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_26 :
    lowCentralLargeTerminalShardSum 1 3 2 < 520178 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_27 :
    lowCentralLargeTerminalShardSum 1 3 3 < 516043 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_28 :
    lowCentralLargeTerminalShardSum 1 3 4 < 511924 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_29 :
    lowCentralLargeTerminalShardSum 1 3 5 < 507821 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_30 :
    lowCentralLargeTerminalShardSum 1 3 6 < 503732 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_31 :
    lowCentralLargeTerminalShardSum 1 3 7 < 499658 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_32 :
    lowCentralLargeTerminalShardSum 1 4 0 < 495596 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_33 :
    lowCentralLargeTerminalShardSum 1 4 1 < 491546 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_34 :
    lowCentralLargeTerminalShardSum 1 4 2 < 487507 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_35 :
    lowCentralLargeTerminalShardSum 1 4 3 < 483478 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_36 :
    lowCentralLargeTerminalShardSum 1 4 4 < 479459 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_37 :
    lowCentralLargeTerminalShardSum 1 4 5 < 475448 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_38 :
    lowCentralLargeTerminalShardSum 1 4 6 < 471445 / 100000000 := by close_lowCentralLargeTerminalShard
private theorem lowCentralLargeTerminalShard1_39 :
    lowCentralLargeTerminalShardSum 1 4 7 < 467448 / 100000000 := by close_lowCentralLargeTerminalShard

private theorem lowCentralLargeTerminalBranch0_lt :
    (∑ major : Fin 5, ∑ minor : Fin 8, lowCentralLargeTerminalShardSum 0 major minor) <
      (13780646 : Real) / 100000000 := by
  simp only [Fin.sum_univ_five, Fin.sum_univ_eight]
  linarith [
    lowCentralLargeTerminalShard0_00, lowCentralLargeTerminalShard0_01, lowCentralLargeTerminalShard0_02,
    lowCentralLargeTerminalShard0_03, lowCentralLargeTerminalShard0_04, lowCentralLargeTerminalShard0_05,
    lowCentralLargeTerminalShard0_06, lowCentralLargeTerminalShard0_07, lowCentralLargeTerminalShard0_08,
    lowCentralLargeTerminalShard0_09, lowCentralLargeTerminalShard0_10, lowCentralLargeTerminalShard0_11,
    lowCentralLargeTerminalShard0_12, lowCentralLargeTerminalShard0_13, lowCentralLargeTerminalShard0_14,
    lowCentralLargeTerminalShard0_15, lowCentralLargeTerminalShard0_16, lowCentralLargeTerminalShard0_17,
    lowCentralLargeTerminalShard0_18, lowCentralLargeTerminalShard0_19, lowCentralLargeTerminalShard0_20,
    lowCentralLargeTerminalShard0_21, lowCentralLargeTerminalShard0_22, lowCentralLargeTerminalShard0_23,
    lowCentralLargeTerminalShard0_24, lowCentralLargeTerminalShard0_25, lowCentralLargeTerminalShard0_26,
    lowCentralLargeTerminalShard0_27, lowCentralLargeTerminalShard0_28, lowCentralLargeTerminalShard0_29,
    lowCentralLargeTerminalShard0_30, lowCentralLargeTerminalShard0_31, lowCentralLargeTerminalShard0_32,
    lowCentralLargeTerminalShard0_33, lowCentralLargeTerminalShard0_34, lowCentralLargeTerminalShard0_35,
    lowCentralLargeTerminalShard0_36, lowCentralLargeTerminalShard0_37, lowCentralLargeTerminalShard0_38,
    lowCentralLargeTerminalShard0_39
  ]

private theorem lowCentralLargeTerminalBranch1_lt :
    (∑ major : Fin 5, ∑ minor : Fin 8, lowCentralLargeTerminalShardSum 1 major minor) <
      (21962128 : Real) / 100000000 := by
  simp only [Fin.sum_univ_five, Fin.sum_univ_eight]
  linarith [
    lowCentralLargeTerminalShard1_00, lowCentralLargeTerminalShard1_01, lowCentralLargeTerminalShard1_02,
    lowCentralLargeTerminalShard1_03, lowCentralLargeTerminalShard1_04, lowCentralLargeTerminalShard1_05,
    lowCentralLargeTerminalShard1_06, lowCentralLargeTerminalShard1_07, lowCentralLargeTerminalShard1_08,
    lowCentralLargeTerminalShard1_09, lowCentralLargeTerminalShard1_10, lowCentralLargeTerminalShard1_11,
    lowCentralLargeTerminalShard1_12, lowCentralLargeTerminalShard1_13, lowCentralLargeTerminalShard1_14,
    lowCentralLargeTerminalShard1_15, lowCentralLargeTerminalShard1_16, lowCentralLargeTerminalShard1_17,
    lowCentralLargeTerminalShard1_18, lowCentralLargeTerminalShard1_19, lowCentralLargeTerminalShard1_20,
    lowCentralLargeTerminalShard1_21, lowCentralLargeTerminalShard1_22, lowCentralLargeTerminalShard1_23,
    lowCentralLargeTerminalShard1_24, lowCentralLargeTerminalShard1_25, lowCentralLargeTerminalShard1_26,
    lowCentralLargeTerminalShard1_27, lowCentralLargeTerminalShard1_28, lowCentralLargeTerminalShard1_29,
    lowCentralLargeTerminalShard1_30, lowCentralLargeTerminalShard1_31, lowCentralLargeTerminalShard1_32,
    lowCentralLargeTerminalShard1_33, lowCentralLargeTerminalShard1_34, lowCentralLargeTerminalShard1_35,
    lowCentralLargeTerminalShard1_36, lowCentralLargeTerminalShard1_37, lowCentralLargeTerminalShard1_38,
    lowCentralLargeTerminalShard1_39
  ]

private theorem lowCentralLargeTerminalWeightSum_eq_shards :
    (∑ index : Fin 2 × Fin 800,
      (sectionSixFirstLowCentralLargeTerminalCertificateCell index).weight) =
      ∑ branch : Fin 2, ∑ major : Fin 5, ∑ minor : Fin 8,
        lowCentralLargeTerminalShardSum branch major minor := by
  calc
    _ = ∑ index : Fin 2 × ((Fin 5 × Fin 8) × Fin 20),
        (sectionSixFirstLowCentralLargeTerminalCertificateCell
          (lowCentralLargeTerminalShardIndexEquiv index)).weight :=
      (lowCentralLargeTerminalShardIndexEquiv.sum_comp
        (fun index =>
          (sectionSixFirstLowCentralLargeTerminalCertificateCell index).weight)).symm
    _ = _ := by
      simp [lowCentralLargeTerminalShardIndexEquiv,
        lowCentralLargeTerminalShardSum, Fintype.sum_prod_type]

theorem sectionSixFirstLowCentralLargeTerminalCertificate_weight_sum_lt :
    (∑ index : Fin 2 × Fin 800,
      (sectionSixFirstLowCentralLargeTerminalCertificateCell index).weight) <
        (143 : Real) / 400 := by
  rw [lowCentralLargeTerminalWeightSum_eq_shards, Fin.sum_univ_two]
  linarith [lowCentralLargeTerminalBranch0_lt, lowCentralLargeTerminalBranch1_lt]

end

end PrimesRestrictedDigits
