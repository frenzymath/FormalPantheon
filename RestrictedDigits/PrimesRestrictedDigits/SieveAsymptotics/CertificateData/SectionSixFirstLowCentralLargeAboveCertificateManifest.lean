import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateNodes
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstLowCentralLargeAboveCertificateManifest -/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def lowCentralLargeAboveMidpointShardIndexEquiv :
    ((Fin 3 × Fin 20) ⊕ Fin 15) ≃ Fin 15 × Fin 5 :=
  ((Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans
    finSumFinEquiv).trans (@finProdFinEquiv 15 5).symm

private def lowCentralLargeAboveTrapezoidShardIndexEquiv :
    Fin 4 × Fin 20 ≃ Fin 16 × Fin 5 :=
  finProdFinEquiv.trans (@finProdFinEquiv 16 5).symm

private def lowCentralLargeAboveMidpointShardSum
    (branch : Fin 2) (block : Fin 3) : Real :=
  ∑ offset : Fin 20,
    sectionSixFirstLowCentralLargeAboveCertificateNode
      (Sum.inl (Sum.inl
        (branch, lowCentralLargeAboveMidpointShardIndexEquiv
          (Sum.inl (block, offset)))))

private def lowCentralLargeAboveMidpointTailSum (branch : Fin 2) : Real :=
  ∑ offset : Fin 15,
    sectionSixFirstLowCentralLargeAboveCertificateNode
      (Sum.inl (Sum.inl
        (branch, lowCentralLargeAboveMidpointShardIndexEquiv (Sum.inr offset))))

private def lowCentralLargeAboveMiddleShardSum : Real :=
  ∑ coordinate : Fin 2 × Fin 2,
    sectionSixFirstLowCentralLargeAboveCertificateNode
      (Sum.inl (Sum.inr coordinate))

private def lowCentralLargeAboveTrapezoidShardSum
    (branch : Fin 2) (block : Fin 4) : Real :=
  ∑ offset : Fin 20,
    sectionSixFirstLowCentralLargeAboveCertificateNode
      (Sum.inr
        (branch, lowCentralLargeAboveTrapezoidShardIndexEquiv (block, offset)))

private def lowCentralLargeAboveMidpointHalfSum
    (branch : Fin 2) (block : Fin 3) (half : Fin 2) : Real :=
  ∑ offset : Fin 10,
    sectionSixFirstLowCentralLargeAboveCertificateNode
      (Sum.inl (Sum.inl
        (branch, lowCentralLargeAboveMidpointShardIndexEquiv
          (Sum.inl (block, finProdFinEquiv (half, offset))))))

private def lowCentralLargeAboveTrapezoidHalfSum
    (branch : Fin 2) (block : Fin 4) (half : Fin 2) : Real :=
  ∑ offset : Fin 10,
    sectionSixFirstLowCentralLargeAboveCertificateNode
      (Sum.inr
        (branch, lowCentralLargeAboveTrapezoidShardIndexEquiv
          (block, finProdFinEquiv (half, offset))))

private theorem lowCentralLargeAboveMidpointShardSum_eq_halves
    (branch : Fin 2) (block : Fin 3) :
    lowCentralLargeAboveMidpointShardSum branch block =
      ∑ half : Fin 2,
        lowCentralLargeAboveMidpointHalfSum branch block half := by
  unfold lowCentralLargeAboveMidpointShardSum
  calc
    _ = ∑ position : Fin 2 × Fin 10,
        sectionSixFirstLowCentralLargeAboveCertificateNode
          (Sum.inl (Sum.inl
            (branch, lowCentralLargeAboveMidpointShardIndexEquiv
              (Sum.inl (block, finProdFinEquiv position))))) :=
      ((@finProdFinEquiv 2 10).sum_comp (fun offset =>
        sectionSixFirstLowCentralLargeAboveCertificateNode
          (Sum.inl (Sum.inl
            (branch, lowCentralLargeAboveMidpointShardIndexEquiv
              (Sum.inl (block, offset))))))).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type,
        lowCentralLargeAboveMidpointHalfSum]

private theorem lowCentralLargeAboveTrapezoidShardSum_eq_halves
    (branch : Fin 2) (block : Fin 4) :
    lowCentralLargeAboveTrapezoidShardSum branch block =
      ∑ half : Fin 2,
        lowCentralLargeAboveTrapezoidHalfSum branch block half := by
  unfold lowCentralLargeAboveTrapezoidShardSum
  calc
    _ = ∑ position : Fin 2 × Fin 10,
        sectionSixFirstLowCentralLargeAboveCertificateNode
          (Sum.inr
            (branch, lowCentralLargeAboveTrapezoidShardIndexEquiv
              (block, finProdFinEquiv position))) :=
      ((@finProdFinEquiv 2 10).sum_comp (fun offset =>
        sectionSixFirstLowCentralLargeAboveCertificateNode
          (Sum.inr
            (branch, lowCentralLargeAboveTrapezoidShardIndexEquiv
              (block, offset))))).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type,
        lowCentralLargeAboveTrapezoidHalfSum]

local macro "close_lowCentralLargeAboveShard" : tactic =>
  `(tactic|
    norm_num [lowCentralLargeAboveMidpointShardSum,
      lowCentralLargeAboveMidpointTailSum,
      lowCentralLargeAboveMiddleShardSum,
      lowCentralLargeAboveTrapezoidShardSum,
      lowCentralLargeAboveMidpointHalfSum,
      lowCentralLargeAboveTrapezoidHalfSum,
      lowCentralLargeAboveMidpointShardIndexEquiv,
      lowCentralLargeAboveTrapezoidShardIndexEquiv,
      sectionSixFirstLowCentralLargeAboveCertificateNode,
      sectionSixFirstLowCentralLargeAboveTransformedIntegrand,
      finProdFinEquiv, finSumFinEquiv, Fintype.sum_prod_type,
      Fin.sum_univ_succ])

private theorem lowCentralLargeAboveShard0_01Half0 :
    lowCentralLargeAboveMidpointHalfSum 0 1 0 < 3041232064585 / 1000000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard0_01Half1 :
    lowCentralLargeAboveMidpointHalfSum 0 1 1 < 3596417611241 / 1000000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard0_02Half0 :
    lowCentralLargeAboveMidpointHalfSum 0 2 0 < 3789545629074 / 1000000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard0_02Half1 :
    lowCentralLargeAboveMidpointHalfSum 0 2 1 < 3620116847373 / 1000000000000000 := by close_lowCentralLargeAboveShard

private theorem lowCentralLargeAboveShard3_01Half0 :
    lowCentralLargeAboveMidpointHalfSum 1 1 0 < 1006715234401 / 1000000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard3_01Half1 :
    lowCentralLargeAboveMidpointHalfSum 1 1 1 < 1194048308456 / 1000000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard3_02Half0 :
    lowCentralLargeAboveMidpointHalfSum 1 2 0 < 1313830153607 / 1000000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard3_02Half1 :
    lowCentralLargeAboveMidpointHalfSum 1 2 1 < 1367808459870 / 1000000000000000 := by close_lowCentralLargeAboveShard

private theorem lowCentralLargeAboveShard1_01Half0 :
    lowCentralLargeAboveTrapezoidHalfSum 0 1 0 < 529557854873 / 1000000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard1_01Half1 :
    lowCentralLargeAboveTrapezoidHalfSum 0 1 1 < 360924347267 / 1000000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard1_02Half0 :
    lowCentralLargeAboveTrapezoidHalfSum 0 2 0 < 224240544420 / 1000000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard1_02Half1 :
    lowCentralLargeAboveTrapezoidHalfSum 0 2 1 < 119632779901 / 1000000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard1_03Half0 :
    lowCentralLargeAboveTrapezoidHalfSum 0 3 0 < 47468742368 / 1000000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard1_03Half1 :
    lowCentralLargeAboveTrapezoidHalfSum 0 3 1 < 7669348546 / 1000000000000000 := by close_lowCentralLargeAboveShard

private theorem lowCentralLargeAboveShard4_01Half0 :
    lowCentralLargeAboveTrapezoidHalfSum 1 1 0 < 2026275723268 / 1000000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard4_01Half1 :
    lowCentralLargeAboveTrapezoidHalfSum 1 1 1 < 1360174130952 / 1000000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard4_02Half0 :
    lowCentralLargeAboveTrapezoidHalfSum 1 2 0 < 826208251691 / 1000000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard4_02Half1 :
    lowCentralLargeAboveTrapezoidHalfSum 1 2 1 < 422687769950 / 1000000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard4_03Half0 :
    lowCentralLargeAboveTrapezoidHalfSum 1 3 0 < 151433591169 / 1000000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard4_03Half1 :
    lowCentralLargeAboveTrapezoidHalfSum 1 3 1 < 17236707028 / 1000000000000000 := by close_lowCentralLargeAboveShard

private theorem lowCentralLargeAboveShard0_00 :
    lowCentralLargeAboveMidpointShardSum 0 0 <
      2914804797 / 1000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard0_01 :
    lowCentralLargeAboveMidpointShardSum 0 1 <
      6637649676 / 1000000000000 := by
  rw [lowCentralLargeAboveMidpointShardSum_eq_halves, Fin.sum_univ_two]
  linarith [lowCentralLargeAboveShard0_01Half0,
    lowCentralLargeAboveShard0_01Half1]
private theorem lowCentralLargeAboveShard0_02 :
    lowCentralLargeAboveMidpointShardSum 0 2 <
      7409662477 / 1000000000000 := by
  rw [lowCentralLargeAboveMidpointShardSum_eq_halves, Fin.sum_univ_two]
  linarith [lowCentralLargeAboveShard0_02Half0,
    lowCentralLargeAboveShard0_02Half1]
private theorem lowCentralLargeAboveShard0_03 :
    lowCentralLargeAboveMidpointTailSum 0 <
      4294785034 / 1000000000000 := by close_lowCentralLargeAboveShard

private theorem lowCentralLargeAboveShard3_00 :
    lowCentralLargeAboveMidpointShardSum 1 0 <
      1169178005 / 1000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard3_01 :
    lowCentralLargeAboveMidpointShardSum 1 1 <
      2200763543 / 1000000000000 := by
  rw [lowCentralLargeAboveMidpointShardSum_eq_halves, Fin.sum_univ_two]
  linarith [lowCentralLargeAboveShard3_01Half0,
    lowCentralLargeAboveShard3_01Half1]
private theorem lowCentralLargeAboveShard3_02 :
    lowCentralLargeAboveMidpointShardSum 1 2 <
      2681638614 / 1000000000000 := by
  rw [lowCentralLargeAboveMidpointShardSum_eq_halves, Fin.sum_univ_two]
  linarith [lowCentralLargeAboveShard3_02Half0,
    lowCentralLargeAboveShard3_02Half1]
private theorem lowCentralLargeAboveShard3_03 :
    lowCentralLargeAboveMidpointTailSum 1 <
      2011848009 / 1000000000000 := by close_lowCentralLargeAboveShard

private theorem lowCentralLargeAboveShard2_00 :
    lowCentralLargeAboveMiddleShardSum <
      41234424 / 1000000000000 := by close_lowCentralLargeAboveShard

private theorem lowCentralLargeAboveShard1_00 :
    lowCentralLargeAboveTrapezoidShardSum 0 0 <
      1437176825 / 1000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard1_01 :
    lowCentralLargeAboveTrapezoidShardSum 0 1 <
      890482203 / 1000000000000 := by
  rw [lowCentralLargeAboveTrapezoidShardSum_eq_halves, Fin.sum_univ_two]
  linarith [lowCentralLargeAboveShard1_01Half0,
    lowCentralLargeAboveShard1_01Half1]
private theorem lowCentralLargeAboveShard1_02 :
    lowCentralLargeAboveTrapezoidShardSum 0 2 <
      343873325 / 1000000000000 := by
  rw [lowCentralLargeAboveTrapezoidShardSum_eq_halves, Fin.sum_univ_two]
  linarith [lowCentralLargeAboveShard1_02Half0,
    lowCentralLargeAboveShard1_02Half1]
private theorem lowCentralLargeAboveShard1_03 :
    lowCentralLargeAboveTrapezoidShardSum 0 3 <
      55138091 / 1000000000000 := by
  rw [lowCentralLargeAboveTrapezoidShardSum_eq_halves, Fin.sum_univ_two]
  linarith [lowCentralLargeAboveShard1_03Half0,
    lowCentralLargeAboveShard1_03Half1]

private theorem lowCentralLargeAboveShard4_00 :
    lowCentralLargeAboveTrapezoidShardSum 1 0 <
      5601120503 / 1000000000000 := by close_lowCentralLargeAboveShard
private theorem lowCentralLargeAboveShard4_01 :
    lowCentralLargeAboveTrapezoidShardSum 1 1 <
      3386449855 / 1000000000000 := by
  rw [lowCentralLargeAboveTrapezoidShardSum_eq_halves, Fin.sum_univ_two]
  linarith [lowCentralLargeAboveShard4_01Half0,
    lowCentralLargeAboveShard4_01Half1]
private theorem lowCentralLargeAboveShard4_02 :
    lowCentralLargeAboveTrapezoidShardSum 1 2 <
      1248896022 / 1000000000000 := by
  rw [lowCentralLargeAboveTrapezoidShardSum_eq_halves, Fin.sum_univ_two]
  linarith [lowCentralLargeAboveShard4_02Half0,
    lowCentralLargeAboveShard4_02Half1]
private theorem lowCentralLargeAboveShard4_03 :
    lowCentralLargeAboveTrapezoidShardSum 1 3 <
      168670299 / 1000000000000 := by
  rw [lowCentralLargeAboveTrapezoidShardSum_eq_halves, Fin.sum_univ_two]
  linarith [lowCentralLargeAboveShard4_03Half0,
    lowCentralLargeAboveShard4_03Half1]

private theorem lowCentralLargeAboveMidpointNodeSum_eq_shards :
    (∑ index : Fin 2 × Fin 15 × Fin 5,
      sectionSixFirstLowCentralLargeAboveCertificateNode
        (Sum.inl (Sum.inl index))) =
      ∑ branch : Fin 2,
        ((∑ block : Fin 3,
          lowCentralLargeAboveMidpointShardSum branch block) +
            lowCentralLargeAboveMidpointTailSum branch) := by
  calc
    _ = ∑ branch : Fin 2, ∑ coordinate : Fin 15 × Fin 5,
        sectionSixFirstLowCentralLargeAboveCertificateNode
          (Sum.inl (Sum.inl (branch, coordinate))) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ branch : Fin 2,
        ∑ position : (Fin 3 × Fin 20) ⊕ Fin 15,
          sectionSixFirstLowCentralLargeAboveCertificateNode
            (Sum.inl (Sum.inl
              (branch, lowCentralLargeAboveMidpointShardIndexEquiv position))) := by
      apply Finset.sum_congr rfl
      intro branch _
      exact (lowCentralLargeAboveMidpointShardIndexEquiv.sum_comp
        (fun coordinate =>
          sectionSixFirstLowCentralLargeAboveCertificateNode
            (Sum.inl (Sum.inl (branch, coordinate))))).symm
    _ = _ := by
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type,
        lowCentralLargeAboveMidpointShardSum,
        lowCentralLargeAboveMidpointTailSum]

private theorem lowCentralLargeAboveTrapezoidNodeSum_eq_shards :
    (∑ index : Fin 2 × Fin 16 × Fin 5,
      sectionSixFirstLowCentralLargeAboveCertificateNode (Sum.inr index)) =
      ∑ branch : Fin 2, ∑ block : Fin 4,
        lowCentralLargeAboveTrapezoidShardSum branch block := by
  calc
    _ = ∑ branch : Fin 2, ∑ coordinate : Fin 16 × Fin 5,
        sectionSixFirstLowCentralLargeAboveCertificateNode
          (Sum.inr (branch, coordinate)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ branch : Fin 2, ∑ position : Fin 4 × Fin 20,
        sectionSixFirstLowCentralLargeAboveCertificateNode
          (Sum.inr
            (branch, lowCentralLargeAboveTrapezoidShardIndexEquiv position)) := by
      apply Finset.sum_congr rfl
      intro branch _
      exact (lowCentralLargeAboveTrapezoidShardIndexEquiv.sum_comp
        (fun coordinate =>
          sectionSixFirstLowCentralLargeAboveCertificateNode
            (Sum.inr (branch, coordinate)))).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type,
        lowCentralLargeAboveTrapezoidShardSum]

private theorem lowCentralLargeAboveNodeSum_eq_shards :
    (∑ index :
      ((Fin 2 × Fin 15 × Fin 5) ⊕ (Fin 2 × Fin 2)) ⊕
        (Fin 2 × Fin 16 × Fin 5),
      sectionSixFirstLowCentralLargeAboveCertificateNode index) =
      (∑ branch : Fin 2,
        ((∑ block : Fin 3,
          lowCentralLargeAboveMidpointShardSum branch block) +
            lowCentralLargeAboveMidpointTailSum branch)) +
      lowCentralLargeAboveMiddleShardSum +
      ∑ branch : Fin 2, ∑ block : Fin 4,
        lowCentralLargeAboveTrapezoidShardSum branch block := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type,
    lowCentralLargeAboveMidpointNodeSum_eq_shards,
    lowCentralLargeAboveTrapezoidNodeSum_eq_shards]
  rfl

theorem sectionSixFirstLowCentralLargeAboveCertificate_node_sum_lt :
    (∑ index :
      ((Fin 2 × Fin 15 × Fin 5) ⊕ (Fin 2 × Fin 2)) ⊕
        (Fin 2 × Fin 16 × Fin 5),
      sectionSixFirstLowCentralLargeAboveCertificateNode index) <
        (42493371702 : Real) / 1000000000000 := by
  rw [lowCentralLargeAboveNodeSum_eq_shards]
  simp only [Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four]
  linarith [
    lowCentralLargeAboveShard0_00, lowCentralLargeAboveShard0_01,
    lowCentralLargeAboveShard0_02, lowCentralLargeAboveShard0_03,
    lowCentralLargeAboveShard3_00, lowCentralLargeAboveShard3_01,
    lowCentralLargeAboveShard3_02, lowCentralLargeAboveShard3_03,
    lowCentralLargeAboveShard2_00,
    lowCentralLargeAboveShard1_00, lowCentralLargeAboveShard1_01,
    lowCentralLargeAboveShard1_02, lowCentralLargeAboveShard1_03,
    lowCentralLargeAboveShard4_00, lowCentralLargeAboveShard4_01,
    lowCentralLargeAboveShard4_02, lowCentralLargeAboveShard4_03
  ]

end

end PrimesRestrictedDigits
