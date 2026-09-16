import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimesRestrictedDigits.BasicEstimates.ConcaveMidpointUpper
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateConvexity
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell2
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell4
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureY
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.SectionSixFirstLowCentralLargeAboveCertificateManifest
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveRatioCharts
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstUniformIntegralRegions
/-! # SectionSixFirstLowCentralLargeAboveIntegralBound -/
open Filter MeasureTheory Set
namespace PrimesRestrictedDigits
noncomputable section
private def aboveTightLog (r : Real) : Real := let z := (r - 1) / (r + 1); 2 * (z + z ^ 3 / (3 * (1 - z ^ 2)))
private def aboveTightIntegrand (cell : Fin 5) : Real -> Real -> Real := sectionSixFirstLowCentralLargeAboveTransformedIntegrand aboveTightLog cell
private theorem aboveActualFiber_le_tightFiber (cell : Fin 5) {x : Real} (hx : x ∈ Icc (0 : Real) 1) :
    (∫ y in (0 : Real)..1, sectionSixFirstLowCentralLargeAboveTransformedIntegrand
      Real.log cell x y) ≤ ∫ y in (0 : Real)..1, aboveTightIntegrand cell x y := by
  have hp := sectionSixFirstLowCentralLargeAbove_tight_properties cell; dsimp only at hp
  by_cases hactual : IntervalIntegrable
      (sectionSixFirstLowCentralLargeAboveTransformedIntegrand Real.log cell x) volume 0 1
  · exact intervalIntegral.integral_mono_on zero_le_one hactual (hp.2.1 x hx)
      (fun y hy => hp.2.2.2.2 x hx y hy)
  · rw [intervalIntegral.integral_undef hactual]
    exact intervalIntegral.integral_nonneg zero_le_one (fun y hy => hp.2.2.2.1 x hx y hy)
private theorem aboveActualCell_le_tightCell (cell : Fin 5) : (∫ x in (0 : Real)..1, ∫ y in (0 : Real)..1,
      sectionSixFirstLowCentralLargeAboveTransformedIntegrand Real.log cell x y) ≤
      ∫ x in (0 : Real)..1, ∫ y in (0 : Real)..1, aboveTightIntegrand cell x y := by
  have hp := sectionSixFirstLowCentralLargeAbove_tight_properties cell; dsimp only at hp
  by_cases hactual : IntervalIntegrable
      (fun x => ∫ y in (0 : Real)..1,
        sectionSixFirstLowCentralLargeAboveTransformedIntegrand Real.log cell x y) volume 0 1
  · exact intervalIntegral.integral_mono_on zero_le_one hactual hp.2.2.1
      (fun x hx => aboveActualFiber_le_tightFiber cell hx)
  · rw [intervalIntegral.integral_undef hactual]
    exact intervalIntegral.integral_nonneg zero_le_one
      (fun x hx => intervalIntegral.integral_nonneg zero_le_one (fun y hy => hp.2.2.2.1 x hx y hy))
private theorem aboveIntegral_certificateDelta_le_tightIntegrals : sectionSixFirstLowCentralLargeAboveIntegral (1 / 1000000) ≤
      ∑ cell : Fin 5, ∫ x in (0 : Real)..1, ∫ y in (0 : Real)..1,
        aboveTightIntegrand cell x y := by
  refine sectionSixFirstLowCentralLargeAboveIntegral_certificateDelta_le_transformedIntegral.trans ?_
  exact Finset.sum_le_sum fun cell _ => aboveActualCell_le_tightCell cell
private theorem midpoint_fifteen_five_eq (f : Real -> Real -> Real) : midpoint_integral (fun x => midpoint_integral (f x) 5 0 1) 15 0 1 =
      (1 / ((15 : Real) * 5)) * ∑ i : Fin 15, ∑ j : Fin 5,
        f ((2 * (i.val : Real) + 1) / (2 * 15))
          ((2 * (j.val : Real) + 1) / (2 * 5)) := by
  unfold midpoint_integral
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  push_cast; ring
private theorem midpoint_two_two_eq (f : Real -> Real -> Real) :
    midpoint_integral (fun x => midpoint_integral (f x) 2 0 1) 2 0 1 =
      (1 / ((2 : Real) * 2)) * ∑ i : Fin 2, ∑ j : Fin 2,
        f ((2 * (i.val : Real) + 1) / (2 * 2))
          ((2 * (j.val : Real) + 1) / (2 * 2)) := by
  unfold midpoint_integral
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  push_cast; ring
private def aboveEndpointWeight (i : Fin 16) : Real := if i.val = 0 ∨ i.val = 15 then 1 / 2 else 1
private theorem trapezoid_fifteen_midpoint_five_eq (f : Real -> Real -> Real) :
    trapezoidal_integral (fun x => midpoint_integral (f x) 5 0 1) 15 0 1 =
      (1 / ((15 : Real) * 5)) * ∑ i : Fin 16, ∑ j : Fin 5,
        aboveEndpointWeight i * f ((i.val : Real) / 15)
          ((2 * (j.val : Real) + 1) / (2 * 5)) := by
  norm_num [trapezoidal_integral, midpoint_integral, aboveEndpointWeight,
    Fin.sum_univ_succ, Finset.sum_range_succ]
  ring
private theorem midpoint_group_eq_nodes :
    midpoint_integral (fun x => midpoint_integral (aboveTightIntegrand 0 x) 5 0 1) 15 0 1 +
      midpoint_integral (fun x => midpoint_integral (aboveTightIntegrand 3 x) 5 0 1) 15 0 1 =
      ∑ index : Fin 2 × Fin 15 × Fin 5,
        sectionSixFirstLowCentralLargeAboveCertificateNode (Sum.inl (Sum.inl index)) := by
  rw [midpoint_fifteen_five_eq, midpoint_fifteen_five_eq,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  congr 1
  · rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i hi; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j hj
    change _ = aboveTightIntegrand 0
      ((2 * (i.val : Real) + 1) / (2 * 15))
      ((2 * (j.val : Real) + 1) / (2 * 5)) / ((15 : Real) * 5)
    ring
  · rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i hi; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j hj
    change _ = aboveTightIntegrand 3
      ((2 * (i.val : Real) + 1) / (2 * 15))
      ((2 * (j.val : Real) + 1) / (2 * 5)) / ((15 : Real) * 5)
    ring
private theorem middle_group_eq_nodes :
    midpoint_integral (fun x => midpoint_integral (aboveTightIntegrand 2 x) 2 0 1) 2 0 1 =
      ∑ index : Fin 2 × Fin 2,
        sectionSixFirstLowCentralLargeAboveCertificateNode (Sum.inl (Sum.inr index)) := by
  rw [midpoint_two_two_eq, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i hi; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j hj
  change _ = aboveTightIntegrand 2
    ((2 * (i.val : Real) + 1) / (2 * 2))
    ((2 * (j.val : Real) + 1) / (2 * 2)) / ((2 : Real) * 2)
  ring
private theorem trapezoid_group_eq_nodes :
    trapezoidal_integral (fun x => midpoint_integral (aboveTightIntegrand 1 x) 5 0 1) 15 0 1 +
      trapezoidal_integral (fun x => midpoint_integral (aboveTightIntegrand 4 x) 5 0 1) 15 0 1 =
      ∑ index : Fin 2 × Fin 16 × Fin 5,
        sectionSixFirstLowCentralLargeAboveCertificateNode (Sum.inr index) := by
  rw [trapezoid_fifteen_midpoint_five_eq, trapezoid_fifteen_midpoint_five_eq,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  congr 1
  · rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i hi; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j hj
    change _ = aboveEndpointWeight i * aboveTightIntegrand 1
      ((i.val : Real) / 15)
      ((2 * (j.val : Real) + 1) / (2 * 5)) / ((15 : Real) * 5)
    ring
  · rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i hi; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j hj
    change _ = aboveEndpointWeight i * aboveTightIntegrand 4
      ((i.val : Real) / 15)
      ((2 * (j.val : Real) + 1) / (2 * 5)) / ((15 : Real) * 5)
    ring
private theorem all_quadrature_eq_nodes :
    midpoint_integral (fun x => midpoint_integral (aboveTightIntegrand 0 x) 5 0 1) 15 0 1 +
      midpoint_integral (fun x => midpoint_integral (aboveTightIntegrand 3 x) 5 0 1) 15 0 1 +
      midpoint_integral (fun x => midpoint_integral (aboveTightIntegrand 2 x) 2 0 1) 2 0 1 +
      trapezoidal_integral (fun x => midpoint_integral (aboveTightIntegrand 1 x) 5 0 1) 15 0 1 +
      trapezoidal_integral (fun x => midpoint_integral (aboveTightIntegrand 4 x) 5 0 1) 15 0 1 =
      ∑ index : ((Fin 2 × Fin 15 × Fin 5) ⊕ (Fin 2 × Fin 2)) ⊕ (Fin 2 × Fin 16 × Fin 5),
        sectionSixFirstLowCentralLargeAboveCertificateNode index := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type,
    ← midpoint_group_eq_nodes, ← middle_group_eq_nodes, ← trapezoid_group_eq_nodes]
  ring
private theorem tight_iterated_le_midpoint
    (cell : Fin 5) (Nx Ny : Nat) (hNx : 0 < Nx) (hNy : 0 < Ny)
    (hconcX : ∀ y ∈ Icc (0 : Real) 1,
      ConcaveOn Real (Icc (0 : Real) 1) (fun x => aboveTightIntegrand cell x y)) :
    (∫ x in (0 : Real)..1, ∫ y in (0 : Real)..1,
        aboveTightIntegrand cell x y) <=
      midpoint_integral (fun x => midpoint_integral (aboveTightIntegrand cell x) Ny 0 1) Nx 0 1 := by
  have hp := sectionSixFirstLowCentralLargeAbove_tight_properties cell; dsimp only at hp
  apply iteratedIntervalIntegral_le_tensorCompositeMidpoint_of_separatelyConcaveOn
    zero_le_one zero_le_one hNx hNy hconcX
  · intro x hx
    have hy := sectionSixFirstLowCentralLargeAbove_tight_concaveOn_y cell x hx
    change ConcaveOn Real (Icc (0 : Real) 1)
      (fun y => sectionSixFirstLowCentralLargeAboveTransformedIntegrand
        aboveTightLog cell x y)
    exact hy
  · exact hp.2.1
  · exact hp.2.2.1
private theorem tight_iterated_le_trapezoid_midpoint
    (cell : Fin 5)
    (hconvX : ∀ y ∈ Icc (0 : Real) 1,
      ConvexOn Real (Icc (0 : Real) 1) (fun x => aboveTightIntegrand cell x y)) :
    (∫ x in (0 : Real)..1, ∫ y in (0 : Real)..1,
        aboveTightIntegrand cell x y) <=
      trapezoidal_integral (fun x => midpoint_integral (aboveTightIntegrand cell x) 5 0 1) 15 0 1 := by
  have hp := sectionSixFirstLowCentralLargeAbove_tight_properties cell; dsimp only at hp
  apply iteratedIntervalIntegral_le_tensorTrapezoidalCompositeMidpoint_of_convexOn_concaveOn
    zero_le_one zero_le_one (by norm_num) (by norm_num) hconvX
  · intro x hx
    have hy := sectionSixFirstLowCentralLargeAbove_tight_concaveOn_y cell x hx
    change ConcaveOn Real (Icc (0 : Real) 1)
      (fun y => sectionSixFirstLowCentralLargeAboveTransformedIntegrand
        aboveTightLog cell x y)
    exact hy
  · exact hp.2.1
  · exact hp.2.2.1
private theorem tight_sum_le_nodes
    (h0 : ∀ y ∈ Icc (0 : Real) 1,
      ConcaveOn Real (Icc (0 : Real) 1) (fun x => aboveTightIntegrand 0 x y))
    (h1 : ∀ y ∈ Icc (0 : Real) 1,
      ConvexOn Real (Icc (0 : Real) 1) (fun x => aboveTightIntegrand 1 x y))
    (h2 : ∀ y ∈ Icc (0 : Real) 1,
      ConcaveOn Real (Icc (0 : Real) 1) (fun x => aboveTightIntegrand 2 x y))
    (h3 : ∀ y ∈ Icc (0 : Real) 1,
      ConcaveOn Real (Icc (0 : Real) 1) (fun x => aboveTightIntegrand 3 x y))
    (h4 : ∀ y ∈ Icc (0 : Real) 1,
      ConvexOn Real (Icc (0 : Real) 1) (fun x => aboveTightIntegrand 4 x y)) :
    (∑ cell : Fin 5, ∫ x in (0 : Real)..1, ∫ y in (0 : Real)..1,
        aboveTightIntegrand cell x y) ≤
      ∑ index : ((Fin 2 × Fin 15 × Fin 5) ⊕ (Fin 2 × Fin 2)) ⊕
        (Fin 2 × Fin 16 × Fin 5),
        sectionSixFirstLowCentralLargeAboveCertificateNode index := by
  have hcell0 := tight_iterated_le_midpoint 0 15 5 (by norm_num) (by norm_num) h0
  have hcell1 := tight_iterated_le_trapezoid_midpoint 1 h1
  have hcell2 := tight_iterated_le_midpoint 2 2 2 (by norm_num) (by norm_num) h2
  have hcell3 := tight_iterated_le_midpoint 3 15 5 (by norm_num) (by norm_num) h3
  have hcell4 := tight_iterated_le_trapezoid_midpoint 4 h4
  have hsum :
      (∑ cell : Fin 5, ∫ x in (0 : Real)..1, ∫ y in (0 : Real)..1,
          aboveTightIntegrand cell x y) =
        (∫ x in (0 : Real)..1, ∫ y in (0 : Real)..1, aboveTightIntegrand 0 x y) +
        ((∫ x in (0 : Real)..1, ∫ y in (0 : Real)..1, aboveTightIntegrand 1 x y) +
        ((∫ x in (0 : Real)..1, ∫ y in (0 : Real)..1, aboveTightIntegrand 2 x y) +
        ((∫ x in (0 : Real)..1, ∫ y in (0 : Real)..1, aboveTightIntegrand 3 x y) +
          (∫ x in (0 : Real)..1, ∫ y in (0 : Real)..1, aboveTightIntegrand 4 x y)))) := by
    simp [Fin.sum_univ_succ]
  calc
    (∑ cell : Fin 5, ∫ x in (0 : Real)..1, ∫ y in (0 : Real)..1,
        aboveTightIntegrand cell x y) = _ := hsum
    _ ≤
      midpoint_integral (fun x => midpoint_integral (aboveTightIntegrand 0 x) 5 0 1) 15 0 1 +
        midpoint_integral (fun x => midpoint_integral (aboveTightIntegrand 3 x) 5 0 1) 15 0 1 +
        midpoint_integral (fun x => midpoint_integral (aboveTightIntegrand 2 x) 2 0 1) 2 0 1 +
        trapezoidal_integral (fun x => midpoint_integral (aboveTightIntegrand 1 x) 5 0 1) 15 0 1 +
        trapezoidal_integral (fun x => midpoint_integral (aboveTightIntegrand 4 x) 5 0 1) 15 0 1 := by
      linarith
    _ = ∑ index : ((Fin 2 × Fin 15 × Fin 5) ⊕ (Fin 2 × Fin 2)) ⊕
        (Fin 2 × Fin 16 × Fin 5),
        sectionSixFirstLowCentralLargeAboveCertificateNode index := by
      convert all_quadrature_eq_nodes using 1
private def aboveDelta : Real := 1 / 1000000
private theorem aboveKernel_integrableOn_delta :
    IntegrableOn sectionSixFirstLowCentralLargeAboveKernel
      (sectionSixFirstLowCentralLargeAboveRegion aboveDelta) := by
  let extension := sectionSixFirstLowCentralLargeBelowKernelExtension
    aboveDelta (by norm_num [aboveDelta]) (by norm_num [aboveDelta])
  have hext : IntegrableOn (fun z => extension z)
      ((Icc (sectionSixThetaGap aboveDelta) (1 / 2) ×ˢ
        Icc (sectionSixThetaGap aboveDelta) (1 / 2)) ×ˢ Icc (sectionSixThetaGap aboveDelta) (1 / 2)) :=
    extension.continuous.continuousOn.integrableOn_compact
      ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc)
  have hsubset : sectionSixFirstLowCentralLargeAboveRegion aboveDelta ⊆
      ((Icc (sectionSixThetaGap aboveDelta) (1 / 2) ×ˢ
        Icc (sectionSixThetaGap aboveDelta) (1 / 2)) ×ˢ Icc (sectionSixThetaGap aboveDelta) (1 / 2)) := by
    intro z hz
    rcases sectionSixFirstLowCentralLargeAboveRegion_subset_logBox
      aboveDelta (by norm_num [aboveDelta]) (by norm_num [aboveDelta]) hz with
      ⟨⟨hu, hv⟩, hw⟩
    exact ⟨⟨⟨hu.1.le, hu.2⟩, ⟨hv.1.le, hv.2⟩⟩, ⟨hw.1.le, hw.2⟩⟩
  apply (hext.mono_set hsubset).congr_fun
  · simpa [extension] using
      sectionSixFirstLowCentralLargeAboveKernelExtension_eq_on_region
        aboveDelta (by norm_num [aboveDelta]) (by norm_num [aboveDelta])
  · exact measurableSet_sectionSixFirstLowCentralLargeAboveRegion aboveDelta
private theorem aboveKernel_nonneg_on_delta {z : (Real × Real) × Real}
    (hz : z ∈ sectionSixFirstLowCentralLargeAboveRegion aboveDelta) :
    0 ≤ sectionSixFirstLowCentralLargeAboveKernel z := by
  rcases hz with ⟨hgap, horder, _, _, _, _, _, hvw, hcap, _⟩
  have hgapPos : 0 < sectionSixThetaGap aboveDelta :=
    (sectionSix_parameter_bounds (by norm_num [aboveDelta]) (by norm_num [aboveDelta])).1
  have hv : 0 < z.1.2 := hgapPos.trans hgap
  have hu : 0 < z.1.1 := hv.trans_le horder
  have hw : 0 < z.2 := hv.trans hvw
  have harg : 1 ≤ (1 - z.1.1 - z.1.2 - z.2) / z.2 := by rw [le_div_iff₀ hw]; linarith
  have homega := (buchstabFunction_mem_Icc harg).1
  unfold sectionSixFirstLowCentralLargeAboveKernel sectionSixFirstLowCentralLargeBelowKernel
  exact div_nonneg (by linarith [homega])
    (mul_nonneg (mul_nonneg hu.le hv.le) (sq_nonneg _))
private theorem aboveIntegral_le_delta {epsilon : Real}
    (hepsilonUpper : epsilon ≤ 1 / 1000000) :
    sectionSixFirstLowCentralLargeAboveIntegral epsilon ≤
      sectionSixFirstLowCentralLargeAboveIntegral aboveDelta := by
  have hepsilonDelta : epsilon ≤ aboveDelta := by
    simpa [aboveDelta] using hepsilonUpper
  have hnonneg : 0 ≤ᵐ[volume.restrict
      (sectionSixFirstLowCentralLargeAboveRegion aboveDelta)]
      sectionSixFirstLowCentralLargeAboveKernel := by
    filter_upwards [ae_restrict_mem (measurableSet_sectionSixFirstLowCentralLargeAboveRegion
      aboveDelta)] with x hx
    exact aboveKernel_nonneg_on_delta hx
  unfold sectionSixFirstLowCentralLargeAboveIntegral
  exact setIntegral_mono_set aboveKernel_integrableOn_delta hnonneg
    (Filter.Eventually.of_forall (sectionSixFirstLowCentralLargeAboveRegion_mono hepsilonDelta))
theorem sectionSixFirstLowCentralLargeAboveIntegral_certificateDelta_le_node_sum :
    sectionSixFirstLowCentralLargeAboveIntegral (1 / 1000000) <=
      ∑ index :
        ((Fin 2 × Fin 15 × Fin 5) ⊕ (Fin 2 × Fin 2)) ⊕
          (Fin 2 × Fin 16 × Fin 5),
        sectionSixFirstLowCentralLargeAboveCertificateNode index := by
  refine aboveIntegral_certificateDelta_le_tightIntegrals.trans ?_
  apply tight_sum_le_nodes
  · intro y hy
    change ConcaveOn Real (Icc (0 : Real) 1) (fun x => sectionSixFirstLowCentralLargeAboveTransformedIntegrand aboveTightLog 0 x y)
    exact sectionSixFirstLowCentralLargeAbove_tight_concaveOn_x_cell0 y hy
  · intro y hy
    change ConvexOn Real (Icc (0 : Real) 1) (fun x => sectionSixFirstLowCentralLargeAboveTransformedIntegrand aboveTightLog 1 x y)
    exact sectionSixFirstLowCentralLargeAbove_tight_convexOn_x_cell1 y hy
  · intro y hy
    change ConcaveOn Real (Icc (0 : Real) 1) (fun x => sectionSixFirstLowCentralLargeAboveTransformedIntegrand aboveTightLog 2 x y)
    exact sectionSixFirstLowCentralLargeAbove_tight_concaveOn_x_cell2 y hy
  · intro y hy
    change ConcaveOn Real (Icc (0 : Real) 1) (fun x => sectionSixFirstLowCentralLargeAboveTransformedIntegrand aboveTightLog 3 x y)
    exact sectionSixFirstLowCentralLargeAbove_tight_concaveOn_x_cell3 y hy
  · intro y hy
    change ConvexOn Real (Icc (0 : Real) 1) (fun x => sectionSixFirstLowCentralLargeAboveTransformedIntegrand aboveTightLog 4 x y)
    exact sectionSixFirstLowCentralLargeAbove_tight_convexOn_x_cell4 y hy
theorem sectionSixFirstLowCentralLargeAboveIntegral_lt {epsilon : Real}
    (hepsilonUpper : epsilon <= 1 / 1000000) :
    sectionSixFirstLowCentralLargeAboveIntegral epsilon <
      (17 : Real) / 400 := by
  calc
    sectionSixFirstLowCentralLargeAboveIntegral epsilon ≤
        sectionSixFirstLowCentralLargeAboveIntegral aboveDelta :=
      aboveIntegral_le_delta hepsilonUpper
    _ ≤ ∑ index :
        ((Fin 2 × Fin 15 × Fin 5) ⊕ (Fin 2 × Fin 2)) ⊕
          (Fin 2 × Fin 16 × Fin 5),
        sectionSixFirstLowCentralLargeAboveCertificateNode index := by
      simpa [aboveDelta] using sectionSixFirstLowCentralLargeAboveIntegral_certificateDelta_le_node_sum
    _ < (42493371702 : Real) / 1000000000000 :=
      sectionSixFirstLowCentralLargeAboveCertificate_node_sum_lt
    _ < (17 : Real) / 400 := by norm_num
end
end PrimesRestrictedDigits
