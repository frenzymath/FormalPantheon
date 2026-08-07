import BoundedGaps.Maynard.MaynardS2CoordinateOneGoodFiberSum
import BoundedGaps.Maynard.MaynardS2OuterTupleFactorization
import BoundedGaps.Maynard.MaynardS2OuterTupleBoxFactorization

noncomputable section

namespace BoundedGaps.Maynard

open Finset
open scoped BigOperators

def maynardS2OuterCoordinateOneFaceBox
    {H : Finset ℕ} (R D : ℕ) (m : H) : Finset (H → ℕ) :=
  squarefreeCoprimeTupleBox H (primorial D)
    (fun h => if h = m then 1 else R)

theorem maynardS2OuterSquarefreeMean_one (W : ℕ) :
    maynardS2OuterSquarefreeMean W 1 = 1 := by
  unfold maynardS2OuterSquarefreeMean
  rw [show Finset.Icc 1 1 = {1} by ext n; simp]
  simp only [Finset.sum_singleton]
  exact (maynardS2OuterSquarefreeAF_isMultiplicative W).map_one

set_option maxRecDepth 4000 in
theorem mem_maynardS2OuterCoordinateOneFaceBox_of_goodSupport
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hr : r ∈ engelsmaS2CoordinateFiberGoodSupport R D m) :
    r ∈ maynardS2OuterCoordinateOneFaceBox R D m := by
  rw [maynardS2OuterCoordinateOneFaceBox, squarefreeCoprimeTupleBox,
    Fintype.mem_piFinset]
  intro h
  have hrData := Finset.mem_filter.mp hr
  have htuple := isMaynardDivisorTuple_of_mem_support hrData.1
  have hbox := (mem_maynardDivisorTupleSupport_iff.mp hrData.1).1
  have hcoord := (mem_maynardDivisorTupleBox_iff.mp hbox) h
  by_cases hhm : h = m
  · subst h
    have hrm : r m = 1 := hrData.2.1
    rw [if_pos rfl]
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
      ⟨by simp [hrData.2.1], by simp [hrData.2.1]⟩⟩
  · apply Finset.mem_filter.mpr
    rw [if_neg hhm]
    exact ⟨Finset.mem_Icc.mpr ⟨hcoord.1, hcoord.2.le⟩,
      ⟨htuple.coordinate_squarefree h, htuple.coordinate_coprime_W h⟩⟩

set_option maxRecDepth 4000 in
theorem engelsmaS2CoordinateFiberGoodSupport_subset_outerFaceBox
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) :
    engelsmaS2CoordinateFiberGoodSupport R D m ⊆
      maynardS2OuterCoordinateOneFaceBox R D m := by
  intro r hr
  exact mem_maynardS2OuterCoordinateOneFaceBox_of_goodSupport m hr

theorem maynardS2OuterCoordinateOneFaceBox_sum_eq_prod_offCoordinateMeans
    {H : Finset ℕ} {R D : ℕ} (m : H) :
    (∑ r ∈ maynardS2OuterCoordinateOneFaceBox R D m,
      ∏ h : H, maynardS2OuterSquarefreeAF (primorial D) (r h)) =
      ∏ h : H, maynardS2OuterSquarefreeMean (primorial D)
        (if h = m then 1 else R) := by
  exact maynardS2OuterSquarefreeTupleBox_sum_eq_prod_mean

theorem maynardS2OuterCoordinateOneFaceBox_sum_eq_erase_prod_mean
    {H : Finset ℕ} {R D : ℕ} (m : H) :
    (∑ r ∈ maynardS2OuterCoordinateOneFaceBox R D m,
      ∏ h : H, maynardS2OuterSquarefreeAF (primorial D) (r h)) =
      ∏ _h ∈ Finset.univ.erase m,
        maynardS2OuterSquarefreeMean (primorial D) R := by
  rw [maynardS2OuterCoordinateOneFaceBox_sum_eq_prod_offCoordinateMeans]
  calc
    (∏ h : H, maynardS2OuterSquarefreeMean (primorial D)
        (if h = m then 1 else R)) =
        maynardS2OuterSquarefreeMean (primorial D) 1 *
          ∏ h ∈ Finset.univ.erase m,
            maynardS2OuterSquarefreeMean (primorial D)
              (if h = m then 1 else R) := by
      simpa using (Finset.mul_prod_erase Finset.univ
        (fun h : H => maynardS2OuterSquarefreeMean (primorial D)
          (if h = m then 1 else R)) (Finset.mem_univ m)).symm
    _ = ∏ h ∈ Finset.univ.erase m,
          maynardS2OuterSquarefreeMean (primorial D) R := by
      rw [maynardS2OuterSquarefreeMean_one]
      simp only [one_mul]
      apply Finset.prod_congr rfl
      intro h hh
      have hne := (Finset.mem_erase.mp hh).1
      simp [hne]

set_option maxRecDepth 5000 in
theorem engelsmaS2CoordinateFiberGoodOuterMoment_le_faceBox_mul
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple) {B : ℝ}
    (hB : 0 ≤ B)
    (hpoint : ∀ r ∈ engelsmaS2CoordinateFiberGoodSupport R D m,
      ((Real.log R) *
        (∫ x in (0 : ℝ)..(
          Real.log (maynardS2CoordinateFiberEndpoint R
            (maynardS2OffCoordinateProduct
              BoundedGaps.engelsmaTuple m r)) / Real.log R),
          engelsmaS2CoordinateFiberPolynomialTest R m r x)) ^ 2 ≤ B) :
    engelsmaS2CoordinateFiberGoodOuterMoment R D m ≤
      B * ∏ _h ∈ Finset.univ.erase m,
        maynardS2OuterSquarefreeMean (primorial D) R := by
  let G := engelsmaS2CoordinateFiberGoodSupport R D m
  let F := fun r : BoundedGaps.engelsmaTuple → ℕ =>
    ∏ h : BoundedGaps.engelsmaTuple,
      maynardS2OuterSquarefreeAF (primorial D) (r h)
  let I := fun r : BoundedGaps.engelsmaTuple → ℕ =>
    ((Real.log R) *
      (∫ x in (0 : ℝ)..(
        Real.log (maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct
            BoundedGaps.engelsmaTuple m r)) / Real.log R),
        engelsmaS2CoordinateFiberPolynomialTest R m r x)) ^ 2
  have hrewrite : ∀ r ∈ G,
      maynardS2OuterSquarefreeAF (primorial D)
          (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) = F r := by
    intro r hr
    have hrData := Finset.mem_filter.mp hr
    have hfac := maynardS2OuterSquarefreeAF_offCoordinateProduct_eq_prod m r
      (isMaynardDivisorTuple_of_mem_support hrData.1)
    have hrm : r m = 1 := hrData.2.1
    unfold F
    calc
      maynardS2OuterSquarefreeAF (primorial D)
          (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) =
          ∏ h ∈ Finset.univ.erase m,
            maynardS2OuterSquarefreeAF (primorial D) (r h) := hfac
      _ = maynardS2OuterSquarefreeAF (primorial D) (r m) *
          ∏ h ∈ Finset.univ.erase m,
            maynardS2OuterSquarefreeAF (primorial D) (r h) := by
        rw [hrm]
        simp only [(maynardS2OuterSquarefreeAF_isMultiplicative
          (primorial D)).map_one, one_mul]
      _ = ∏ h : BoundedGaps.engelsmaTuple,
          maynardS2OuterSquarefreeAF (primorial D) (r h) :=
        Finset.mul_prod_erase Finset.univ
          (fun h : BoundedGaps.engelsmaTuple =>
            maynardS2OuterSquarefreeAF (primorial D) (r h))
          (Finset.mem_univ m)
  have hterm : ∀ r ∈ G, F r * I r ≤ F r * B := by
    intro r hr
    exact mul_le_mul_of_nonneg_left (hpoint r hr) (by
      dsimp [F]
      apply Finset.prod_nonneg
      intro h hh
      exact maynardS2OuterSquarefreeAF_nonneg _ _)
  have hsumPoint :
      (∑ r ∈ G, F r * I r) ≤ ∑ r ∈ G, F r * B := by
    exact Finset.sum_le_sum fun r hr => hterm r hr
  have hsumFactor :
      (∑ r ∈ G, F r * B) = B * ∑ r ∈ G, F r := by
    rw [← Finset.sum_mul]
    ring
  have hsumBox :
      (∑ r ∈ G, F r) ≤
        ∑ r ∈ maynardS2OuterCoordinateOneFaceBox R D m, F r := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact engelsmaS2CoordinateFiberGoodSupport_subset_outerFaceBox R D m
    · intro r hrBox hrNot
      dsimp [F]
      apply Finset.prod_nonneg
      intro h hh
      exact maynardS2OuterSquarefreeAF_nonneg _ _
  unfold engelsmaS2CoordinateFiberGoodOuterMoment
  calc
    (∑ r ∈ G,
        maynardS2OuterSquarefreeAF (primorial D)
            (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) * I r) =
        ∑ r ∈ G, F r * I r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hrewrite r hr]
    _ ≤ ∑ r ∈ G, F r * B := hsumPoint
    _ = B * ∑ r ∈ G, F r := hsumFactor
    _ ≤ B * ∑ r ∈ maynardS2OuterCoordinateOneFaceBox R D m, F r := by
      exact mul_le_mul_of_nonneg_left hsumBox hB
    _ = B * ∏ h ∈ Finset.univ.erase m,
          maynardS2OuterSquarefreeMean (primorial D) R := by
      rw [maynardS2OuterCoordinateOneFaceBox_sum_eq_erase_prod_mean]

end BoundedGaps.Maynard
