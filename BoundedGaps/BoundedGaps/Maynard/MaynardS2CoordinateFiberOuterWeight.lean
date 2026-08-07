import BoundedGaps.Maynard.MaynardS2CoordinateFiberLocalSeries
import BoundedGaps.Maynard.MaynardS2OuterSquarefreeFunction

noncomputable section

/-!
# S2 coordinate-fiber outer weight

The squared singular density of a distinguished-coordinate fiber, after
division by its tuple `g`-factor, is exactly the squarefree outer coefficient.
This is the pointwise normalization preceding the outer partial summations in
Maynard2013v3, source lines 536--552.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

theorem maynardS2G_divisorTupleProduct_eq_prod
    {H : Finset ℕ} {R W : ℕ} {r : H → ℕ}
    (hr : IsMaynardDivisorTuple H R W r) :
    maynardS2G (divisorTupleProduct H r) =
      ∏ h : H, maynardS2G (r h) := by
  unfold divisorTupleProduct
  exact (ArithmeticFunction.IsMultiplicative.prodPrimeFactors
    (fun p : ℕ => p - 2)).map_prod r Finset.univ
      (fun a _ b _ hab => hr.coordinates_coprime hab)

theorem maynardS2CoordinateFiberSingularSeries_sq_div_gProduct_eq_outerSquarefree
    {H : Finset ℕ} {D R : ℕ} (m : H) (r : H → ℕ)
    (hr : IsMaynardDivisorTuple H R (primorial D) r)
    (hrm : r m = 1) :
    maynardS2CoordinateFiberSingularSeries D m r ^ 2 /
        ∏ h : H, (maynardS2G (r h) : ℝ) =
      preSieveSingularSeries D ^ 2 *
        maynardS2OuterSquarefreeAF (primorial D)
          (maynardS2OffCoordinateProduct H m r) := by
  let P := maynardS2OffCoordinateProduct H m r
  have hPsq : Squarefree P := maynardS2OffCoordinateProduct_squarefree m r hr
  have hPW : Nat.Coprime P (primorial D) :=
    (maynardS2OffCoordinateProduct_coprime m r hr).symm
  have hgNat := maynardS2G_divisorTupleProduct_eq_prod hr
  have hprod : divisorTupleProduct H r = P :=
    divisorTupleProduct_eq_offCoordinateProduct m hrm
  have hg : (maynardS2G P : ℝ) =
      ∏ h : H, (maynardS2G (r h) : ℝ) := by
    rw [hprod] at hgNat
    exact_mod_cast hgNat
  rw [maynardS2CoordinateFiberSingularSeries_eq_preSieve_mul m r hr,
    maynardS2OuterSquarefreeAF_apply_squarefree_of_coprime hPsq hPW,
    ← hg]
  simp only [P, div_eq_mul_inv, mul_inv]
  ring

theorem sum_maynardS2CoordinateFiberSingularSeries_sq_div_gProduct_eq_outerSquarefree
    {H : Finset ℕ} {D R : ℕ} (m : H) (F : (H → ℕ) → ℝ) :
    (∑ r ∈ (maynardDivisorTupleSupport H R (primorial D)).filter
        (fun r => r m = 1),
      (maynardS2CoordinateFiberSingularSeries D m r * F r) ^ 2 /
        ∏ h : H, (maynardS2G (r h) : ℝ)) =
      preSieveSingularSeries D ^ 2 *
        ∑ r ∈ (maynardDivisorTupleSupport H R (primorial D)).filter
          (fun r => r m = 1),
        maynardS2OuterSquarefreeAF (primorial D)
            (maynardS2OffCoordinateProduct H m r) * F r ^ 2 := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hrMem
  have hrData := Finset.mem_filter.mp hrMem
  have hr := isMaynardDivisorTuple_of_mem_support hrData.1
  have hweight :=
    maynardS2CoordinateFiberSingularSeries_sq_div_gProduct_eq_outerSquarefree
      m r hr hrData.2
  calc
    (maynardS2CoordinateFiberSingularSeries D m r * F r) ^ 2 /
        ∏ h : H, (maynardS2G (r h) : ℝ) =
      (maynardS2CoordinateFiberSingularSeries D m r ^ 2 /
        ∏ h : H, (maynardS2G (r h) : ℝ)) * F r ^ 2 := by ring
    _ = (preSieveSingularSeries D ^ 2 *
        maynardS2OuterSquarefreeAF (primorial D)
          (maynardS2OffCoordinateProduct H m r)) * F r ^ 2 := by
      rw [hweight]
    _ = preSieveSingularSeries D ^ 2 *
        (maynardS2OuterSquarefreeAF (primorial D)
          (maynardS2OffCoordinateProduct H m r) * F r ^ 2) := by ring

end BoundedGaps.Maynard
