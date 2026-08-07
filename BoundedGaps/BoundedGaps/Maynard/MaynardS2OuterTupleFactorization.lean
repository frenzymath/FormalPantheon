import BoundedGaps.Maynard.MaynardS2CoordinateFiberOuterWeight

noncomputable section

/-!
# Off-coordinate factorization of the S2 outer weight

The scalar outer coefficient on the off-coordinate product factors into its
coordinate-local squarefree weights. This records the precise measure carried
by the S2 outer face before any multidimensional summation argument.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

theorem maynardS2OuterSquarefreeAF_offCoordinateProduct_eq_prod
    {H : Finset ℕ} {R W : ℕ} (m : H) (r : H → ℕ)
    (hr : IsMaynardDivisorTuple H R W r) :
    maynardS2OuterSquarefreeAF W
        (maynardS2OffCoordinateProduct H m r) =
      ∏ h ∈ Finset.univ.erase m,
        maynardS2OuterSquarefreeAF W (r h) := by
  unfold maynardS2OffCoordinateProduct
  exact (maynardS2OuterSquarefreeAF_isMultiplicative W).map_prod r
    (Finset.univ.erase m)
    (fun a _ b _ hab => hr.coordinates_coprime hab)

theorem maynardS2OuterSquarefreeAF_offCoordinateProduct_eq_local_phi_g_weight
    {H : Finset ℕ} {D R : ℕ} (m : H) (r : H → ℕ)
    (hr : IsMaynardDivisorTuple H R (primorial D) r) :
    maynardS2OuterSquarefreeAF (primorial D)
        (maynardS2OffCoordinateProduct H m r) =
      ∏ h ∈ Finset.univ.erase m,
        (Nat.totient (r h) : ℝ) ^ 2 /
          ((maynardS2G (r h) : ℝ) * (r h : ℝ) ^ 2) := by
  rw [maynardS2OuterSquarefreeAF_offCoordinateProduct_eq_prod m r hr]
  apply Finset.prod_congr rfl
  intro h hh
  exact maynardS2OuterSquarefreeAF_apply_squarefree_of_coprime
    (hr.coordinate_squarefree h) (hr.coordinate_coprime_W h)

end BoundedGaps.Maynard
