import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2BarycentricBoundsD978
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabPositiveSecantD977

/-!
# Constant P2 slot bounds from finite vertex data

The existing constant payload is bounded for every width/denominator choice, including
nonpositive widths. Source context: `MAYNARD-PRD-PUBLISHED`, Section 6, Eqs. (6.12)-(6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem weighted_positive_D979 {w f : Fin 4 -> Real}
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hf : ∀ i, 0 < f i) :
    0 < ∑ i, w i * f i := by
  have h := (convex_Ioi (0 : Real)).sum_mem
    (t := (Finset.univ : Finset (Fin 4))) (w := w) (z := f)
    (fun i _ => hw i) hsum (fun i _ => hf i)
  simpa only [smul_eq_mul, Set.mem_Ioi] using h

theorem joint_reciprocal_le_barycentric_of_lower_D979
    {m : Nat} {w : Fin 4 -> Real} {p : Fin 4 -> Fin m -> Real}
    {y : Fin m -> Real} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hp : ∀ i k, 0 < p i k) (hpy : ∀ k, (∑ i, w i * p i k) ≤ y k) :
    (∏ k, (y k)⁻¹) ≤ ∑ i, w i * ∏ k, (p i k)⁻¹ := by
  have hmean (k : Fin m) : 0 < ∑ i, w i * p i k :=
    weighted_positive_D979 hw hsum (fun i => hp i k)
  calc
    (∏ k, (y k)⁻¹) ≤ ∏ k, (∑ i, w i * p i k)⁻¹ :=
      Finset.prod_le_prod
        (fun k _ => inv_nonneg.mpr ((hmean k).trans_le (hpy k)).le)
        (fun k _ => inv_anti₀ (hmean k) (hpy k))
    _ ≤ _ := joint_reciprocal_barycentric_secant_le_D964 hw hsum hp

theorem sectionSixP2ConstantPayload_le_vertexProduct_D979
    (w u v d W rhoL rhoH : Fin 4 -> Real)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i) (hd : ∀ i, 0 < d i)
    (hW : ∀ i, 0 < W i) (hrhoL : ∀ i, 0 < rhoL i)
    (hrhoH : ∀ i, 0 < rhoH i) (C : Real) (hC : 0 ≤ C)
    (j : Fin 4) (lo hi : Bool) :
    let M := fun f : Fin 4 -> Real => ∑ i, w i * f i
    let L := max (M d) (min (M W) (M rhoL))
    let H := max (M d) (min (M W) (M rhoH))
    let N := fun i => max 0 (![W i - d i, rhoH i - d i,
      W i - rhoL i, rhoH i - rhoL i] j)
    let R := fun i => (u i * v i * W i *
      (if lo then rhoL i else d i) *
      (if hi then min (W i) (rhoH i) else d i))⁻¹
    sectionSixBuchstabConstantPayload (M u) (M v) (M W) L H C ≤
      C * M N * M R := by
  dsimp only
  let M := fun f : Fin 4 -> Real => ∑ i, w i * f i
  let L := max (M d) (min (M W) (M rhoL))
  let H := max (M d) (min (M W) (M rhoH))
  let N := fun i => max 0 (![W i - d i, rhoH i - d i,
    W i - rhoL i, rhoH i - rhoL i] j)
  let ell := fun i => if lo then rhoL i else d i
  let eta := fun i => if hi then min (W i) (rhoH i) else d i
  let R := fun i => (u i * v i * W i * ell i * eta i)⁻¹
  change sectionSixBuchstabConstantPayload (M u) (M v) (M W) L H C ≤ C * M N * M R
  have hMu : 0 < M u := weighted_positive_D979 hw hsum hu
  have hMv : 0 < M v := weighted_positive_D979 hw hsum hv
  have hMW : 0 < M W := weighted_positive_D979 hw hsum hW
  have hMd : 0 < M d := weighted_positive_D979 hw hsum hd
  have hL : 0 < L := hMd.trans_le (le_max_left _ _)
  have hH : 0 < H := hMd.trans_le (le_max_left _ _)
  have hell (i : Fin 4) : 0 < ell i := by
    dsimp only [ell]
    split <;> first | exact hrhoL i | exact hd i
  have heta (i : Fin 4) : 0 < eta i := by
    dsimp only [eta]
    split
    · exact lt_min (hW i) (hrhoH i)
    · exact hd i
  have hN : 0 ≤ M N := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hw i) (le_max_left _ _)
  have hR : 0 ≤ M R := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hw i) (inv_nonneg.mpr
      (mul_pos (mul_pos (mul_pos (mul_pos (hu i) (hv i)) (hW i)) (hell i)) (heta i)).le)
  have hden : 0 < M u * M v * M W * L * H := by positivity
  rw [sectionSixBuchstabConstantPayload_eq_width_D977
    (M u) (M v) (M W) L H C hL.ne' hH.ne']
  by_cases hwidth : 0 < H - L
  · have hlower := sectionSixP2ClampedLower_vertex_bounds_D978 w d W rhoL rhoH hw hwidth
    have hupper := sectionSixP2ClampedUpper_vertex_bounds_D978 w d W rhoL rhoH hw hwidth
    have hMN : H - L ≤ M N :=
      sectionSixP2ClampedWidth_vertex_le_D978 w d W rhoL rhoH hw j
    let p : Fin 4 -> Fin 5 -> Real := fun i => ![u i, v i, W i, ell i, eta i]
    let y : Fin 5 -> Real := ![M u, M v, M W, L, H]
    have hp : ∀ i k, 0 < p i k := by
      intro i k
      fin_cases k <;> simp only [p]
      · exact hu i
      · exact hv i
      · exact hW i
      · exact hell i
      · exact heta i
    have hpy : ∀ k, (∑ i, w i * p i k) ≤ y k := by
      intro k
      fin_cases k <;> simp only [p, y]
      · exact le_rfl
      · exact le_rfl
      · exact le_rfl
      · cases lo
        · exact hlower.1
        · exact hlower.2.1
      · cases hi
        · exact hupper.1
        · exact hupper.2.1
    have hrec : (M u * M v * M W * L * H)⁻¹ ≤ M R := by
      have h := joint_reciprocal_le_barycentric_of_lower_D979 hw hsum hp hpy
      simpa [p, y, R, M, Fin.prod_univ_five, mul_inv_rev,
        mul_assoc, mul_left_comm, mul_comm] using h
    calc
      C * (H - L) / (M u * M v * M W * L * H) =
          C * ((H - L) * (M u * M v * M W * L * H)⁻¹) := by ring
      _ ≤ C * (M N * M R) := mul_le_mul_of_nonneg_left
        (mul_le_mul hMN hrec (inv_nonneg.mpr hden.le) hN) hC
      _ = _ := by ring
  · exact (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hC (le_of_not_gt hwidth)) hden.le).trans
      (mul_nonneg (mul_nonneg hC hN) hR)

end PrimesRestrictedDigits
