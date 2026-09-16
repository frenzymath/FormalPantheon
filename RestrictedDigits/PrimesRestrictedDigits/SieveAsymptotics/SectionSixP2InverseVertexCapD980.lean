import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ConstantVertexCapD979

/-!
# Inverse P2 slot bounds from finite vertex data

The positive split of the existing secant payload is bounded by three affine vertex
interpolants in each term. Repeated denominator columns retain the two reciprocal squares
exactly. Source context: `MAYNARD-PRD-PUBLISHED`, Section 6, Eqs. (6.12)-(6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem weighted_positive_D980 {w f : Fin 4 -> Real}
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hf : ∀ i, 0 < f i) :
    0 < ∑ i, w i * f i := by
  have h := (convex_Ioi (0 : Real)).sum_mem
    (t := (Finset.univ : Finset (Fin 4))) (w := w) (z := f)
    (fun i _ => hw i) hsum (fun i _ => hf i)
  simpa only [smul_eq_mul, Set.mem_Ioi] using h

private theorem mul_mul_le_mul_mul_D980
    {x y z X Y Z : Real} (hx : 0 ≤ x) (hX : x ≤ X)
    (hy : 0 ≤ y) (hY : y ≤ Y) (hz : 0 ≤ z) (hZ : z ≤ Z) :
    x * y * z ≤ X * Y * Z := by
  have hX0 : 0 ≤ X := hx.trans hX
  have hY0 : 0 ≤ Y := hy.trans hY
  exact mul_le_mul (mul_le_mul hX hY hy hX0) hZ hz (mul_nonneg hX0 hY0)

set_option maxHeartbeats 800000 in
theorem sectionSixP2SecantPayload_le_vertexProducts_D980
    (w u v d W rhoL rhoH B : Fin 4 -> Real)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i) (hd : ∀ i, 0 < d i)
    (hW : ∀ i, 0 < W i) (hrhoL : ∀ i, 0 < rhoL i)
    (hrhoH : ∀ i, 0 < rhoH i) (hrho : ∀ i, rhoL i ≤ rhoH i)
    (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (hwall : ∀ i, B i ≤ (b + 1) * rhoL i)
    (j : Fin 4) (lo hi upper : Bool) :
    let M := fun f : Fin 4 -> Real => ∑ i, w i * f i
    let L := max (M d) (min (M W) (M rhoL))
    let H := max (M d) (min (M W) (M rhoH))
    let c := a + b + 1
    let N := fun i => max 0 (![W i - d i, rhoH i - d i,
      W i - rhoL i, rhoH i - rhoL i] j)
    let ell := fun i => if lo then rhoL i else d i
    let eta := fun i => if hi then min (W i) (rhoH i) else d i
    let QH := fun i => max 0 (c * (if upper then rhoH i else W i) - B i)
    let QL := fun i => max 0 (c * max (d i) (rhoL i) - B i)
    let RH := fun i => (u i * v i * W i * ell i * eta i ^ 2)⁻¹
    let RL := fun i => (u i * v i * W i * ell i ^ 2 * eta i)⁻¹
    sectionSixBuchstabSecantPayload (M u) (M v) (M W) (M B) L H a b ≤
      (M N * M QH * M RH + M N * M QL * M RL) / (2 * a * b) := by
  dsimp only
  let M := fun f : Fin 4 -> Real => ∑ i, w i * f i
  let L := max (M d) (min (M W) (M rhoL))
  let H := max (M d) (min (M W) (M rhoH))
  let c := a + b + 1
  let N := fun i => max 0 (![W i - d i, rhoH i - d i,
    W i - rhoL i, rhoH i - rhoL i] j)
  let ell := fun i => if lo then rhoL i else d i
  let eta := fun i => if hi then min (W i) (rhoH i) else d i
  let QH := fun i => max 0 (c * (if upper then rhoH i else W i) - B i)
  let QL := fun i => max 0 (c * max (d i) (rhoL i) - B i)
  let RH := fun i => (u i * v i * W i * ell i * eta i ^ 2)⁻¹
  let RL := fun i => (u i * v i * W i * ell i ^ 2 * eta i)⁻¹
  change sectionSixBuchstabSecantPayload (M u) (M v) (M W) (M B) L H a b ≤
    (M N * M QH * M RH + M N * M QL * M RL) / (2 * a * b)
  have hMu : 0 < M u := weighted_positive_D980 hw hsum hu
  have hMv : 0 < M v := weighted_positive_D980 hw hsum hv
  have hMW : 0 < M W := weighted_positive_D980 hw hsum hW
  have hMd : 0 < M d := weighted_positive_D980 hw hsum hd
  have hL : 0 < L := hMd.trans_le (le_max_left _ _)
  have hH : 0 < H := hMd.trans_le (le_max_left _ _)
  have hMrho : M rhoL ≤ M rhoH := Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (hrho i) (hw i)
  have hLH : L ≤ H := max_le_max_left (M d) (min_le_min_left (M W) hMrho)
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
  have hQH : 0 ≤ M QH := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hw i) (le_max_left _ _)
  have hQL : 0 ≤ M QL := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hw i) (le_max_left _ _)
  have hRHvertex (i : Fin 4) : 0 < RH i := by
    dsimp only [RH]
    exact inv_pos.mpr <| mul_pos
      (mul_pos (mul_pos (mul_pos (hu i) (hv i)) (hW i)) (hell i))
      (pow_pos (heta i) 2)
  have hRLvertex (i : Fin 4) : 0 < RL i := by
    dsimp only [RL]
    exact inv_pos.mpr <| mul_pos
      (mul_pos (mul_pos (mul_pos (hu i) (hv i)) (hW i)) (pow_pos (hell i) 2))
      (heta i)
  have hRH : 0 ≤ M RH := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hw i) (hRHvertex i).le
  have hRL : 0 ≤ M RL := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hw i) (hRLvertex i).le
  rw [sectionSixBuchstabSecantPayload_eq_positiveSplit_D977
    (M u) (M v) (M W) (M B) L H a b hL.ne' hH.ne' ha.ne' hb.ne']
  by_cases hwidth : 0 < H - L
  · have hlower := sectionSixP2ClampedLower_vertex_bounds_D978
      w d W rhoL rhoH hw hwidth
    have hupper := sectionSixP2ClampedUpper_vertex_bounds_D978
      w d W rhoL rhoH hw hwidth
    have hMN : H - L ≤ M N :=
      sectionSixP2ClampedWidth_vertex_le_D978 w d W rhoL rhoH hw j
    have hMB : M B ≤ (b + 1) * M rhoL := by
      calc
        M B ≤ M (fun i => (b + 1) * rhoL i) := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hwall i) (hw i)
        _ = (b + 1) * M rhoL := by
          dsimp only [M]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    have hMBL : M B ≤ (b + 1) * L := hMB.trans <|
      mul_le_mul_of_nonneg_left hlower.2.1 (by positivity)
    have hc : 0 < c := by dsimp only [c]; positivity
    have hML : 0 < c * L - M B := by
      dsimp only [c]
      nlinarith [mul_pos ha hL]
    have hMH : 0 < c * H - M B := by
      have hcLH : c * L ≤ c * H := mul_le_mul_of_nonneg_left hLH hc.le
      linarith
    have hMQH : c * H - M B ≤ M QH :=
      (le_max_right 0 (c * H - M B)).trans <|
        sectionSixP2ClampedUpperNumerator_vertex_le_D978
          w d W rhoL rhoH B hw c hc.le upper hwidth
    have hMQL : c * L - M B ≤ M QL :=
      (le_max_right 0 (c * L - M B)).trans <|
        sectionSixP2ClampedLowerNumerator_vertex_le_D978
          w d W rhoL rhoH B hw c hc.le hwidth
    let pH : Fin 4 -> Fin 6 -> Real := fun i =>
      ![u i, v i, W i, ell i, eta i, eta i]
    let yH : Fin 6 -> Real := ![M u, M v, M W, L, H, H]
    have hpH : ∀ i k, 0 < pH i k := by
      intro i k
      fin_cases k <;> simp only [pH]
      · exact hu i
      · exact hv i
      · exact hW i
      · exact hell i
      · exact heta i
      · exact heta i
    have hpyH : ∀ k, (∑ i, w i * pH i k) ≤ yH k := by
      intro k
      fin_cases k <;> simp only [pH, yH]
      · exact le_rfl
      · exact le_rfl
      · exact le_rfl
      · cases lo
        · exact hlower.1
        · exact hlower.2.1
      · cases hi
        · exact hupper.1
        · exact hupper.2.1
      · cases hi
        · exact hupper.1
        · exact hupper.2.1
    have hrecH : (M u * M v * M W * L * H ^ 2)⁻¹ ≤ M RH := by
      have h := joint_reciprocal_le_barycentric_of_lower_D979 hw hsum hpH hpyH
      simpa [pH, yH, RH, M, Fin.prod_univ_six, pow_two, mul_inv_rev,
        mul_assoc, mul_left_comm, mul_comm] using h
    let pL : Fin 4 -> Fin 6 -> Real := fun i =>
      ![u i, v i, W i, ell i, ell i, eta i]
    let yL : Fin 6 -> Real := ![M u, M v, M W, L, L, H]
    have hpL : ∀ i k, 0 < pL i k := by
      intro i k
      fin_cases k <;> simp only [pL]
      · exact hu i
      · exact hv i
      · exact hW i
      · exact hell i
      · exact hell i
      · exact heta i
    have hpyL : ∀ k, (∑ i, w i * pL i k) ≤ yL k := by
      intro k
      fin_cases k <;> simp only [pL, yL]
      · exact le_rfl
      · exact le_rfl
      · exact le_rfl
      · cases lo
        · exact hlower.1
        · exact hlower.2.1
      · cases lo
        · exact hlower.1
        · exact hlower.2.1
      · cases hi
        · exact hupper.1
        · exact hupper.2.1
    have hrecL : (M u * M v * M W * L ^ 2 * H)⁻¹ ≤ M RL := by
      have h := joint_reciprocal_le_barycentric_of_lower_D979 hw hsum hpL hpyL
      simpa [pL, yL, RL, M, Fin.prod_univ_six, pow_two, mul_inv_rev,
        mul_assoc, mul_left_comm, mul_comm] using h
    have hdenH : 0 < M u * M v * M W * L * H ^ 2 := by positivity
    have hdenL : 0 < M u * M v * M W * L ^ 2 * H := by positivity
    have htermH :
        (H - L) * (c * H - M B) / (M u * M v * M W * L * H ^ 2) ≤
          M N * M QH * M RH := by
      rw [div_eq_mul_inv]
      exact mul_mul_le_mul_mul_D980 hwidth.le hMN hMH.le hMQH
        (inv_nonneg.mpr hdenH.le) hrecH
    have htermL :
        (H - L) * (c * L - M B) / (M u * M v * M W * L ^ 2 * H) ≤
          M N * M QL * M RL := by
      rw [div_eq_mul_inv]
      exact mul_mul_le_mul_mul_D980 hwidth.le hMN hML.le hMQL
        (inv_nonneg.mpr hdenL.le) hrecL
    exact div_le_div_of_nonneg_right (add_le_add htermH htermL) (by positivity)
  · have hHL : H ≤ L := sub_nonpos.mp (le_of_not_gt hwidth)
    have heq : H = L := le_antisymm hHL hLH
    rw [heq]
    simp only [sub_self, zero_mul, zero_div, zero_add]
    exact div_nonneg
      (add_nonneg (mul_nonneg (mul_nonneg hN hQH) hRH)
        (mul_nonneg (mul_nonneg hN hQL) hRL)) (by positivity)

end PrimesRestrictedDigits
