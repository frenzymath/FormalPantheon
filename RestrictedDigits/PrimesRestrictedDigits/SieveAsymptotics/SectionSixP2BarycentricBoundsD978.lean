import PrimesRestrictedDigits.BasicEstimates.JointReciprocalBarycentricSecantD964
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ClampedIntervalAlgebraD976
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Barycentric bounds for clamped P2 endpoints

Nonnegative weighted sums turn the positive-width endpoint identities into finite vertex
bounds. These inequalities are the algebraic input for the later constant and inverse slot
caps.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem weighted_sum_le_D978
    {w a b : Fin 4 -> Real} (hw : forall i, 0 <= w i)
    (hab : forall i, a i <= b i) :
    (∑ i, w i * a i) <= ∑ i, w i * b i :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hab i) (hw i)

private theorem weighted_max_le_D978
    {w a b : Fin 4 -> Real} (hw : forall i, 0 <= w i) :
    max (∑ i, w i * a i) (∑ i, w i * b i) <=
      ∑ i, w i * max (a i) (b i) := by
  apply max_le
  · exact weighted_sum_le_D978 hw fun i => le_max_left _ _
  · exact weighted_sum_le_D978 hw fun i => le_max_right _ _

private theorem weighted_min_le_D978
    {w a b : Fin 4 -> Real} (hw : forall i, 0 <= w i) :
    (∑ i, w i * min (a i) (b i)) <=
      min (∑ i, w i * a i) (∑ i, w i * b i) := by
  apply le_min
  · exact weighted_sum_le_D978 hw fun i => min_le_left _ _
  · exact weighted_sum_le_D978 hw fun i => min_le_right _ _

private theorem weighted_sub_D978
    (w a b : Fin 4 -> Real) :
    (∑ i, w i * a i) - (∑ i, w i * b i) =
      ∑ i, w i * (a i - b i) := by
  simp only [mul_sub, Finset.sum_sub_distrib]

private theorem weighted_scale_sub_D978
    (w a b : Fin 4 -> Real) (c : Real) :
    c * (∑ i, w i * a i) - (∑ i, w i * b i) =
      ∑ i, w i * (c * a i - b i) := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  apply congrArg₂ (· - ·)
  · apply Finset.sum_congr rfl
    intro i hi
    ring
  · rfl

theorem sectionSixP2ClampedLower_vertex_bounds_D978
    (w d W rhoL rhoH : Fin 4 -> Real) (hw : forall i, 0 <= w i) :
    let md := ∑ i, w i * d i
    let mW := ∑ i, w i * W i
    let mrhoL := ∑ i, w i * rhoL i
    let mrhoH := ∑ i, w i * rhoH i
    let L := max md (min mW mrhoL)
    let H := max md (min mW mrhoH)
    0 < H - L ->
      md <= L ∧ mrhoL <= L ∧
        L <= ∑ i, w i * max (d i) (rhoL i) := by
  dsimp only
  intro hpos
  have hL := (sectionSixBuchstabClampedEndpoints_of_posWidth_D976 hpos).1
  rw [hL]
  exact ⟨le_max_left _ _, le_max_right _ _, weighted_max_le_D978 hw⟩

theorem sectionSixP2ClampedUpper_vertex_bounds_D978
    (w d W rhoL rhoH : Fin 4 -> Real) (hw : forall i, 0 <= w i) :
    let md := ∑ i, w i * d i
    let mW := ∑ i, w i * W i
    let mrhoL := ∑ i, w i * rhoL i
    let mrhoH := ∑ i, w i * rhoH i
    let L := max md (min mW mrhoL)
    let H := max md (min mW mrhoH)
    0 < H - L ->
      md <= H ∧ (∑ i, w i * min (W i) (rhoH i)) <= H ∧
        H <= mW ∧ H <= mrhoH := by
  dsimp only
  intro hpos
  have hH := (sectionSixBuchstabClampedEndpoints_of_posWidth_D976 hpos).2
  refine ⟨le_max_left _ _, ?_, ?_, ?_⟩
  · rw [hH]
    exact weighted_min_le_D978 hw
  · rw [hH]
    exact min_le_left _ _
  · rw [hH]
    exact min_le_right _ _

theorem sectionSixP2ClampedWidth_vertex_le_D978
    (w d W rhoL rhoH : Fin 4 -> Real) (hw : forall i, 0 <= w i)
    (j : Fin 4) :
    let md := ∑ i, w i * d i
    let mW := ∑ i, w i * W i
    let mrhoL := ∑ i, w i * rhoL i
    let mrhoH := ∑ i, w i * rhoH i
    let L := max md (min mW mrhoL)
    let H := max md (min mW mrhoH)
    H - L <= ∑ i, w i * max 0
      (![W i - d i, rhoH i - d i, W i - rhoL i,
          rhoH i - rhoL i] j) := by
  dsimp only
  by_cases hpos : 0 <
      max (∑ i, w i * d i) (min (∑ i, w i * W i) (∑ i, w i * rhoH i)) -
        max (∑ i, w i * d i) (min (∑ i, w i * W i) (∑ i, w i * rhoL i))
  · have hlo := sectionSixP2ClampedLower_vertex_bounds_D978 w d W rhoL rhoH hw hpos
    have hup := sectionSixP2ClampedUpper_vertex_bounds_D978 w d W rhoL rhoH hw hpos
    have hchoice (a b : Fin 4 -> Real)
        (ha : max (∑ i, w i * d i)
            (min (∑ i, w i * W i) (∑ i, w i * rhoH i)) <=
              ∑ i, w i * a i)
        (hb : (∑ i, w i * b i) <=
          max (∑ i, w i * d i)
            (min (∑ i, w i * W i) (∑ i, w i * rhoL i))) :
        max (∑ i, w i * d i)
              (min (∑ i, w i * W i) (∑ i, w i * rhoH i)) -
            max (∑ i, w i * d i)
              (min (∑ i, w i * W i) (∑ i, w i * rhoL i)) <=
          ∑ i, w i * max 0 (a i - b i) := by
      calc
        _ <= (∑ i, w i * a i) - (∑ i, w i * b i) := sub_le_sub ha hb
        _ = ∑ i, w i * (a i - b i) := weighted_sub_D978 w a b
        _ <= ∑ i, w i * max 0 (a i - b i) :=
          weighted_sum_le_D978 hw fun i => le_max_right _ _
    fin_cases j
    · simpa using hchoice W d hup.2.2.1 hlo.1
    · simpa using hchoice rhoH d hup.2.2.2 hlo.1
    · simpa using hchoice W rhoL hup.2.2.1 hlo.2.1
    · simpa using hchoice rhoH rhoL hup.2.2.2 hlo.2.1
  · have hnonpos :
        max (∑ i, w i * d i)
              (min (∑ i, w i * W i) (∑ i, w i * rhoH i)) -
            max (∑ i, w i * d i)
              (min (∑ i, w i * W i) (∑ i, w i * rhoL i)) <= 0 :=
      le_of_not_gt hpos
    exact hnonpos.trans <| Finset.sum_nonneg fun i _ =>
      mul_nonneg (hw i) (le_max_left _ _)

theorem sectionSixP2ClampedLowerNumerator_vertex_le_D978
    (w d W rhoL rhoH B : Fin 4 -> Real) (hw : forall i, 0 <= w i)
    (c : Real) (hc : 0 <= c) :
    let md := ∑ i, w i * d i
    let mW := ∑ i, w i * W i
    let mrhoL := ∑ i, w i * rhoL i
    let mrhoH := ∑ i, w i * rhoH i
    let mB := ∑ i, w i * B i
    let L := max md (min mW mrhoL)
    let H := max md (min mW mrhoH)
    0 < H - L ->
      max 0 (c * L - mB) <=
        ∑ i, w i * max 0 (c * max (d i) (rhoL i) - B i) := by
  dsimp only
  intro hpos
  have hL :=
    (sectionSixP2ClampedLower_vertex_bounds_D978 w d W rhoL rhoH hw hpos).2.2
  have hraw :
      c * max (∑ i, w i * d i)
            (min (∑ i, w i * W i) (∑ i, w i * rhoL i)) -
          (∑ i, w i * B i) <=
        c * (∑ i, w i * max (d i) (rhoL i)) - (∑ i, w i * B i) :=
    sub_le_sub_right (mul_le_mul_of_nonneg_left hL hc) _
  calc
    max 0 (c * max (∑ i, w i * d i)
          (min (∑ i, w i * W i) (∑ i, w i * rhoL i)) -
        (∑ i, w i * B i)) <=
        max 0 (c * (∑ i, w i * max (d i) (rhoL i)) -
          (∑ i, w i * B i)) := max_le_max_left 0 hraw
    _ = max 0 (∑ i, w i * (c * max (d i) (rhoL i) - B i)) := by
      rw [<- weighted_scale_sub_D978]
    _ <= _ := positivePart_barycentric_le_D964 hw

theorem sectionSixP2ClampedUpperNumerator_vertex_le_D978
    (w d W rhoL rhoH B : Fin 4 -> Real) (hw : forall i, 0 <= w i)
    (c : Real) (hc : 0 <= c) (j : Bool) :
    let md := ∑ i, w i * d i
    let mW := ∑ i, w i * W i
    let mrhoL := ∑ i, w i * rhoL i
    let mrhoH := ∑ i, w i * rhoH i
    let mB := ∑ i, w i * B i
    let L := max md (min mW mrhoL)
    let H := max md (min mW mrhoH)
    0 < H - L ->
      max 0 (c * H - mB) <=
        ∑ i, w i * max 0 (c * (if j then rhoH i else W i) - B i) := by
  dsimp only
  intro hpos
  have hup := sectionSixP2ClampedUpper_vertex_bounds_D978 w d W rhoL rhoH hw hpos
  have hbound (U : Fin 4 -> Real)
      (hU : max (∑ i, w i * d i)
          (min (∑ i, w i * W i) (∑ i, w i * rhoH i)) <=
            ∑ i, w i * U i) :
      max 0 (c * max (∑ i, w i * d i)
            (min (∑ i, w i * W i) (∑ i, w i * rhoH i)) -
          (∑ i, w i * B i)) <=
        ∑ i, w i * max 0 (c * U i - B i) := by
    have hraw :
        c * max (∑ i, w i * d i)
              (min (∑ i, w i * W i) (∑ i, w i * rhoH i)) -
            (∑ i, w i * B i) <=
          c * (∑ i, w i * U i) - (∑ i, w i * B i) :=
      sub_le_sub_right (mul_le_mul_of_nonneg_left hU hc) _
    calc
      _ <= max 0 (c * (∑ i, w i * U i) - (∑ i, w i * B i)) :=
        max_le_max_left 0 hraw
      _ = max 0 (∑ i, w i * (c * U i - B i)) := by
        rw [<- weighted_scale_sub_D978]
      _ <= _ := positivePart_barycentric_le_D964 hw
  cases j
  · exact hbound W hup.2.2.1
  · exact hbound rhoH hup.2.2.2

end PrimesRestrictedDigits
