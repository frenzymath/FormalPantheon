import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabClampedRationalFiberD899B
import PrimesRestrictedDigits.BasicEstimates.UniformRealGrid
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixBuchstabEightSecantFiberD900D -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixBuchstabArgumentCell
    (B l h a b : Real) : Real × Real :=
  (sectionSixBuchstabClamp l h (B / (b + 1)),
    sectionSixBuchstabClamp l h (B / (a + 1)))

def sectionSixBuchstabConstantPayload
    (u v w l h C : Real) : Real :=
  C / (u * v * w) * (1 / l - 1 / h)

private theorem d900D_reciprocal_le_secant
    {a b y : Real}
    (ha : 0 < a) (hab : a <= b) (hy : y ∈ Icc a b) :
    1 / y <= 1 / a + 1 / b - y / (a * b) := by
  have hb : 0 < b := ha.trans_le hab
  have hy0 : 0 < y := ha.trans_le hy.1
  rw [div_le_iff₀ hy0]
  have hprod : (y - a) * (y - b) <= 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hy.1) (sub_nonpos.mpr hy.2)
  field_simp [ha.ne', hb.ne']
  nlinarith

private theorem d900D_secant_primitive
    {u v w B l h a b : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h)
    (ha : 0 < a) (hb : 0 < b) :
    (∫ t in l..h,
      (1 / a + 1 / b - ((B - t) / t) / (a * b)) /
        (u * v * w * t ^ 2)) =
      sectionSixBuchstabSecantPayload u v w B l h a b := by
  rcases hlh.eq_or_lt with rfl | hlh
  · simp [sectionSixBuchstabSecantPayload]
  · let F : Real -> Real := fun t =>
      1 / (u * v * w) *
        (-(1 / a + 1 / b + 1 / (a * b)) * t⁻¹ +
          (B / (2 * a * b)) * (t⁻¹) ^ 2)
    have hderiv : forall t : Real, t ∈ uIcc l h ->
        HasDerivAt F
          ((1 / a + 1 / b - ((B - t) / t) / (a * b)) /
            (u * v * w * t ^ 2)) t := by
      intro t ht
      rw [uIcc_of_le hlh.le] at ht
      have ht0 : 0 < t := hl.trans_le ht.1
      have hinv := hasDerivAt_inv ht0.ne'
      have hinvSq := hinv.pow 2
      have hraw :=
        ((hinv.const_mul (-(1 / a + 1 / b + 1 / (a * b)))).add
          (hinvSq.const_mul (B / (2 * a * b)))).const_mul
            (1 / (u * v * w))
      have hraw' := hraw.congr_deriv
        (g' := (1 / a + 1 / b - ((B - t) / t) / (a * b)) /
          (u * v * w * t ^ 2)) (by
          simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
          field_simp [ha.ne', hb.ne', ht0.ne', hu.ne', hv.ne', hw.ne']
          ring)
      apply hraw'.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall fun x => by
        simp only [F, Pi.add_apply, Pi.pow_apply]
    have hint : IntervalIntegrable
        (fun t : Real =>
          (1 / a + 1 / b - ((B - t) / t) / (a * b)) /
            (u * v * w * t ^ 2)) volume l h := by
      apply ContinuousOn.intervalIntegrable
      apply continuousOn_of_forall_continuousAt
      intro t ht
      rw [uIcc_of_le hlh.le] at ht
      have ht0 : 0 < t := hl.trans_le ht.1
      have hden : Ne (u * v * w * t ^ 2) 0 := by positivity
      fun_prop (disch := positivity)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    dsimp [F, sectionSixBuchstabSecantPayload]
    field_simp [ha.ne', hb.ne', hu.ne', hv.ne', hw.ne', hl.ne',
      (hl.trans hlh).ne']
    ring

private theorem d900D_secant_branch_le
    {u v w B l h a b : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h)
    (haOne : 1 <= a) (hab : a <= b) (hbTwo : b <= 2)
    (hLower : (a + 1) * h <= B)
    (hUpper : B <= (b + 1) * l) :
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) /
        (u * v * w * t ^ 2)) <=
      sectionSixBuchstabSecantPayload u v w B l h a b := by
  have ha : 0 < a := lt_of_lt_of_le (by norm_num) haOne
  have hb : 0 < b := ha.trans_le hab
  have hh : 0 < h := hl.trans_le hlh
  have hB : 2 * h <= B := by nlinarith [haOne, hh]
  have hfun := sectionSixBuchstabFiber_intervalIntegrable
    hu hv hw hl hlh hB
  have hmajorant : IntervalIntegrable
      (fun t : Real =>
        (1 / a + 1 / b - ((B - t) / t) / (a * b)) /
          (u * v * w * t ^ 2)) volume l h := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [uIcc_of_le hlh] at ht
    have ht0 : 0 < t := hl.trans_le ht.1
    have hden : Ne (u * v * w * t ^ 2) 0 := by positivity
    fun_prop (disch := positivity)
  calc
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) /
        (u * v * w * t ^ 2)) <=
        ∫ t in l..h,
          (1 / a + 1 / b - ((B - t) / t) / (a * b)) /
            (u * v * w * t ^ 2) := by
      apply intervalIntegral.integral_mono_on hlh hfun hmajorant
      intro t ht
      have ht0 : 0 < t := hl.trans_le ht.1
      have hyLower : a <= (B - t) / t := by
        rw [le_div_iff₀ ht0]
        nlinarith [hLower, ht.2]
      have hyUpper : (B - t) / t <= b := by
        rw [div_le_iff₀ ht0]
        nlinarith [hUpper, ht.1]
      have homega : buchstabFunction ((B - t) / t) =
          1 / ((B - t) / t) := by
        simpa only [one_div] using
          (buchstabFunction_eq_inv (haOne.trans hyLower)
            (hyUpper.trans hbTwo))
      have hsecant := d900D_reciprocal_le_secant ha hab
        (show (B - t) / t ∈ Icc a b from ⟨hyLower, hyUpper⟩)
      have hden : 0 < u * v * w * t ^ 2 := by positivity
      rw [homega]
      exact (div_le_div_iff_of_pos_right hden).2 hsecant
    _ = _ := d900D_secant_primitive hu hv hw hl hlh ha hb

private theorem d900D_payload_self
    (u v w B x a b : Real) :
    sectionSixBuchstabSecantPayload u v w B x x a b = 0 := by
  simp [sectionSixBuchstabSecantPayload]

private theorem d900D_raw_order
    {B a b : Real} (hB : 0 < B) (ha : 1 <= a)
    (hab : a <= b) :
    B / (b + 1) <= B / (a + 1) := by
  have ha1 : 0 < a + 1 := by linarith
  have hb1 : 0 < b + 1 := by linarith
  rw [div_le_div_iff_of_pos_left hB hb1 ha1]
  linarith

private theorem d900D_clamp_left
    {l h x : Real} (hlh : l <= h) (hx : x <= l) :
    sectionSixBuchstabClamp l h x = l := by
  unfold sectionSixBuchstabClamp
  rw [min_eq_right (hx.trans hlh), max_eq_left hx]

private theorem d900D_clamp_right
    {l h x : Real} (hlh : l <= h) (hx : h <= x) :
    sectionSixBuchstabClamp l h x = h := by
  unfold sectionSixBuchstabClamp
  rw [min_eq_left hx, max_eq_right hlh]

private theorem d900D_clamp_mono
    {l h x y : Real} (hxy : x <= y) :
    sectionSixBuchstabClamp l h x <= sectionSixBuchstabClamp l h y := by
  unfold sectionSixBuchstabClamp
  exact max_le_max_left l (min_le_min_left h hxy)

private theorem d900D_clamped_cell_le
    {u v w B l h a b : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h)
    (haOne : 1 <= a) (hab : a <= b) (hbTwo : b <= 2)
    (hB : 0 < B) :
    (∫ t in
        (sectionSixBuchstabClamp l h (B / (b + 1)))..
        (sectionSixBuchstabClamp l h (B / (a + 1))),
      buchstabFunction ((B - t) / t) /
        (u * v * w * t ^ 2)) <=
      sectionSixBuchstabSecantPayload u v w B
        (sectionSixBuchstabArgumentCell B l h a b).1
        (sectionSixBuchstabArgumentCell B l h a b).2 a b := by
  let rawL : Real := B / (b + 1)
  let rawH : Real := B / (a + 1)
  let low : Real := sectionSixBuchstabClamp l h rawL
  let high : Real := sectionSixBuchstabClamp l h rawH
  have hraw : rawL <= rawH := by
    dsimp [rawL, rawH]
    exact d900D_raw_order hB haOne hab
  change (∫ t in low..high,
      buchstabFunction ((B - t) / t) /
        (u * v * w * t ^ 2)) <=
      sectionSixBuchstabSecantPayload u v w B low high a b
  by_cases hleft : rawH <= l
  · have hlow : low = l := by
      dsimp [low]
      exact d900D_clamp_left hlh (hraw.trans hleft)
    have hhigh : high = l := by
      dsimp [high]
      exact d900D_clamp_left hlh hleft
    rw [hlow, hhigh, d900D_payload_self]
    simp
  · by_cases hright : h <= rawL
    · have hlow : low = h := by
        dsimp [low]
        exact d900D_clamp_right hlh hright
      have hhigh : high = h := by
        dsimp [high]
        exact d900D_clamp_right hlh (hright.trans hraw)
      rw [hlow, hhigh, d900D_payload_self]
      simp
    · have hrawHgt : l < rawH := lt_of_not_ge hleft
      have hrawLlt : rawL < h := lt_of_not_ge hright
      have hlow_raw : rawL <= low := by
        dsimp [low, sectionSixBuchstabClamp]
        rw [min_eq_right hrawLlt.le]
        exact le_max_right _ _
      have hhigh_raw : high <= rawH := by
        dsimp [high, sectionSixBuchstabClamp]
        apply max_le
        · exact hrawHgt.le
        · exact min_le_right _ _
      have hordered : low <= high := by
        dsimp [low, high, sectionSixBuchstabClamp]
        exact d900D_clamp_mono hraw
      have hlow_pos : 0 < low := hl.trans_le (le_max_left _ _)
      have hhigh_pos : 0 < high := hlow_pos.trans_le hordered
      have hLower : (a + 1) * high <= B := by
        have hmul := mul_le_mul_of_nonneg_left hhigh_raw (by positivity : 0 <= a + 1)
        dsimp [rawH] at hmul
        have heq : (a + 1) * (B / (a + 1)) = B := by
          have ha1 : a + 1 ≠ 0 := by positivity
          field_simp [ha1]
        rw [heq] at hmul
        exact hmul
      have hUpper : B <= (b + 1) * low := by
        have hmul := mul_le_mul_of_nonneg_left hlow_raw
          (by linarith [haOne, hab] : 0 <= b + 1)
        dsimp [rawL] at hmul
        have heq : (b + 1) * (B / (b + 1)) = B := by
          have hb1 : b + 1 ≠ 0 := by linarith [haOne, hab]
          field_simp [hb1]
        rw [heq] at hmul
        exact hmul
      simpa only [low, high] using
        (d900D_secant_branch_le hu hv hw hlow_pos hordered
          haOne hab hbTwo hLower hUpper)

private theorem d900D_grid_bounds (i : Fin 8) :
    (1 : Real) <= uniformRealGridLower 1 2 i /\
      uniformRealGridLower 1 2 i <= uniformRealGridUpper 1 2 i /\
      uniformRealGridUpper 1 2 i <= 2 := by
  have h := uniformRealGrid_bounds (a := (1 : Real)) (b := 2)
    (n := 8) (by norm_num) (by norm_num) i
  exact h

private theorem d900D_cell_order
    {B l h a b : Real} (hB : 0 < B)
    (ha : 1 <= a) (hab : a <= b) :
    (sectionSixBuchstabArgumentCell B l h a b).1 <=
      (sectionSixBuchstabArgumentCell B l h a b).2 := by
  dsimp [sectionSixBuchstabArgumentCell]
  apply d900D_clamp_mono
  exact d900D_raw_order hB ha hab

private theorem d900D_cell_integrable
    {u v w B l h a b : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h) (hB : 2 * h <= B)
    (ha : 1 <= a) (hab : a <= b) :
    IntervalIntegrable
      (fun t : Real => buchstabFunction ((B - t) / t) /
        (u * v * w * t ^ 2)) volume
      (sectionSixBuchstabArgumentCell B l h a b).1
      (sectionSixBuchstabArgumentCell B l h a b).2 := by
  have hlow : l <= (sectionSixBuchstabArgumentCell B l h a b).1 := by
    exact le_max_left _ _
  have hhigh : (sectionSixBuchstabArgumentCell B l h a b).2 <= h := by
    dsimp [sectionSixBuchstabArgumentCell, sectionSixBuchstabClamp]
    exact max_le hlh (min_le_left _ _)
  have hBpos : 0 < B := by nlinarith [hl, hlh, hB]
  have horder :
      (sectionSixBuchstabArgumentCell B l h a b).1 <=
        (sectionSixBuchstabArgumentCell B l h a b).2 :=
    d900D_cell_order (B := B) (l := l) (h := h) hBpos ha hab
  have hglob := sectionSixBuchstabFiber_intervalIntegrable
    (B := B) (l := l) (h := h) hu hv hw hl hlh hB
  apply hglob.mono_set
  rw [uIcc_of_le horder, uIcc_of_le hlh] at *
  intro t ht
  exact ⟨hlow.trans ht.1, ht.2.trans hhigh⟩

private theorem d900D_pointwise_cell
    {u v w B l h : Real} (i : Fin 8)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h) (hB : 0 < B) :
    (∫ t in
        (sectionSixBuchstabArgumentCell B l h
          (uniformRealGridLower 1 2 i)
          (uniformRealGridUpper 1 2 i)).1..
        (sectionSixBuchstabArgumentCell B l h
          (uniformRealGridLower 1 2 i)
          (uniformRealGridUpper 1 2 i)).2,
      buchstabFunction ((B - t) / t) /
        (u * v * w * t ^ 2)) <=
      sectionSixBuchstabSecantPayload u v w B
        (sectionSixBuchstabArgumentCell B l h
          (uniformRealGridLower 1 2 i)
          (uniformRealGridUpper 1 2 i)).1
        (sectionSixBuchstabArgumentCell B l h
          (uniformRealGridLower 1 2 i)
          (uniformRealGridUpper 1 2 i)).2
        (uniformRealGridLower 1 2 i)
        (uniformRealGridUpper 1 2 i) := by
  have hb := d900D_grid_bounds i
  exact d900D_clamped_cell_le hu hv hw hl hlh hb.1 hb.2.1 hb.2.2 hB

private def d900DPoint (B l h : Real) (k : Nat) : Real :=
  sectionSixBuchstabClamp l h (B / (3 - (k : Real) / 8))

private theorem d900DPoint_zero
    {B l h : Real} (hlh : l <= h) (hthree : B <= 3 * l) :
    d900DPoint B l h 0 = l := by
  dsimp [d900DPoint]
  apply d900D_clamp_left hlh
  norm_num
  nlinarith [hthree]

private theorem d900DPoint_eight
    {B l h : Real} (hlh : l <= h) (hB : 2 * h <= B) :
    d900DPoint B l h 8 = h := by
  dsimp [d900DPoint]
  apply d900D_clamp_right hlh
  norm_num
  rw [le_div_iff₀ (by norm_num : (0 : Real) < 2)]
  nlinarith [hB]

private theorem d900DPoint_order
    {B l h : Real} (_hlh : l <= h) (hB : 0 < B)
    {k : Nat} (hk : k < 8) :
    d900DPoint B l h k <= d900DPoint B l h (k + 1) := by
  apply d900D_clamp_mono
  have hkR : (k : Real) < 8 := by exact_mod_cast hk
  have hk1 : k + 1 < 9 := by omega
  have hk1R : ((k + 1 : Nat) : Real) < 9 := by exact_mod_cast hk1
  have hd0 : 0 < 3 - (k : Real) / 8 := by norm_num; linarith
  have hd1 : 0 < 3 - ((k + 1 : Nat) : Real) / 8 := by norm_num; linarith
  have hden : 3 - ((k + 1 : Nat) : Real) / 8 <= 3 - (k : Real) / 8 := by
    norm_num
    norm_num at hkR ⊢
    linarith
  exact (div_le_div_iff_of_pos_left hB hd0 hd1).2 hden

private theorem d900DPoint_cell_eq
    {B l h : Real} {k : Nat} (hk : k < 8) :
    d900DPoint B l h k =
      (sectionSixBuchstabArgumentCell B l h
        (uniformRealGridLower 1 2 (Fin.rev (Fin.ofNat 8 k)))
        (uniformRealGridUpper 1 2 (Fin.rev (Fin.ofNat 8 k)))).1 /\
    d900DPoint B l h (k + 1) =
      (sectionSixBuchstabArgumentCell B l h
        (uniformRealGridLower 1 2 (Fin.rev (Fin.ofNat 8 k)))
        (uniformRealGridUpper 1 2 (Fin.rev (Fin.ofNat 8 k)))).2 := by
  interval_cases k <;>
    norm_num [d900DPoint, sectionSixBuchstabArgumentCell,
      uniformRealGridLower, uniformRealGridUpper, Fin.val_rev]

private theorem d900DPoint_integrable
    {u v w B l h : Real} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h) (hB : 2 * h <= B)
    {k : Nat} (hk : k < 8) :
    IntervalIntegrable
      (fun t : Real => buchstabFunction ((B - t) / t) /
        (u * v * w * t ^ 2)) volume
      (d900DPoint B l h k) (d900DPoint B l h (k + 1)) := by
  rw [(d900DPoint_cell_eq hk).1, (d900DPoint_cell_eq hk).2]
  have hb := d900D_grid_bounds (Fin.rev (Fin.ofNat 8 k))
  exact d900D_cell_integrable hu hv hw hl hlh hB hb.1 hb.2.1

private def d900DPayload
    (u v w B l h : Real) (i : Fin 8) : Real :=
  sectionSixBuchstabSecantPayload u v w B
    (sectionSixBuchstabArgumentCell B l h
      (uniformRealGridLower 1 2 i)
      (uniformRealGridUpper 1 2 i)).1
    (sectionSixBuchstabArgumentCell B l h
      (uniformRealGridLower 1 2 i)
      (uniformRealGridUpper 1 2 i)).2
    (uniformRealGridLower 1 2 i)
    (uniformRealGridUpper 1 2 i)

private def d900DPayloadNat
    (u v w B l h : Real) (k : Nat) : Real :=
  d900DPayload u v w B l h (Fin.rev (Fin.ofNat 8 k))

theorem sectionSixBuchstabInverseEightSecants_le
    {u v w B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h)
    (hB : 2 * h <= B) (hthree : B <= 3 * l) :
    let cell := fun i : Fin 8 =>
      sectionSixBuchstabArgumentCell B l h
        (uniformRealGridLower (1 : Real) 2 i)
        (uniformRealGridUpper (1 : Real) 2 i)
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) /
        (u * v * w * t ^ 2)) <=
      ∑ i : Fin 8,
        sectionSixBuchstabSecantPayload u v w B
          (cell i).1 (cell i).2
          (uniformRealGridLower (1 : Real) 2 i)
          (uniformRealGridUpper (1 : Real) 2 i) := by
  dsimp only
  let f : Real -> Real := fun t =>
    buchstabFunction ((B - t) / t) /
      (u * v * w * t ^ 2)
  let point := d900DPoint B l h
  let payload := d900DPayload u v w B l h
  have hBpos : 0 < B := by linarith
  have hsum :
      (∑ k ∈ Finset.range 8, ∫ t in point k..point (k + 1), f t) =
        ∫ t in point 0..point 8, f t := by
    exact intervalIntegral.sum_integral_adjacent_intervals
      (f := f) (μ := (volume : Measure Real)) (a := point) (n := 8)
      (fun k hk => d900DPoint_integrable hu hv hw hl hlh hB hk)
  have hpartition :
      (∫ t in l..h, f t) =
        ∑ k ∈ Finset.range 8, ∫ t in point k..point (k + 1), f t := by
    rw [hsum]
    simp [point, d900DPoint_zero hlh hthree,
      d900DPoint_eight hlh hB]
  have hcell : ∀ k : Nat, k < 8 ->
      (∫ t in point k..point (k + 1), f t) <=
        d900DPayloadNat u v w B l h k := by
    intro k hk
    dsimp [d900DPayloadNat, d900DPayload, point, f]
    rw [(d900DPoint_cell_eq hk).1, (d900DPoint_cell_eq hk).2]
    exact d900D_pointwise_cell (Fin.rev (Fin.ofNat 8 k))
      hu hv hw hl hlh hBpos
  calc
    (∫ t in l..h, f t) =
        ∑ k ∈ Finset.range 8, ∫ t in point k..point (k + 1), f t := hpartition
    _ <= ∑ k ∈ Finset.range 8, d900DPayloadNat u v w B l h k := by
      exact Finset.sum_le_sum fun k hk => hcell k (Finset.mem_range.mp hk)
    _ = ∑ i : Fin 8, payload i := by
      dsimp [payload, d900DPayloadNat, d900DPayload]
      rw [← Equiv.sum_comp Fin.revPerm]
      rfl

end

end PrimesRestrictedDigits
