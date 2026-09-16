import PrimesRestrictedDigits.BasicEstimates.BuchstabRefinedTailEnvelopeD900B
import PrimesRestrictedDigits.BasicEstimates.BuchstabMiddleEightCellEnvelopeD900C
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabEightSecantFiberD900D
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixBuchstabClampedRefinedFiberD900E -/
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped BigOperators
namespace PrimesRestrictedDigits
noncomputable section
def sectionSixBuchstabRefinedFiberBound
    (u v w B l h : Real) : Real :=
  let m13 := sectionSixBuchstabClamp l h (4 * B / 17)
  let m4 := sectionSixBuchstabClamp m13 h (B / 4)
  let m3 := sectionSixBuchstabClamp m4 h (B / 3)
  let middleCell := fun i : Fin 8 =>
    sectionSixBuchstabArgumentCell B m4 m3
      (uniformRealGridLower (2 : Real) 3 i)
      (uniformRealGridUpper (2 : Real) 3 i)
  let inverseCell := fun i : Fin 8 =>
    sectionSixBuchstabArgumentCell B m3 h
      (uniformRealGridLower (1 : Real) 2 i)
      (uniformRealGridUpper (1 : Real) 2 i)
  sectionSixBuchstabConstantPayload u v w l m13 (281 / 500) +
  sectionSixBuchstabConstantPayload u v w m13 m4
    (564383 / 1000000) +
  (∑ i : Fin 8,
    sectionSixBuchstabConstantPayload u v w
      (middleCell i).1 (middleCell i).2
      (sectionSixBuchstabMiddleEightCellCap i)) +
  ∑ i : Fin 8,
    sectionSixBuchstabSecantPayload u v w B
      (inverseCell i).1 (inverseCell i).2
      (uniformRealGridLower (1 : Real) 2 i)
      (uniformRealGridUpper (1 : Real) 2 i)
private theorem d900E_clamp_left
    {l h x : Real} (hlh : l <= h) (hx : x <= l) :
    sectionSixBuchstabClamp l h x = l := by
  unfold sectionSixBuchstabClamp
  rw [min_eq_right (hx.trans hlh), max_eq_left hx]
private theorem d900E_clamp_right
    {l h x : Real} (hlh : l <= h) (hx : h <= x) :
    sectionSixBuchstabClamp l h x = h := by
  unfold sectionSixBuchstabClamp
  rw [min_eq_left hx, max_eq_right hlh]
private theorem d900E_clamp_mono
    {l h x y : Real} (hxy : x <= y) :
    sectionSixBuchstabClamp l h x <= sectionSixBuchstabClamp l h y := by
  unfold sectionSixBuchstabClamp
  exact max_le_max_left l (min_le_min_left h hxy)
private theorem d900E_clamp_mem {l h x : Real} (hlh : l <= h) :
    l <= sectionSixBuchstabClamp l h x ∧
      sectionSixBuchstabClamp l h x <= h := by
  exact ⟨le_max_left _ _, max_le hlh (min_le_left _ _)⟩
private theorem d900E_constant_integral
    {C u v w l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h) :
    (∫ t in l..h, C / (u * v * w * t ^ 2)) =
      sectionSixBuchstabConstantPayload u v w l h C := by
  rcases hlh.eq_or_lt with rfl | hlh
  · simp [sectionSixBuchstabConstantPayload]
  · let K : Real := C / (u * v * w)
    have hderiv : ∀ t : Real, t ∈ uIcc l h ->
        HasDerivAt (fun s : Real => -K * s⁻¹)
          (C / (u * v * w * t ^ 2)) t := by
      intro t ht
      rw [uIcc_of_le hlh.le] at ht
      have htPos : 0 < t := hl.trans_le ht.1
      dsimp only [K]
      convert (hasDerivAt_inv htPos.ne').const_mul
        (-(C / (u * v * w))) using 1 <;>
          first | rfl | field_simp
    have hint : IntervalIntegrable
        (fun t : Real => C / (u * v * w * t ^ 2)) volume l h := by
      apply ContinuousOn.intervalIntegrable
      apply continuousOn_of_forall_continuousAt
      intro t ht
      rw [uIcc_of_le hlh.le] at ht
      have htPos : 0 < t := hl.trans_le ht.1
      have hden : u * v * w * t ^ 2 ≠ 0 := by positivity
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    dsimp [K, sectionSixBuchstabConstantPayload]
    field_simp
    ring
private theorem d900E_constant_branch_le
    {C u v w B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h) (hB : 2 * h <= B)
    (hpoint : ∀ t : Real, t ∈ Icc l h ->
      buchstabFunction ((B - t) / t) <= C) :
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) /
        (u * v * w * t ^ 2)) <=
      sectionSixBuchstabConstantPayload u v w l h C := by
  have hfun := sectionSixBuchstabFiber_intervalIntegrable
    hu hv hw hl hlh hB
  have hconst : IntervalIntegrable
      (fun t : Real => C / (u * v * w * t ^ 2)) volume l h := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [uIcc_of_le hlh] at ht
    have htPos : 0 < t := hl.trans_le ht.1
    have hden : u * v * w * t ^ 2 ≠ 0 := by positivity
    fun_prop
  calc
    (∫ t in l..h,
        buchstabFunction ((B - t) / t) /
          (u * v * w * t ^ 2)) <=
        ∫ t in l..h, C / (u * v * w * t ^ 2) := by
      apply intervalIntegral.integral_mono_on hlh hfun hconst
      intro t ht
      have htPos : 0 < t := hl.trans_le ht.1
      have hden : 0 < u * v * w * t ^ 2 := by positivity
      exact (div_le_div_iff_of_pos_right hden).2 (hpoint t ht)
    _ = _ := d900E_constant_integral hu hv hw hl hlh
private theorem d900E_middle_grid_bounds (i : Fin 8) :
    (2 : Real) <= uniformRealGridLower 2 3 i ∧
      uniformRealGridLower 2 3 i <= uniformRealGridUpper 2 3 i ∧
      uniformRealGridUpper 2 3 i <= 3 := by
  exact uniformRealGrid_bounds (a := (2 : Real)) (b := 3)
    (n := 8) (by norm_num) (by norm_num) i
private theorem d900E_raw_order
    {B a b : Real} (hB : 0 < B) (ha : 1 <= a)
    (hab : a <= b) : B / (b + 1) <= B / (a + 1) := by
  have ha1 : 0 < a + 1 := by linarith
  have hb1 : 0 < b + 1 := by linarith
  rw [div_le_div_iff_of_pos_left hB hb1 ha1]
  linarith
private theorem d900E_middle_cell_le
    {u v w B l h a b C : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h) (hB : 0 < B)
    (hTwo : 2 * h <= B)
    (ha : 2 <= a) (hab : a <= b) (_hb : b <= 3)
    (hcap : ∀ y : Real, a <= y -> y <= b ->
      buchstabFunction y <= C) :
    (∫ t in
        (sectionSixBuchstabArgumentCell B l h a b).1..
        (sectionSixBuchstabArgumentCell B l h a b).2,
      buchstabFunction ((B - t) / t) /
        (u * v * w * t ^ 2)) <=
      sectionSixBuchstabConstantPayload u v w
        (sectionSixBuchstabArgumentCell B l h a b).1
        (sectionSixBuchstabArgumentCell B l h a b).2 C := by
  let rawL : Real := B / (b + 1)
  let rawH : Real := B / (a + 1)
  let low : Real := sectionSixBuchstabClamp l h rawL
  let high : Real := sectionSixBuchstabClamp l h rawH
  have hraw : rawL <= rawH := by
    dsimp [rawL, rawH]
    exact d900E_raw_order hB (by linarith [ha]) hab
  change (∫ t in low..high,
      buchstabFunction ((B - t) / t) /
        (u * v * w * t ^ 2)) <=
      sectionSixBuchstabConstantPayload u v w low high C
  by_cases hleft : rawH <= l
  · have hlow : low = l := by
      dsimp [low]
      exact d900E_clamp_left hlh (hraw.trans hleft)
    have hhigh : high = l := by
      dsimp [high]
      exact d900E_clamp_left hlh hleft
    rw [hlow, hhigh]
    simp [sectionSixBuchstabConstantPayload]
  · by_cases hright : h <= rawL
    · have hlow : low = h := by
        dsimp [low]
        exact d900E_clamp_right hlh hright
      have hhigh : high = h := by
        dsimp [high]
        exact d900E_clamp_right hlh (hright.trans hraw)
      rw [hlow, hhigh]
      simp [sectionSixBuchstabConstantPayload]
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
        dsimp [low, high]
        exact d900E_clamp_mono hraw
      have hlow_pos : 0 < low := hl.trans_le (le_max_left _ _)
      have hhigh_pos : 0 < high := hlow_pos.trans_le hordered
      have hhigh_le : high <= h := by
        dsimp [high, sectionSixBuchstabClamp]
        exact max_le hlh (min_le_left _ _)
      have hTwoHigh : 2 * high <= B := by
        have hh := mul_le_mul_of_nonneg_left hhigh_le
          (by norm_num : (0 : Real) <= 2)
        linarith
      have hLower : (a + 1) * high <= B := by
        have hmul := mul_le_mul_of_nonneg_left hhigh_raw (by positivity : 0 <= a + 1)
        dsimp [rawH] at hmul
        have heq : (a + 1) * (B / (a + 1)) = B := by
          field_simp [show a + 1 ≠ 0 by positivity]
        rw [heq] at hmul
        exact hmul
      have hUpper : B <= (b + 1) * low := by
        have hmul := mul_le_mul_of_nonneg_left hlow_raw
          (by linarith [ha, hab] : 0 <= b + 1)
        dsimp [rawL] at hmul
        have heq : (b + 1) * (B / (b + 1)) = B := by
          field_simp [show b + 1 ≠ 0 by linarith [ha, hab]]
        rw [heq] at hmul
        exact hmul
      have hconst := d900E_constant_branch_le hu hv hw hlow_pos hordered
        hTwoHigh (fun t ht => by
          have htPos : 0 < t := hlow_pos.trans_le ht.1
          have hyLower : a <= (B - t) / t := by
            rw [le_div_iff₀ htPos]
            nlinarith [hLower, ht.2]
          have hyUpper : (B - t) / t <= b := by
            rw [div_le_iff₀ htPos]
            nlinarith [hUpper, ht.1]
          exact hcap _ hyLower hyUpper)
      exact hconst
private def d900EMiddlePoint (B l h : Real) (k : Nat) : Real :=
  sectionSixBuchstabClamp l h (B / (4 - (k : Real) / 8))
private theorem d900EMiddlePoint_cell_eq
    {B l h : Real} {k : Nat} (hk : k < 8) :
    d900EMiddlePoint B l h k =
      (sectionSixBuchstabArgumentCell B l h
        (uniformRealGridLower (2 : Real) 3 (Fin.rev (Fin.ofNat 8 k)))
        (uniformRealGridUpper (2 : Real) 3 (Fin.rev (Fin.ofNat 8 k)))).1 /\
    d900EMiddlePoint B l h (k + 1) =
      (sectionSixBuchstabArgumentCell B l h
        (uniformRealGridLower (2 : Real) 3 (Fin.rev (Fin.ofNat 8 k)))
        (uniformRealGridUpper (2 : Real) 3 (Fin.rev (Fin.ofNat 8 k)))).2 := by
  interval_cases k <;>
    norm_num [d900EMiddlePoint, sectionSixBuchstabArgumentCell,
      uniformRealGridLower, uniformRealGridUpper, Fin.val_rev]
private def d900EMiddlePayloadNat
    (u v w B m4 m3 : Real) (k : Nat) : Real :=
  sectionSixBuchstabConstantPayload u v w
    (sectionSixBuchstabArgumentCell B m4 m3
      (uniformRealGridLower (2 : Real) 3 (Fin.rev (Fin.ofNat 8 k)))
      (uniformRealGridUpper (2 : Real) 3 (Fin.rev (Fin.ofNat 8 k)))).1
    (sectionSixBuchstabArgumentCell B m4 m3
      (uniformRealGridLower (2 : Real) 3 (Fin.rev (Fin.ofNat 8 k)))
      (uniformRealGridUpper (2 : Real) 3 (Fin.rev (Fin.ofNat 8 k)))).2
      (sectionSixBuchstabMiddleEightCellCap (Fin.rev (Fin.ofNat 8 k)))
private theorem d900E_middle_sum_le
    {u v w B m4 m3 : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hm4 : 0 < m4) (hm43 : m4 <= m3) (hB : 2 * m3 <= B)
    (hleft : sectionSixBuchstabClamp m4 m3 (B / 4) = m4)
    (hright : sectionSixBuchstabClamp m4 m3 (B / 3) = m3) :
    (∫ t in m4..m3,
      buchstabFunction ((B - t) / t) /
        (u * v * w * t ^ 2)) <=
      ∑ i : Fin 8, sectionSixBuchstabConstantPayload u v w
        (sectionSixBuchstabArgumentCell B m4 m3
          (uniformRealGridLower (2 : Real) 3 i)
          (uniformRealGridUpper (2 : Real) 3 i)).1
        (sectionSixBuchstabArgumentCell B m4 m3
          (uniformRealGridLower (2 : Real) 3 i)
          (uniformRealGridUpper (2 : Real) 3 i)).2
        (sectionSixBuchstabMiddleEightCellCap i) := by
  let f : Real -> Real := fun t =>
    buchstabFunction ((B - t) / t) /
      (u * v * w * t ^ 2)
  let point := d900EMiddlePoint B m4 m3
  have hsum :
      (∑ k ∈ Finset.range 8, ∫ t in point k..point (k + 1), f t) =
        ∫ t in point 0..point 8, f t := by
    exact intervalIntegral.sum_integral_adjacent_intervals
      (f := f) (μ := (volume : Measure Real)) (a := point) (n := 8)
      (fun k hk => by
        dsimp [point]
        rw [(d900EMiddlePoint_cell_eq hk).1,
          (d900EMiddlePoint_cell_eq hk).2]
        have hb := d900E_middle_grid_bounds
          (Fin.rev (Fin.ofNat 8 k))
        have hlow : 0 <
            (sectionSixBuchstabArgumentCell B m4 m3
              (uniformRealGridLower (2 : Real) 3 (Fin.rev (Fin.ofNat 8 k)))
              (uniformRealGridUpper (2 : Real) 3 (Fin.rev (Fin.ofNat 8 k)))).1 := by
          have : m4 <=
              (sectionSixBuchstabArgumentCell B m4 m3
                (uniformRealGridLower (2 : Real) 3 (Fin.rev (Fin.ofNat 8 k)))
                (uniformRealGridUpper (2 : Real) 3 (Fin.rev (Fin.ofNat 8 k)))).1 :=
            le_max_left _ _
          exact hm4.trans_le this
        have hraw := d900E_raw_order (B := B) (a :=
          uniformRealGridLower (2 : Real) 3 (Fin.rev (Fin.ofNat 8 k)))
          (b := uniformRealGridUpper (2 : Real) 3 (Fin.rev (Fin.ofNat 8 k)))
          (by linarith [hB, hm4, hm43]) (by linarith [hb.1]) hb.2.1
        have horder := d900E_clamp_mono (l := m4) (h := m3) hraw
        have hhighle :
            (sectionSixBuchstabArgumentCell B m4 m3
              (uniformRealGridLower (2 : Real) 3 (Fin.rev (Fin.ofNat 8 k)))
              (uniformRealGridUpper (2 : Real) 3 (Fin.rev (Fin.ofNat 8 k)))).2 <= m3 := by
          dsimp [sectionSixBuchstabArgumentCell, sectionSixBuchstabClamp]
          exact max_le hm43 (min_le_left _ _)
        exact sectionSixBuchstabFiber_intervalIntegrable hu hv hw hlow
          horder (by linarith [hB, hhighle]))
  have hleft' : point 0 = m4 := by
    simpa [point, d900EMiddlePoint] using hleft
  have hright' : point 8 = m3 := by
    norm_num [point, d900EMiddlePoint]
    exact hright
  have hpartition :
      (∫ t in m4..m3, f t) =
        ∑ k ∈ Finset.range 8, ∫ t in point k..point (k + 1), f t := by
    rw [hsum, hleft', hright']
  have hcell : ∀ k : Nat, k < 8 ->
      (∫ t in point k..point (k + 1), f t) <=
        d900EMiddlePayloadNat u v w B m4 m3 k := by
    intro k hk
    dsimp [point]
    rw [(d900EMiddlePoint_cell_eq hk).1,
      (d900EMiddlePoint_cell_eq hk).2]
    have hb := d900E_middle_grid_bounds (Fin.rev (Fin.ofNat 8 k))
    exact d900E_middle_cell_le hu hv hw hm4 hm43 (by linarith) (by linarith)
      hb.1 hb.2.1 hb.2.2 (fun y hya hyb =>
        buchstabFunction_le_middleEightCellEnvelope
          (Fin.rev (Fin.ofNat 8 k)) hya hyb)
  calc
    (∫ t in m4..m3, f t) =
        ∑ k ∈ Finset.range 8, ∫ t in point k..point (k + 1), f t := hpartition
    _ <= ∑ k ∈ Finset.range 8, d900EMiddlePayloadNat u v w B m4 m3 k := by
      exact Finset.sum_le_sum fun k hk => hcell k (Finset.mem_range.mp hk)
    _ = _ := by
      dsimp [d900EMiddlePayloadNat]
      rw [← Equiv.sum_comp Fin.revPerm]
      rfl
theorem sectionSixBuchstabClampedRefinedFiber_le
    {u v w B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h) (hB : 2 * h <= B) :
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) /
        (u * v * w * t ^ 2)) <=
      sectionSixBuchstabRefinedFiberBound u v w B l h := by
  dsimp only [sectionSixBuchstabRefinedFiberBound]
  let m13 := sectionSixBuchstabClamp l h (4 * B / 17)
  let m4 := sectionSixBuchstabClamp m13 h (B / 4)
  let m3 := sectionSixBuchstabClamp m4 h (B / 3)
  let f : Real -> Real := fun t =>
    buchstabFunction ((B - t) / t) /
      (u * v * w * t ^ 2)
  have hm13 := d900E_clamp_mem (x := 4 * B / 17) hlh
  change l <= m13 ∧ m13 <= h at hm13
  have hm4 := d900E_clamp_mem (x := B / 4) hm13.2
  change m13 <= m4 ∧ m4 <= h at hm4
  have hm3 := d900E_clamp_mem (x := B / 3) hm4.2
  change m4 <= m3 ∧ m3 <= h at hm3
  have hm13pos : 0 < m13 := hl.trans_le hm13.1
  have hm4pos : 0 < m4 := hm13pos.trans_le hm4.1
  have hm3pos : 0 < m3 := hm4pos.trans_le hm3.1
  have hB13 : 2 * m13 <= B := by linarith [hm13.2]
  have hB4 : 2 * m4 <= B := by linarith [hm4.2]
  have hB3 : 2 * m3 <= B := by linarith [hm3.2]
  have hInt0 := sectionSixBuchstabFiber_intervalIntegrable
    hu hv hw hl hm13.1 hB13
  have hInt1 := sectionSixBuchstabFiber_intervalIntegrable
    hu hv hw hm13pos hm4.1 hB4
  have hInt2 := sectionSixBuchstabFiber_intervalIntegrable
    hu hv hw hm4pos hm3.1 hB3
  have hInt3 := sectionSixBuchstabFiber_intervalIntegrable
    hu hv hw hm3pos hm3.2 hB
  have htail : (∫ t in l..m13, f t) <=
      sectionSixBuchstabConstantPayload u v w l m13 (281 / 500) := by
    by_cases hc : 4 * B / 17 <= l
    · have heq : m13 = l := by
        exact d900E_clamp_left hlh (by nlinarith)
      rw [heq]
      simp [sectionSixBuchstabConstantPayload]
    · have hm13cut : m13 <= 4 * B / 17 := by
        dsimp [m13, sectionSixBuchstabClamp]
        exact max_le (le_of_not_ge hc) (min_le_right _ _)
      apply d900E_constant_branch_le hu hv hw hl hm13.1 hB13
      intro t ht
      have htPos : 0 < t := hl.trans_le ht.1
      have hy : 13 / 4 <= (B - t) / t := by
        rw [le_div_iff₀ htPos]
        nlinarith [hm13cut, ht.2]
      exact buchstabFunction_le_refinedTailEnvelope hy
  have hlegacy : (∫ t in m13..m4, f t) <=
      sectionSixBuchstabConstantPayload u v w m13 m4
        (564383 / 1000000) := by
    by_cases hc : h <= B / 4
    · have heq : m4 = h := d900E_clamp_right hm13.2 hc
      rw [heq]
      change (∫ t in m13..h,
        buchstabFunction ((B - t) / t) /
          (u * v * w * t ^ 2)) <= _
      apply d900E_constant_branch_le hu hv hw hm13pos (by linarith) hB
      intro t ht
      have htPos : 0 < t := hm13pos.trans_le ht.1
      have hy : 3 <= (B - t) / t := by
        rw [le_div_iff₀ htPos]
        nlinarith [hc, ht.2]
      exact buchstabFunction_le_tailEnvelope hy
    · by_cases hc' : B / 4 <= m13
      · have heq : m4 = m13 := d900E_clamp_left hm13.2 hc'
        rw [heq]
        simp [sectionSixBuchstabConstantPayload]
      · have hm4cut : m4 <= B / 4 := by
          dsimp [m4, sectionSixBuchstabClamp]
          exact max_le (le_of_not_ge hc') (min_le_right _ _)
        apply d900E_constant_branch_le hu hv hw hm13pos hm4.1 hB4
        intro t ht
        have htPos : 0 < t := hm13pos.trans_le ht.1
        have hy : 3 <= (B - t) / t := by
          rw [le_div_iff₀ htPos]
          nlinarith [hm4cut, ht.2]
        exact buchstabFunction_le_tailEnvelope hy
  have hmiddleLeft : sectionSixBuchstabClamp m4 m3 (B / 4) = m4 := by
    by_cases hxm : B / 4 <= m13
    · have hm4eq : m4 = m13 := d900E_clamp_left hm13.2 hxm
      have hx : B / 4 <= m4 := by simpa [hm4eq] using hxm
      exact d900E_clamp_left (l := m4) (h := m3) (x := B / 4) hm3.1 hx
    · by_cases hxh : h <= B / 4
      · have hm4eq : m4 = h := d900E_clamp_right hm13.2 hxh
        have hm3eq : m3 = h := d900E_clamp_right hm4.2 (by linarith)
        rw [hm4eq, hm3eq]
        exact d900E_clamp_right (l := h) (h := h) (x := B / 4) (by rfl) hxh
      · have hxlt : m13 < B / 4 := lt_of_not_ge hxm
        have hxhi : B / 4 < h := lt_of_not_ge hxh
        have hm4eq : m4 = B / 4 := by
          dsimp [m4, sectionSixBuchstabClamp]
          rw [min_eq_right hxhi.le, max_eq_right hxlt.le]
        rw [hm4eq]
        have hm3lower : B / 4 <= m3 := by simpa [hm4eq] using hm3.1
        exact d900E_clamp_left (l := B / 4) (h := m3) (x := B / 4)
          hm3lower le_rfl
  have hmiddleRight : sectionSixBuchstabClamp m4 m3 (B / 3) = m3 := by
    by_cases hxm : B / 3 <= m4
    · have hm3eq : m3 = m4 := by
        simpa [m3] using
          d900E_clamp_left (l := m4) (h := h) (x := B / 3) hm4.2 hxm
      rw [hm3eq]
      exact d900E_clamp_left (l := m4) (h := m4) (x := B / 3) (by rfl) hxm
    · by_cases hxh : h <= B / 3
      · have hm3eq : m3 = h := d900E_clamp_right hm4.2 hxh
        rw [hm3eq]
        exact d900E_clamp_right (l := m4) (h := h) (x := B / 3) hm4.2 hxh
      · have hxlt : m4 < B / 3 := lt_of_not_ge hxm
        have hxhi : B / 3 < h := lt_of_not_ge hxh
        have hm3eq : m3 = B / 3 := by
          dsimp [m3, sectionSixBuchstabClamp]
          rw [min_eq_right hxhi.le, max_eq_right hxlt.le]
        rw [hm3eq]
        exact d900E_clamp_right (l := m4) (h := B / 3) (x := B / 3) hxlt.le le_rfl
  have hmiddle := d900E_middle_sum_le hu hv hw hm4pos hm3.1 hB3
    hmiddleLeft hmiddleRight
  have hinverse : (∫ t in m3..h, f t) <=
      ∑ i : Fin 8, sectionSixBuchstabSecantPayload u v w B
        (sectionSixBuchstabArgumentCell B m3 h
          (uniformRealGridLower (1 : Real) 2 i)
          (uniformRealGridUpper (1 : Real) 2 i)).1
        (sectionSixBuchstabArgumentCell B m3 h
          (uniformRealGridLower (1 : Real) 2 i)
          (uniformRealGridUpper (1 : Real) 2 i)).2
        (uniformRealGridLower (1 : Real) 2 i)
        (uniformRealGridUpper (1 : Real) 2 i) := by
    by_cases hc : h <= B / 3
    · have heq : m3 = h := d900E_clamp_right hm4.2 hc
      rw [heq]
      simp [sectionSixBuchstabArgumentCell, sectionSixBuchstabClamp,
        sectionSixBuchstabSecantPayload]
    · have hthree : B <= 3 * m3 := by
        have hlow : B / 3 <= m3 := by
          dsimp [m3, sectionSixBuchstabClamp]
          rw [min_eq_right (le_of_not_ge hc)]
          exact le_max_right _ _
        linarith
      exact sectionSixBuchstabInverseEightSecants_le hu hv hw hm3pos hm3.2 hB hthree
  have hsplit01 := intervalIntegral.integral_add_adjacent_intervals hInt0 hInt1
  have hsplit012 := intervalIntegral.integral_add_adjacent_intervals
    (hInt0.trans hInt1) hInt2
  have hsplitAll := intervalIntegral.integral_add_adjacent_intervals
    ((hInt0.trans hInt1).trans hInt2) hInt3
  calc
    (∫ t in l..h, f t) =
        (((∫ t in l..m13, f t) + ∫ t in m13..m4, f t) +
          ∫ t in m4..m3, f t) + ∫ t in m3..h, f t := by
      rw [hsplit01, hsplit012, hsplitAll]
    _ <= _ := by
      dsimp [f]
      exact add_le_add (add_le_add (add_le_add htail hlegacy) hmiddle) hinverse
end
end PrimesRestrictedDigits
