import PrimesRestrictedDigits.BasicEstimates.ConvexThreeAffineQuotient
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBelowCertificateNodes
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! Separate convexity of the actual-log charts, including continuity at `x = 0`. -/
open Set
namespace PrimesRestrictedDigits
noncomputable section
private def aoTheta : Real := 180001 / 500000
private def aoStart : Real := 69999 / 250000
private def aoSpan : Real := 40003 / 500000
private def aoC : Real := 564663 / 1000000
private def aoU (X : Real) : Real := aoStart + X
private def aoV (X k : Real) : Real := aoTheta / 2 - k * X
private def aoT (X k : Real) : Real := 3 * aoTheta / 2 - (1 - k) * X
private def aoW (X k : Real) : Real := aoTheta / 2 + k * X
private def aoQ (X k : Real) : Real := aoTheta - (1 - 2 * k) * X
private def aoMixedN (X k : Real) : Real := aoC * (4 * k - 1) * X / aoV X k + Real.log (aoTheta + 2 * k * X) - Real.log (aoTheta - X)
private def aoMixedN1 (X k : Real) : Real := aoC * (4 * k - 1) * (aoTheta / 2) / aoV X k ^ 2 + 2 * k / (aoTheta + 2 * k * X) + 1 / (aoTheta - X)
private def aoMixedN2 (X k : Real) : Real := aoC * (4 * k - 1) * aoTheta * k / aoV X k ^ 3 - (2 * k) ^ 2 / (aoTheta + 2 * k * X) ^ 2 + 1 / (aoTheta - X) ^ 2
private def aoMixedN3 (X k : Real) : Real := 3 * aoC * (4 * k - 1) * aoTheta * k ^ 2 / aoV X k ^ 4 + 2 * (2 * k) ^ 3 / (aoTheta + 2 * k * X) ^ 3 + 2 / (aoTheta - X) ^ 3
private def aoInverseN (X k : Real) : Real := Real.log (aoW X k) + Real.log (aoQ X k) - Real.log (aoV X k) - Real.log (aoTheta - X)
private def aoInverseN1 (X k : Real) : Real := k / aoW X k - (1 - 2 * k) / aoQ X k + k / aoV X k + 1 / (aoTheta - X)
private def aoInverseN2 (X k : Real) : Real := -(k ^ 2 / aoW X k ^ 2) - (1 - 2 * k) ^ 2 / aoQ X k ^ 2 + k ^ 2 / aoV X k ^ 2 + 1 / (aoTheta - X) ^ 2
private def aoInverseN3 (X k : Real) : Real := 2 * k ^ 3 / aoW X k ^ 3 - 2 * (1 - 2 * k) ^ 3 / aoQ X k ^ 3 + 2 * k ^ 3 / aoV X k ^ 3 + 2 / (aoTheta - X) ^ 3
private def aoMixedK1 (X k : Real) : Real := aoC * X * (2 * aoTheta - X) / aoV X k ^ 2 + 2 * X / (aoTheta + 2 * k * X)
private def aoMixedK2 (X k : Real) : Real := 2 * aoC * X ^ 2 * (2 * aoTheta - X) / aoV X k ^ 3 - 4 * X ^ 2 / (aoTheta + 2 * k * X) ^ 2
private def aoInverseK1 (X k : Real) : Real := X / aoW X k + 2 * X / aoQ X k + X / aoV X k
private def aoInverseK2 (X k : Real) : Real := -(X ^ 2 / aoW X k ^ 2) - 4 * X ^ 2 / aoQ X k ^ 2 + X ^ 2 / aoV X k ^ 2
private theorem hasDerivAt_affine {f : Real → Real} (a b x : Real) (hf : ∀ z, f z = a + b * z) : HasDerivAt f b x := by
  have h : HasDerivAt (fun z : Real => a + b * z) b x := by simpa using (hasDerivAt_const_mul (x := x) b).const_add a
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall hf)
private theorem ao_chart_pos {X k : Real} (hX : X ∈ Icc 0 aoSpan) (hk : k ∈ Icc 0 (1 / 2 : Real)) : 0 < aoU X ∧ 0 < aoV X k ∧ 0 < aoT X k ∧ 0 < aoW X k ∧ 0 < aoQ X k ∧ 0 < aoTheta - X ∧ 0 < aoTheta + 2 * k * X := by
  have hkX0 : 0 ≤ k * X := mul_nonneg hk.1 hX.1
  have hkX : k * X ≤ (1 / 2 : Real) * aoSpan := mul_le_mul hk.2 hX.2 hX.1 (by norm_num)
  norm_num [aoSpan] at hkX
  norm_num [aoU, aoV, aoT, aoW, aoQ, aoTheta, aoStart, aoSpan] at hX ⊢
  constructor; · linarith
  constructor; · linarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor <;> nlinarith
private theorem ao_mixed_derivatives {X k : Real} (hX : X ∈ Icc 0 aoSpan) (hk : k ∈ Icc (1 / 4 : Real) (1 / 2)) : HasDerivAt (fun z => aoMixedN z k) (aoMixedN1 X k) X ∧ HasDerivAt (fun z => aoMixedN1 z k) (aoMixedN2 X k) X ∧ HasDerivAt (fun z => aoMixedN2 z k) (aoMixedN3 X k) X := by
  have hp := ao_chart_pos hX ⟨by linarith [hk.1], hk.2⟩
  rcases hp with ⟨hU, hV, hT, hW, hQ, hA, hL⟩
  have hVd : HasDerivAt (fun z => aoV z k) (-k) X := hasDerivAt_affine (aoTheta / 2) (-k) X (fun z => by unfold aoV; ring)
  have hLd : HasDerivAt (fun z => aoTheta + 2 * k * z) (2 * k) X := hasDerivAt_affine aoTheta (2 * k) X (fun z => by ring)
  have hAd : HasDerivAt (fun z => aoTheta - z) (-1) X := hasDerivAt_affine aoTheta (-1) X (fun z => by ring)
  constructor
  · unfold aoMixedN aoMixedN1
    convert (((hasDerivAt_const_mul (x := X) (aoC * (4 * k - 1))).div hVd hV.ne').add
      (hLd.log hL.ne')).sub (hAd.log hA.ne') using 1 <;>
      first | rfl | (rw [show aoV X k = aoTheta / 2 - k * X by rfl]; ring)
  constructor
  · unfold aoMixedN1 aoMixedN2
    convert (((hasDerivAt_const X (aoC * (4 * k - 1) * (aoTheta / 2))).div
      (hVd.pow 2) (pow_ne_zero 2 hV.ne')).add
      ((hasDerivAt_const X (2 * k)).div hLd hL.ne')).add
      ((hasDerivAt_const X 1).div hAd hA.ne') using 1 <;>
      first | rfl | (simp only [Pi.pow_apply]; field_simp [aoV, hV.ne', hL.ne', hA.ne']; ring)
  · unfold aoMixedN2 aoMixedN3
    convert (((hasDerivAt_const X (aoC * (4 * k - 1) * aoTheta * k)).div
      (hVd.pow 3) (pow_ne_zero 3 hV.ne')).sub
      ((hasDerivAt_const X ((2 * k) ^ 2)).div (hLd.pow 2) (pow_ne_zero 2 hL.ne'))).add
      ((hasDerivAt_const X 1).div (hAd.pow 2) (pow_ne_zero 2 hA.ne')) using 1 <;>
      first | rfl | (simp only [Pi.pow_apply]; generalize hv0 : aoV X k = v at hV ⊢; generalize hl0 : aoTheta + 2 * k * X = l at hL ⊢; generalize ha0 : aoTheta - X = a at hA ⊢; field_simp [hV.ne', hL.ne', hA.ne']; ring)
private theorem ao_inverse_derivatives {X k : Real} (hX : X ∈ Icc 0 aoSpan) (hk : k ∈ Icc (0 : Real) (1 / 4)) : HasDerivAt (fun z => aoInverseN z k) (aoInverseN1 X k) X ∧ HasDerivAt (fun z => aoInverseN1 z k) (aoInverseN2 X k) X ∧ HasDerivAt (fun z => aoInverseN2 z k) (aoInverseN3 X k) X := by
  have hp := ao_chart_pos hX ⟨hk.1, hk.2.trans (by norm_num)⟩
  rcases hp with ⟨hU, hV, hT, hW, hQ, hA, hL⟩
  have hVd : HasDerivAt (fun z => aoV z k) (-k) X := hasDerivAt_affine (aoTheta / 2) (-k) X (fun z => by unfold aoV; ring)
  have hWd : HasDerivAt (fun z => aoW z k) k X := hasDerivAt_affine (aoTheta / 2) k X (fun z => by unfold aoW; ring)
  have hQd : HasDerivAt (fun z => aoQ z k) (-(1 - 2 * k)) X := hasDerivAt_affine aoTheta (-(1 - 2 * k)) X (fun z => by unfold aoQ; ring)
  have hAd : HasDerivAt (fun z => aoTheta - z) (-1) X := hasDerivAt_affine aoTheta (-1) X (fun z => by ring)
  constructor
  · unfold aoInverseN aoInverseN1
    convert (((hWd.log hW.ne').add (hQd.log hQ.ne')).sub (hVd.log hV.ne')).sub
      (hAd.log hA.ne') using 1 <;>
      first | rfl | ring_nf
  constructor
  · unfold aoInverseN1 aoInverseN2
    convert ((((hasDerivAt_const X k).div hWd hW.ne').sub
      ((hasDerivAt_const X (1 - 2 * k)).div hQd hQ.ne')).add
      ((hasDerivAt_const X k).div hVd hV.ne')).add
      ((hasDerivAt_const X 1).div hAd hA.ne') using 1 <;>
      first | rfl | ring_nf
  · unfold aoInverseN2 aoInverseN3
    convert (((((hasDerivAt_const X (k ^ 2)).div (hWd.pow 2)
      (pow_ne_zero 2 hW.ne')).neg).sub
      ((hasDerivAt_const X ((1 - 2 * k) ^ 2)).div (hQd.pow 2)
        (pow_ne_zero 2 hQ.ne'))).add
      ((hasDerivAt_const X (k ^ 2)).div (hVd.pow 2) (pow_ne_zero 2 hV.ne'))).add
      ((hasDerivAt_const X 1).div (hAd.pow 2) (pow_ne_zero 2 hA.ne')) using 1 <;>
      first | rfl | (simp only [Pi.pow_apply]; field_simp [aoV, aoW, aoQ, hV.ne', hW.ne', hQ.ne', hA.ne']; ring)
private theorem ao_mixed_signs {X k : Real} (hX : X ∈ Icc 0 aoSpan) (hk : k ∈ Icc (1 / 4 : Real) (1 / 2)) : 0 ≤ aoMixedN X k ∧ 0 ≤ aoMixedN2 X k ∧ 0 ≤ aoMixedN3 X k := by
  have hp := ao_chart_pos hX ⟨by linarith [hk.1], hk.2⟩
  rcases hp with ⟨hU, hV, hT, hW, hQ, hA, hL⟩
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have hk4 : 0 ≤ 4 * k - 1 := by linarith [hk.1]
  have hc : 0 ≤ aoC := by norm_num [aoC]
  have ht : 0 ≤ aoTheta := by norm_num [aoTheta]
  have hlog : 0 ≤ Real.log (aoTheta + 2 * k * X) - Real.log (aoTheta - X) := by
    exact sub_nonneg.mpr (Real.log_le_log hA (by nlinarith [mul_nonneg hk0 hX.1]))
  have hratio : 2 * k / (aoTheta + 2 * k * X) ≤ 1 / (aoTheta - X) := by
    rw [div_le_div_iff₀ hL hA]
    have hkt : 0 ≤ (1 - 2 * k) * aoTheta := mul_nonneg (by linarith [hk.2]) ht
    have hkx : 0 ≤ 4 * k * X := mul_nonneg (mul_nonneg (by norm_num) hk0) hX.1
    nlinarith
  have hsq : (2 * k) ^ 2 / (aoTheta + 2 * k * X) ^ 2 ≤
      1 / (aoTheta - X) ^ 2 := by
    have hs := pow_le_pow_left₀ (div_nonneg (mul_nonneg (by norm_num) hk0) hL.le) hratio 2
    simpa [div_pow] using hs
  constructor
  · unfold aoMixedN
    have hr := div_nonneg (mul_nonneg (mul_nonneg hc hk4) hX.1) hV.le
    nlinarith
  constructor
  · unfold aoMixedN2
    have hfirst : 0 ≤ aoC * (4 * k - 1) * aoTheta * k / aoV X k ^ 3 := by positivity
    nlinarith
  · unfold aoMixedN3
    positivity
private theorem ao_inverse_signs {X k : Real} (hX : X ∈ Icc 0 aoSpan) (hk : k ∈ Icc (0 : Real) (1 / 4)) : 0 ≤ aoInverseN X k ∧ 0 ≤ aoInverseN2 X k ∧ 0 ≤ aoInverseN3 X k := by
  have hp := ao_chart_pos hX ⟨hk.1, hk.2.trans (by norm_num)⟩
  rcases hp with ⟨hU, hV, hT, hW, hQ, hA, hL⟩
  have hVW : aoV X k ≤ aoW X k := by unfold aoV aoW; nlinarith [mul_nonneg hk.1 hX.1]
  have hAQ : aoTheta - X ≤ aoQ X k := by unfold aoQ; nlinarith [mul_nonneg hk.1 hX.1]
  have hkOne : 0 ≤ 1 - 2 * k := by linarith [hk.2]
  have hrat : 1 ≤ aoW X k * aoQ X k / (aoV X k * (aoTheta - X)) := by
    rw [le_div_iff₀ (mul_pos hV hA)]
    nlinarith [mul_nonneg (mul_nonneg hk.1 hX.1) (add_nonneg hA.le hW.le)]
  have hsqW : k ^ 2 / aoW X k ^ 2 ≤ k ^ 2 / aoV X k ^ 2 := by
    gcongr
  have hr : (1 - 2 * k) / aoQ X k ≤ 1 / (aoTheta - X) := by
    rw [div_le_div_iff₀ hQ hA]
    unfold aoQ
    nlinarith [mul_nonneg hk.1 (by norm_num [aoTheta] : 0 ≤ aoTheta)]
  have hsqQ : (1 - 2 * k) ^ 2 / aoQ X k ^ 2 ≤ 1 / (aoTheta - X) ^ 2 := by
    have hs := pow_le_pow_left₀ (div_nonneg hkOne hQ.le) hr 2
    simpa [div_pow] using hs
  constructor
  · unfold aoInverseN
    rw [show Real.log (aoW X k) + Real.log (aoQ X k) - Real.log (aoV X k) -
        Real.log (aoTheta - X) = Real.log (aoW X k * aoQ X k /
          (aoV X k * (aoTheta - X))) by
      rw [Real.log_div (mul_pos hW hQ).ne' (mul_pos hV hA).ne',
        Real.log_mul hW.ne' hQ.ne', Real.log_mul hV.ne' hA.ne']; ring]
    exact Real.log_nonneg hrat
  constructor
  · unfold aoInverseN2
    linarith
  · unfold aoInverseN3
    have hcubes : 2 * (1 - 2 * k) ^ 3 / aoQ X k ^ 3 ≤
        2 / (aoTheta - X) ^ 3 := by
      have hs := pow_le_pow_left₀ (div_nonneg hkOne hQ.le) hr 3
      calc
        2 * (1 - 2 * k) ^ 3 / aoQ X k ^ 3 = 2 * ((1 - 2 * k) / aoQ X k) ^ 3 := by rw [div_pow]; ring
        _ ≤ 2 * (1 / (aoTheta - X)) ^ 3 := mul_le_mul_of_nonneg_left hs (by norm_num)
        _ = 2 / (aoTheta - X) ^ 3 := by rw [div_pow]; ring
    have hwk : 0 ≤ 2 * k ^ 3 / aoW X k ^ 3 := div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hk.1 3)) (pow_nonneg hW.le 3)
    have hvk : 0 ≤ 2 * k ^ 3 / aoV X k ^ 3 := div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hk.1 3)) (pow_nonneg hV.le 3)
    have hkpos := add_nonneg hwk hvk
    linarith
private theorem ao_mixed_k_data {X k : Real} (hX : X ∈ Icc 0 aoSpan) (hk : k ∈ Icc (1 / 4 : Real) (1 / 2)) : HasDerivAt (fun t => aoMixedN X t) (aoMixedK1 X k) k ∧ HasDerivAt (fun t => aoMixedK1 X t) (aoMixedK2 X k) k ∧ 0 ≤ aoMixedK1 X k ∧ 0 ≤ aoMixedK2 X k := by
  rcases ao_chart_pos hX ⟨by linarith [hk.1], hk.2⟩ with ⟨hU, hV, hT, hW, hQ, hA, hL⟩
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have hVd : HasDerivAt (fun t => aoV X t) (-X) k := hasDerivAt_affine (aoTheta / 2) (-X) k (fun t => by unfold aoV; ring)
  have hLd : HasDerivAt (fun t => aoTheta + 2 * t * X) (2 * X) k := hasDerivAt_affine aoTheta (2 * X) k (fun t => by ring)
  have hxTheta : 0 ≤ 2 * aoTheta - X := by norm_num [aoTheta, aoSpan] at hX ⊢; linarith
  have hdom : 2 * aoV X k ^ 3 ≤ aoC * (2 * aoTheta - X) * (aoTheta + 2 * k * X) ^ 2 := by
    have hc : (1 / 2 : Real) ≤ aoC := by norm_num [aoC]
    have hvx : aoV X k ≤ 2 * aoTheta - X := by unfold aoV; nlinarith [mul_nonneg hk0 hX.1]
    have hvl : 2 * aoV X k ≤ aoTheta + 2 * k * X := by unfold aoV; nlinarith [mul_nonneg hk0 hX.1]
    calc
      2 * aoV X k ^ 3 = (1 / 2 : Real) * aoV X k * (2 * aoV X k) ^ 2 := by ring
      _ ≤ aoC * (2 * aoTheta - X) * (aoTheta + 2 * k * X) ^ 2 := by gcongr
  constructor
  · unfold aoMixedN aoMixedK1
    convert (((((hasDerivAt_affine (f := fun t => -aoC * X + 4 * aoC * X * t)
      (-aoC * X) (4 * aoC * X) k (fun t => rfl)).div hVd hV.ne').add
      (hLd.log hL.ne')).sub (hasDerivAt_const k (Real.log (aoTheta - X))))) using 1 <;>
      first | rfl | (funext t; dsimp; ring) | (rw [show aoV X k = aoTheta / 2 - k * X by rfl]; ring)
  constructor
  · unfold aoMixedK1 aoMixedK2
    convert (((hasDerivAt_const k (aoC * X * (2 * aoTheta - X))).div
      (hVd.pow 2) (pow_ne_zero 2 hV.ne')).add
      ((hasDerivAt_const k (2 * X)).div hLd hL.ne')) using 1 <;>
      first | rfl | (simp only [Pi.pow_apply]; field_simp [aoV, hV.ne', hL.ne']; ring)
  constructor
  · unfold aoMixedK1
    exact add_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num [aoC]) hX.1) hxTheta)
      (sq_nonneg _)) (div_nonneg (mul_nonneg (by norm_num) hX.1) hL.le)
  · unfold aoMixedK2
    rw [sub_nonneg, div_le_div_iff₀ (pow_pos hL 2) (pow_pos hV 3)]
    have hm := mul_le_mul_of_nonneg_left hdom (show 0 ≤ (2 : Real) * X ^ 2 by positivity)
    nlinarith
private theorem ao_inverse_k_data {X k : Real} (hX : X ∈ Icc 0 aoSpan) (hk : k ∈ Icc (0 : Real) (1 / 4)) : HasDerivAt (fun t => aoInverseN X t) (aoInverseK1 X k) k ∧ HasDerivAt (fun t => aoInverseK1 X t) (aoInverseK2 X k) k ∧ 0 ≤ aoInverseK2 X k * (aoV X k * aoT X k) + 2 * X * aoQ X k * aoInverseK1 X k := by
  rcases ao_chart_pos hX ⟨hk.1, hk.2.trans (by norm_num)⟩ with ⟨hU, hV, hT, hW, hQ, hA, hL⟩
  have hVd : HasDerivAt (fun t => aoV X t) (-X) k := hasDerivAt_affine (aoTheta / 2) (-X) k (fun t => by unfold aoV; ring)
  have hWd : HasDerivAt (fun t => aoW X t) X k := hasDerivAt_affine (aoTheta / 2) X k (fun t => by unfold aoW; ring)
  have hQd : HasDerivAt (fun t => aoQ X t) (2 * X) k := hasDerivAt_affine (aoTheta - X) (2 * X) k (fun t => by unfold aoQ; ring)
  constructor
  · unfold aoInverseN aoInverseK1
    convert (((hWd.log hW.ne').add (hQd.log hQ.ne')).sub (hVd.log hV.ne')).sub
      (hasDerivAt_const k (Real.log (aoTheta - X))) using 1 <;>
      first | rfl | ring_nf
  constructor
  · unfold aoInverseK1 aoInverseK2
    convert ((((hasDerivAt_const k X).div hWd hW.ne').add
      ((hasDerivAt_const k (2 * X)).div hQd hQ.ne')).add
      ((hasDerivAt_const k X).div hVd hV.ne')) using 1 <;>
      first | rfl | ring_nf
  · have hVXW : aoV X k ≤ aoW X k := by unfold aoV aoW; nlinarith [mul_nonneg hk.1 hX.1]
    have hn2 : -(4 * X ^ 2 / aoQ X k ^ 2) ≤ aoInverseK2 X k := by
      unfold aoInverseK2
      have : X ^ 2 / aoW X k ^ 2 ≤ X ^ 2 / aoV X k ^ 2 := by gcongr
      linarith
    have hp : aoV X k * aoT X k ≤ 3 * aoTheta ^ 2 / 4 := by
      have hv : aoV X k ≤ aoTheta / 2 := by unfold aoV; nlinarith [mul_nonneg hk.1 hX.1]
      have hkOne : 0 ≤ 1 - k := by linarith [hk.2]
      have ht : aoT X k ≤ 3 * aoTheta / 2 := by unfold aoT; nlinarith [mul_nonneg hkOne hX.1]
      calc
        aoV X k * aoT X k ≤ (aoTheta / 2) * (3 * aoTheta / 2) :=
          mul_le_mul hv ht hT.le (by norm_num [aoTheta])
        _ = 3 * aoTheta ^ 2 / 4 := by ring
    have hnk : 2 * X / aoW X k ≤ aoInverseK1 X k := by
      unfold aoInverseK1
      have hxwv : X / aoW X k ≤ X / aoV X k :=
        div_le_div_of_nonneg_left hX.1 hV hVXW
      have hxq : 0 ≤ X / aoQ X k := div_nonneg hX.1 hQ.le
      have hxq2 : 0 ≤ 2 * X / aoQ X k := div_nonneg (mul_nonneg (by norm_num) hX.1) hQ.le
      calc
        2 * X / aoW X k = X / aoW X k + X / aoW X k := by ring
        _ ≤ X / aoW X k + X / aoV X k := by simpa [add_comm] using add_le_add_left hxwv (X / aoW X k)
        _ ≤ (X / aoW X k + X / aoV X k) + 2 * X / aoQ X k := le_add_of_nonneg_right hxq2
        _ = X / aoW X k + 2 * X / aoQ X k + X / aoV X k := by ring
    have hq0 : aoStart ≤ aoQ X k := by unfold aoQ; norm_num [aoStart, aoTheta, aoSpan] at hX ⊢; nlinarith [mul_nonneg hk.1 hX.1]
    have hw0 : aoW X k ≤ (5 * aoTheta - 1) / 4 := by
      have hkX : k * X ≤ (1 / 4 : Real) * aoSpan := mul_le_mul hk.2 hX.2 hX.1 (by norm_num)
      unfold aoW; norm_num [aoSpan, aoTheta] at hkX ⊢; linarith
    have hscalar : 3 * aoTheta ^ 2 * aoW X k < 4 * aoQ X k ^ 3 := by
      have hs : 0 < 16 * aoStart ^ 3 - 3 * aoTheta ^ 2 * (5 * aoTheta - 1) := by
        norm_num [aoStart, aoTheta]
      have hqc : aoStart ^ 3 ≤ aoQ X k ^ 3 := pow_le_pow_left₀ (by norm_num [aoStart]) hq0 3
      nlinarith [mul_le_mul_of_nonneg_left hw0 (by positivity : 0 ≤ 3 * aoTheta ^ 2)]
    have hkey : 3 * aoTheta ^ 2 / aoQ X k ^ 2 < 4 * aoQ X k / aoW X k := by
      rw [div_lt_div_iff₀ (pow_pos hQ 2) hW]
      nlinarith
    have hleft : -(3 * aoTheta ^ 2 * X ^ 2 / aoQ X k ^ 2) ≤
        aoInverseK2 X k * (aoV X k * aoT X k) := by
      have hneg : -(4 * X ^ 2 / aoQ X k ^ 2) ≤ 0 := neg_nonpos.mpr (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg X)) (sq_nonneg _))
      calc
        -(3 * aoTheta ^ 2 * X ^ 2 / aoQ X k ^ 2) =
            -(4 * X ^ 2 / aoQ X k ^ 2) * (3 * aoTheta ^ 2 / 4) := by ring
        _ ≤ -(4 * X ^ 2 / aoQ X k ^ 2) * (aoV X k * aoT X k) :=
          mul_le_mul_of_nonpos_left hp hneg
        _ ≤ aoInverseK2 X k * (aoV X k * aoT X k) :=
          mul_le_mul_of_nonneg_right hn2 (mul_nonneg hV.le hT.le)
    have hright : 4 * X ^ 2 * aoQ X k / aoW X k ≤
        2 * X * aoQ X k * aoInverseK1 X k := by
      have hm : ((2 : Real) * X * aoQ X k) * (2 * X / aoW X k) ≤
          ((2 : Real) * X * aoQ X k) * aoInverseK1 X k :=
        mul_le_mul_of_nonneg_left hnk (mul_nonneg (mul_nonneg (by norm_num) hX.1) hQ.le)
      calc
        4 * X ^ 2 * aoQ X k / aoW X k = (2 * X * aoQ X k) * (2 * X / aoW X k) := by ring
        _ ≤ (2 * X * aoQ X k) * aoInverseK1 X k := hm
    have hmid : 3 * aoTheta ^ 2 * X ^ 2 / aoQ X k ^ 2 ≤ 4 * X ^ 2 * aoQ X k / aoW X k := by
      calc
        3 * aoTheta ^ 2 * X ^ 2 / aoQ X k ^ 2 = X ^ 2 * (3 * aoTheta ^ 2 / aoQ X k ^ 2) := by ring
        _ ≤ X ^ 2 * (4 * aoQ X k / aoW X k) := mul_le_mul_of_nonneg_left hkey.le (sq_nonneg X)
        _ = 4 * X ^ 2 * aoQ X k / aoW X k := by ring
    linarith
private theorem ao_affine_pullback {f : Real → Real} {a b c d m q s : Real} (hs : 0 ≤ s) (hf : ConvexOn Real (Icc c d) f) (hm : MapsTo (fun x => q + m * x) (Icc a b) (Icc c d)) : ConvexOn Real (Icc a b) (fun x => s * f (q + m * x)) := by
  let g : Real →ᵃ[Real] Real :=
    (DistribSMul.toLinearMap Real Real m).toAffineMap + AffineMap.const Real Real q
  have hg := (hf.comp_affineMap g).subset
    (fun x hx => by simpa [g, smul_eq_mul, mul_comm, add_comm] using hm hx) (convex_Icc a b)
  simpa [g, Function.comp_def, smul_eq_mul, mul_comm, add_comm] using hg.smul hs
private theorem ao_transformed_eq (branch : Fin 2) {x y : Real} (hx : x ∈ Icc 0 1)
    (hy : y ∈ Icc 0 1) :
    sectionSixFirstLowCentralLargeBelowTransformedIntegrand Real.log branch x y =
      if branch = 0 then
        1 / aoSpan * (aoSpan * x * aoMixedN (aoSpan * x) ((2 - y) / 4) /
          (aoU (aoSpan * x) * aoV (aoSpan * x) ((2 - y) / 4) * aoT (aoSpan * x) ((2 - y) / 4)))
      else 1 / aoSpan * (aoSpan * x * aoInverseN (aoSpan * x) ((1 - y) / 4) /
          (aoU (aoSpan * x) * aoV (aoSpan * x) ((1 - y) / 4) * aoT (aoSpan * x) ((1 - y) / 4))) := by
  fin_cases branch
  · have hX : aoSpan * x ∈ Icc 0 aoSpan := by norm_num [aoSpan] at hx ⊢; constructor <;> nlinarith
    have hk : (2 - y) / 4 ∈ Icc (1 / 4 : Real) (1 / 2) := by constructor <;> linarith [hy.1, hy.2]
    rcases ao_chart_pos hX ⟨by linarith [hk.1], hk.2⟩ with ⟨hU, hV, hT, hW, hQ, hA, hL⟩
    have hu : (69999 / 250000 : Real) + 40003 / 500000 * x = aoU (aoSpan * x) := by norm_num [aoU, aoStart, aoSpan]
    have hv : (180001 / 500000 : Real) / 2 - 40003 / 500000 * x * (2 - y) / 4 = aoV (aoSpan * x) ((2 - y) / 4) := by norm_num [aoV, aoTheta, aoSpan]; ring
    have ha : (319999 / 500000 : Real) - aoU (aoSpan * x) = aoTheta - aoSpan * x := by unfold aoU; norm_num [aoStart, aoTheta]; ring
    have ht : 1 - aoU (aoSpan * x) - aoV (aoSpan * x) ((2 - y) / 4) = aoT (aoSpan * x) ((2 - y) / 4) := by unfold aoU aoV aoT; norm_num [aoStart, aoTheta]; ring
    have hl : 2 * ((180001 / 500000 : Real) - aoV (aoSpan * x) ((2 - y) / 4)) = aoTheta + 2 * ((2 - y) / 4) * (aoSpan * x) := by unfold aoV; norm_num [aoTheta]; ring
    have hm : (564663 / 1000000 : Real) / (aoU (aoSpan * x) * aoV (aoSpan * x) ((2 - y) / 4)) * ((aoV (aoSpan * x) ((2 - y) / 4))⁻¹ - 3 / aoT (aoSpan * x) ((2 - y) / 4)) =
        (aoC * (4 * ((2 - y) / 4) - 1) * (aoSpan * x) / aoV (aoSpan * x) ((2 - y) / 4)) / (aoU (aoSpan * x) * aoV (aoSpan * x) ((2 - y) / 4) * aoT (aoSpan * x) ((2 - y) / 4)) := by
      field_simp [hU.ne', hV.ne', hT.ne']; unfold aoC aoV aoT; ring
    simp [sectionSixFirstLowCentralLargeBelowTransformedIntegrand]; rw [hu, hv, ht, hl, ha, Real.log_div hL.ne' hA.ne']
    unfold aoMixedN; rw [hm]; ring_nf
    have hspan : aoSpan ≠ 0 := by norm_num [aoSpan]
    field_simp [hspan]
  · have hX : aoSpan * x ∈ Icc 0 aoSpan := by norm_num [aoSpan] at hx ⊢; constructor <;> nlinarith
    have hk : (1 - y) / 4 ∈ Icc (0 : Real) (1 / 4) := by constructor <;> linarith [hy.1, hy.2]
    rcases ao_chart_pos hX ⟨hk.1, hk.2.trans (by norm_num)⟩ with ⟨hU, hV, hT, hW, hQ, hA, hL⟩
    have hu : (69999 / 250000 : Real) + 40003 / 500000 * x = aoU (aoSpan * x) := by norm_num [aoU, aoStart, aoSpan]
    have hv : (180001 / 500000 : Real) / 2 - 40003 / 500000 * x * (1 - y) / 4 =
        aoV (aoSpan * x) ((1 - y) / 4) := by norm_num [aoV, aoTheta, aoSpan]; ring
    have hw : (180001 / 500000 : Real) - aoV (aoSpan * x) ((1 - y) / 4) =
        aoW (aoSpan * x) ((1 - y) / 4) := by unfold aoV aoW; norm_num [aoTheta]; ring
    have hq : 1 - aoU (aoSpan * x) - 2 * aoV (aoSpan * x) ((1 - y) / 4) =
        aoQ (aoSpan * x) ((1 - y) / 4) := by unfold aoU aoV aoQ; norm_num [aoStart, aoTheta]; ring
    have ha : (319999 / 500000 : Real) - aoU (aoSpan * x) = aoTheta - aoSpan * x := by unfold aoU; norm_num [aoStart, aoTheta]; ring
    have ht : 1 - aoU (aoSpan * x) - aoV (aoSpan * x) ((1 - y) / 4) =
        aoT (aoSpan * x) ((1 - y) / 4) := by unfold aoU aoV aoT; norm_num [aoStart, aoTheta]; ring
    simp [sectionSixFirstLowCentralLargeBelowTransformedIntegrand]
    rw [hu, hv, hw, hq, ha, ht, Real.log_div (mul_pos hW hQ).ne' (mul_pos hV hA).ne',
      Real.log_mul hW.ne' hQ.ne', Real.log_mul hV.ne' hA.ne']
    unfold aoInverseN
    field_simp [aoSpan, hU.ne', hV.ne', hT.ne', hA.ne']; ring
theorem
    sectionSixFirstLowCentralLargeBelowTransformedIntegrand_actual_properties
    (branch : Fin 2) :
    ContinuousOn
      (fun z : Real × Real =>
        sectionSixFirstLowCentralLargeBelowTransformedIntegrand
          Real.log branch z.1 z.2)
      (Icc (0 : Real) 1 ×ˢ Icc (0 : Real) 1) ∧
    (∀ y ∈ Icc (0 : Real) 1,
      ConvexOn Real (Icc 0 1)
        (fun x =>
          sectionSixFirstLowCentralLargeBelowTransformedIntegrand
            Real.log branch x y)) ∧
    (∀ x ∈ Icc (0 : Real) 1,
      ConvexOn Real (Icc 0 1)
        (fun y =>
          sectionSixFirstLowCentralLargeBelowTransformedIntegrand
            Real.log branch x y)) := by
  fin_cases branch
  · constructor
    · apply ContinuousOn.congr (f := fun z : Real × Real =>
          1 / aoSpan * (aoSpan * z.1 * aoMixedN (aoSpan * z.1) ((2 - z.2) / 4) /
            (aoU (aoSpan * z.1) * aoV (aoSpan * z.1) ((2 - z.2) / 4) *
              aoT (aoSpan * z.1) ((2 - z.2) / 4))))
      · apply continuousOn_of_forall_continuousAt
        rintro ⟨x, y⟩ ⟨hx, hy⟩
        have hX : aoSpan * x ∈ Icc 0 aoSpan := by norm_num [aoSpan] at hx ⊢; constructor <;> nlinarith
        have hk : (2 - y) / 4 ∈ Icc (1 / 4 : Real) (1 / 2) := by constructor <;> linarith [hy.1, hy.2]
        rcases ao_chart_pos hX ⟨by linarith [hk.1], hk.2⟩ with ⟨hU, hV, hT, hW, hQ, hA, hL⟩
        unfold aoMixedN aoU aoV aoT
        fun_prop (disch := positivity)
      · rintro ⟨x, y⟩ ⟨hx, hy⟩
        exact ao_transformed_eq 0 hx hy
    constructor
    · intro y hy
      let k := (2 - y) / 4
      have hk : k ∈ Icc (1 / 4 : Real) (1 / 2) := by dsimp [k]; constructor <;> linarith [hy.1, hy.2]
      have hphys : ConvexOn Real (Icc 0 aoSpan)
          (fun X => X * aoMixedN X k / (aoU X * aoV X k * aoT X k)) := by
        apply convexOn_x_mul_numerator_div_threeAffine (d := aoStart) (theta := aoTheta)
          (N1 := fun X => aoMixedN1 X k) (N2 := fun X => aoMixedN2 X k) (N3 := fun X => aoMixedN3 X k)
        · norm_num [aoSpan]
        · exact ⟨by linarith [hk.1], hk.2.trans (by norm_num)⟩
        · intro X hX
          rcases ao_chart_pos hX ⟨by linarith [hk.1], hk.2⟩ with ⟨hU, hV, hT, -⟩; exact ⟨hU, hV, hT⟩
        · simp [aoMixedN]
        · intro X hX; exact (ao_mixed_derivatives hX hk).1
        · intro X hX; exact (ao_mixed_derivatives hX hk).2.1
        · intro X hX; exact (ao_mixed_derivatives hX hk).2.2
        · intro X hX; exact (ao_mixed_signs hX hk).1
        · intro X hX; exact (ao_mixed_signs hX hk).2.1
        · intro X hX; exact (ao_mixed_signs hX hk).2.2
      have hpull := ao_affine_pullback (a := (0 : Real)) (b := 1) (c := 0) (d := aoSpan)
        (m := aoSpan) (q := 0) (s := 1 / aoSpan) (by norm_num [aoSpan]) hphys
        (fun x hx => by norm_num [aoSpan] at hx ⊢; constructor <;> nlinarith)
      apply hpull.congr
      intro x hx
      simpa [k] using (ao_transformed_eq 0 hx hy).symm
    · intro x hx
      let X := aoSpan * x
      have hX : X ∈ Icc 0 aoSpan := by dsimp [X]; norm_num [aoSpan] at hx ⊢; constructor <;> nlinarith
      have hslope : ConvexOn Real (Icc (1 / 4 : Real) (1 / 2))
          (fun k => aoMixedN X k / (aoV X k * aoT X k)) := by
        apply convexOn_numerator_div_twoAffine (theta := aoTheta) (X := X)
          (Nk := aoMixedK1 X) (Nkk := aoMixedK2 X)
        · intro k hk
          rcases ao_chart_pos hX ⟨by linarith [hk.1], hk.2⟩ with ⟨hU, hV, hT, -⟩; exact ⟨hV, hT⟩
        · intro k hk; exact (ao_mixed_k_data hX hk).1
        · intro k hk; exact (ao_mixed_k_data hX hk).2.1
        · intro k hk; exact (ao_mixed_signs hX hk).1
        · intro k hk
          rcases ao_mixed_k_data hX hk with ⟨hd0, hd1, hNk, hNkk⟩
          rcases ao_chart_pos hX ⟨by linarith [hk.1], hk.2⟩ with ⟨hU, hV, hT, hW, hQ, hA, hL⟩
          exact add_nonneg (mul_nonneg hNkk (mul_nonneg hV.le hT.le))
            (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hX.1) hQ.le) hNk)
      have hU := (ao_chart_pos (k := 0) hX ⟨by norm_num, by norm_num⟩).1
      have hpull := ao_affine_pullback (a := (0 : Real)) (b := 1) (c := (1 / 4 : Real))
        (d := 1 / 2) (m := -(1 / 4 : Real)) (q := 1 / 2)
        (s := (1 / aoSpan) * (X / aoU X))
        (mul_nonneg (by norm_num [aoSpan]) (div_nonneg hX.1 hU.le)) hslope
        (fun y hy => by dsimp; constructor <;> ring_nf <;> linarith [hy.1, hy.2])
      apply hpull.congr
      intro y hy
      have heq := (ao_transformed_eq 0 hx hy).symm
      dsimp [X] at heq ⊢
      convert heq using 1
      rcases ao_chart_pos (k := 0) hX ⟨by norm_num, by norm_num⟩ with ⟨hU, hV, hT, hW, hQ, hA, hL⟩
      field_simp [hU.ne', hV.ne', hT.ne']; ring
  · constructor
    · apply ContinuousOn.congr (f := fun z : Real × Real =>
          1 / aoSpan * (aoSpan * z.1 * aoInverseN (aoSpan * z.1) ((1 - z.2) / 4) /
            (aoU (aoSpan * z.1) * aoV (aoSpan * z.1) ((1 - z.2) / 4) *
              aoT (aoSpan * z.1) ((1 - z.2) / 4))))
      · apply continuousOn_of_forall_continuousAt
        rintro ⟨x, y⟩ ⟨hx, hy⟩
        have hX : aoSpan * x ∈ Icc 0 aoSpan := by norm_num [aoSpan] at hx ⊢; constructor <;> nlinarith
        have hk : (1 - y) / 4 ∈ Icc (0 : Real) (1 / 4) := by constructor <;> linarith [hy.1, hy.2]
        rcases ao_chart_pos hX ⟨hk.1, hk.2.trans (by norm_num)⟩ with ⟨hU, hV, hT, hW, hQ, hA, hL⟩
        unfold aoInverseN aoU aoV aoT aoW aoQ
        fun_prop (disch := positivity)
      · rintro ⟨x, y⟩ ⟨hx, hy⟩
        exact ao_transformed_eq 1 hx hy
    constructor
    · intro y hy
      let k := (1 - y) / 4
      have hk : k ∈ Icc (0 : Real) (1 / 4) := by dsimp [k]; constructor <;> linarith [hy.1, hy.2]
      have hphys : ConvexOn Real (Icc 0 aoSpan)
          (fun X => X * aoInverseN X k / (aoU X * aoV X k * aoT X k)) := by
        apply convexOn_x_mul_numerator_div_threeAffine (d := aoStart) (theta := aoTheta)
          (N1 := fun X => aoInverseN1 X k) (N2 := fun X => aoInverseN2 X k) (N3 := fun X => aoInverseN3 X k)
        · norm_num [aoSpan]
        · exact ⟨hk.1, hk.2.trans (by norm_num)⟩
        · intro X hX
          rcases ao_chart_pos hX ⟨hk.1, hk.2.trans (by norm_num)⟩ with ⟨hU, hV, hT, -⟩; exact ⟨hU, hV, hT⟩
        · simp [aoInverseN, aoW, aoQ, aoV]
        · intro X hX; exact (ao_inverse_derivatives hX hk).1
        · intro X hX; exact (ao_inverse_derivatives hX hk).2.1
        · intro X hX; exact (ao_inverse_derivatives hX hk).2.2
        · intro X hX; exact (ao_inverse_signs hX hk).1
        · intro X hX; exact (ao_inverse_signs hX hk).2.1
        · intro X hX; exact (ao_inverse_signs hX hk).2.2
      have hpull := ao_affine_pullback (a := (0 : Real)) (b := 1) (c := 0) (d := aoSpan)
        (m := aoSpan) (q := 0) (s := 1 / aoSpan) (by norm_num [aoSpan]) hphys
        (fun x hx => by norm_num [aoSpan] at hx ⊢; constructor <;> nlinarith)
      apply hpull.congr
      intro x hx
      simpa [k] using (ao_transformed_eq 1 hx hy).symm
    · intro x hx
      let X := aoSpan * x
      have hX : X ∈ Icc 0 aoSpan := by dsimp [X]; norm_num [aoSpan] at hx ⊢; constructor <;> nlinarith
      have hslope : ConvexOn Real (Icc (0 : Real) (1 / 4))
          (fun k => aoInverseN X k / (aoV X k * aoT X k)) := by
        apply convexOn_numerator_div_twoAffine (theta := aoTheta) (X := X)
          (Nk := aoInverseK1 X) (Nkk := aoInverseK2 X)
        · intro k hk
          rcases ao_chart_pos hX ⟨hk.1, hk.2.trans (by norm_num)⟩ with ⟨hU, hV, hT, -⟩; exact ⟨hV, hT⟩
        · intro k hk; exact (ao_inverse_k_data hX hk).1
        · intro k hk; exact (ao_inverse_k_data hX hk).2.1
        · intro k hk; exact (ao_inverse_signs hX hk).1
        · intro k hk; exact (ao_inverse_k_data hX hk).2.2
      have hU := (ao_chart_pos (k := 0) hX ⟨by norm_num, by norm_num⟩).1
      have hpull := ao_affine_pullback (a := (0 : Real)) (b := 1) (c := (0 : Real))
        (d := 1 / 4) (m := -(1 / 4 : Real)) (q := 1 / 4)
        (s := (1 / aoSpan) * (X / aoU X))
        (mul_nonneg (by norm_num [aoSpan]) (div_nonneg hX.1 hU.le)) hslope
        (fun y hy => by dsimp; constructor <;> ring_nf <;> linarith [hy.1, hy.2])
      apply hpull.congr
      intro y hy
      have heq := (ao_transformed_eq 1 hx hy).symm
      dsimp [X] at heq ⊢
      convert heq using 1
      rcases ao_chart_pos (k := 0) hX ⟨by norm_num, by norm_num⟩ with ⟨hU, hV, hT, hW, hQ, hA, hL⟩
      field_simp [hU.ne', hV.ne', hT.ne']; ring
end
end PrimesRestrictedDigits
