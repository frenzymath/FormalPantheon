import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabClampedFourBranchFiberD899A

/-!
# clamped rational Buchstab fiber bound

This module replaces the inverse-branch logarithm by two exact rational secant majorants. It
supplies no P2 carrier, finite cover, or numerical cap.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixBuchstabSecantPayload
    (u v w B l h a b : Real) : Real :=
  1 / (u * v * w) *
    ((1 / a + 1 / b + 1 / (a * b)) * (1 / l - 1 / h) -
      B / (2 * a * b) * (1 / l ^ 2 - 1 / h ^ 2))

private theorem sectionSixBuchstabReciprocal_le_secant
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

private theorem sectionSixBuchstabSecant_primitive
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

private theorem sectionSixBuchstabInverseSecantBranch_le
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
      have hsecant := sectionSixBuchstabReciprocal_le_secant ha hab
        (show (B - t) / t ∈ Icc a b from ⟨hyLower, hyUpper⟩)
      have hden : 0 < u * v * w * t ^ 2 := by positivity
      rw [homega]
      exact (div_le_div_iff_of_pos_right hden).2 hsecant
    _ = _ := sectionSixBuchstabSecant_primitive hu hv hw hl hlh ha hb

private theorem sectionSixBuchstabSecantPayload_self
    (u v w B x a b : Real) :
    sectionSixBuchstabSecantPayload u v w B x x a b = 0 := by
  simp [sectionSixBuchstabSecantPayload]

theorem sectionSixBuchstabInverseTwoSecants_le
    {u v w B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h)
    (hB : 2 * h <= B) (hthree : B <= 3 * l) :
    let m15 := sectionSixBuchstabClamp l h (2 * B / 5)
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) /
        (u * v * w * t ^ 2)) <=
      sectionSixBuchstabSecantPayload u v w B l m15 (3 / 2) 2 +
      sectionSixBuchstabSecantPayload u v w B m15 h 1 (3 / 2) := by
  dsimp only
  let m15 := sectionSixBuchstabClamp l h (2 * B / 5)
  change
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) /
        (u * v * w * t ^ 2)) <=
      sectionSixBuchstabSecantPayload u v w B l m15 (3 / 2) 2 +
      sectionSixBuchstabSecantPayload u v w B m15 h 1 (3 / 2)
  have hh : 0 < h := hl.trans_le hlh
  have hBpos : 0 < B := by linarith
  by_cases hleft : 2 * B / 5 <= l
  · have hm15 : m15 = l := by
      dsimp [m15, sectionSixBuchstabClamp]
      rw [min_eq_right (hleft.trans hlh), max_eq_left hleft]
    rw [hm15, sectionSixBuchstabSecantPayload_self, zero_add]
    exact sectionSixBuchstabInverseSecantBranch_le
      hu hv hw hl hlh (by norm_num) (by norm_num) (by norm_num)
      (by norm_num at *; assumption) (by linarith [hleft])
  · by_cases hright : h <= 2 * B / 5
    · have hm15 : m15 = h := by
        dsimp [m15, sectionSixBuchstabClamp]
        rw [min_eq_left hright, max_eq_right hlh]
      rw [hm15, sectionSixBuchstabSecantPayload_self, add_zero]
      exact sectionSixBuchstabInverseSecantBranch_le
        hu hv hw hl hlh (by norm_num) (by norm_num) (by norm_num)
        (by linarith [hright]) (by norm_num at *; assumption)
    · have hlx : l <= 2 * B / 5 := le_of_not_ge hleft
      have hxh : 2 * B / 5 <= h := le_of_not_ge hright
      have hm15 : m15 = 2 * B / 5 := by
        dsimp [m15, sectionSixBuchstabClamp]
        rw [min_eq_right hxh, max_eq_right hlx]
      have hx : 0 < 2 * B / 5 := by positivity
      have hxB : 2 * (2 * B / 5) <= B := by nlinarith
      have hintLeft := sectionSixBuchstabFiber_intervalIntegrable
        hu hv hw hl hlx hxB
      have hintRight := sectionSixBuchstabFiber_intervalIntegrable
        hu hv hw hx hxh hB
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        hintLeft hintRight
      have hsecantLeft :
          (∫ t in l..(2 * B / 5),
            buchstabFunction ((B - t) / t) /
              (u * v * w * t ^ 2)) <=
            sectionSixBuchstabSecantPayload
              u v w B l (2 * B / 5) (3 / 2) 2 := by
        exact sectionSixBuchstabInverseSecantBranch_le
          hu hv hw hl hlx (by norm_num) (by norm_num) (by norm_num)
          (by linarith) (by norm_num at *; assumption)
      have hsecantRight :
          (∫ t in (2 * B / 5)..h,
            buchstabFunction ((B - t) / t) /
              (u * v * w * t ^ 2)) <=
            sectionSixBuchstabSecantPayload
              u v w B (2 * B / 5) h 1 (3 / 2) := by
        exact sectionSixBuchstabInverseSecantBranch_le
          hu hv hw hx hxh (by norm_num) (by norm_num) (by norm_num)
          (by norm_num at *; assumption) (by linarith)
      rw [hm15]
      calc
        (∫ t in l..h,
            buchstabFunction ((B - t) / t) /
              (u * v * w * t ^ 2)) =
            (∫ t in l..(2 * B / 5),
              buchstabFunction ((B - t) / t) /
                (u * v * w * t ^ 2)) +
            ∫ t in (2 * B / 5)..h,
              buchstabFunction ((B - t) / t) /
                (u * v * w * t ^ 2) := by
          rw [hsplit]
        _ <= _ := add_le_add hsecantLeft hsecantRight

theorem sectionSixBuchstabClampedRationalFiber_le
    {u v w B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h) (hB : 2 * h <= B) :
    let m4 := sectionSixBuchstabClamp l h (B / 4)
    let m3 := sectionSixBuchstabClamp m4 h (B / 3)
    let my0 := sectionSixBuchstabClamp m4 m3
      (sectionSixBuchstabShortMiddleBreakpoint B)
    let m15 := sectionSixBuchstabClamp m3 h (2 * B / 5)
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) <=
      (564383 / 1000000 : Real) / (u * v * w) * (1 / l - 1 / m4) +
      (70893 / 125000 : Real) / (u * v * w) * (1 / m4 - 1 / my0) +
      (564663 / 1000000 : Real) / (u * v * w) * (1 / my0 - 1 / m3) +
      sectionSixBuchstabSecantPayload u v w B m3 m15 (3 / 2) 2 +
      sectionSixBuchstabSecantPayload u v w B m15 h 1 (3 / 2) := by
  dsimp only
  let m4 := sectionSixBuchstabClamp l h (B / 4)
  let m3 := sectionSixBuchstabClamp m4 h (B / 3)
  let my0 := sectionSixBuchstabClamp m4 m3
    (sectionSixBuchstabShortMiddleBreakpoint B)
  let m15 := sectionSixBuchstabClamp m3 h (2 * B / 5)
  have hm4lo : l <= m4 := by
    dsimp [m4, sectionSixBuchstabClamp]
    exact le_max_left _ _
  have hm4hi : m4 <= h := by
    dsimp [m4, sectionSixBuchstabClamp]
    exact max_le hlh (min_le_left _ _)
  have hm3lo : m4 <= m3 := by
    dsimp [m3, sectionSixBuchstabClamp]
    exact le_max_left _ _
  have hm3hi : m3 <= h := by
    dsimp [m3, sectionSixBuchstabClamp]
    exact max_le hm4hi (min_le_left _ _)
  have hm3pos : 0 < m3 := hl.trans_le (hm4lo.trans hm3lo)
  have hh : 0 < h := hl.trans_le hlh
  have hbase := sectionSixBuchstabClampedFourBranchFiber_le
    hu hv hw hl hlh hB
  change
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) <=
      (564383 / 1000000 : Real) / (u * v * w) * (1 / l - 1 / m4) +
      (70893 / 125000 : Real) / (u * v * w) * (1 / m4 - 1 / my0) +
      (564663 / 1000000 : Real) / (u * v * w) * (1 / my0 - 1 / m3) +
      sectionSixBuchstabSecantPayload u v w B m3 m15 (3 / 2) 2 +
      sectionSixBuchstabSecantPayload u v w B m15 h 1 (3 / 2)
  change
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) <=
      (564383 / 1000000 : Real) / (u * v * w) * (1 / l - 1 / m4) +
      (70893 / 125000 : Real) / (u * v * w) * (1 / m4 - 1 / my0) +
      (564663 / 1000000 : Real) / (u * v * w) * (1 / my0 - 1 / m3) +
      1 / (u * v * w * B) *
        Real.log (h * (B - m3) / (m3 * (B - h))) at hbase
  by_cases hcut : h <= B / 3
  · have hm3eq : m3 = h := by
      dsimp [m3, sectionSixBuchstabClamp]
      rw [min_eq_left hcut, max_eq_right hm4hi]
    have hm15eq : m15 = h := by
      dsimp [m15, sectionSixBuchstabClamp]
      rw [hm3eq]
      exact max_eq_left (min_le_left _ _)
    have hBh : Ne (B - h) 0 := by linarith
    rw [hm3eq] at hbase
    rw [hm3eq, hm15eq]
    simpa [sectionSixBuchstabSecantPayload, hh.ne', hBh] using hbase
  · have hthree : B <= 3 * m3 := by
      have hcut' : B / 3 <= m3 := by
        dsimp [m3, sectionSixBuchstabClamp]
        rw [min_eq_right (le_of_not_ge hcut)]
        exact le_max_right _ _
      linarith
    have hinverse := sectionSixBuchstabInverseTwoSecants_le
      hu hv hw hm3pos hm3hi hB hthree
    change
      (∫ t in m3..h,
        buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) <=
        sectionSixBuchstabSecantPayload u v w B m3 m15 (3 / 2) 2 +
        sectionSixBuchstabSecantPayload u v w B m15 h 1 (3 / 2) at hinverse
    have heq := integral_sectionSixBuchstabInverseBranch_eq
      hu hv hw hm3pos hm3hi hB hthree
    have hlog :
        1 / (u * v * w * B) *
          Real.log (h * (B - m3) / (m3 * (B - h))) <=
          sectionSixBuchstabSecantPayload u v w B m3 m15 (3 / 2) 2 +
          sectionSixBuchstabSecantPayload u v w B m15 h 1 (3 / 2) := by
      rw [<- heq]
      exact hinverse
    linarith

end

end PrimesRestrictedDigits
