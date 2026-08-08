import Waring.Analytic.ChenTenMajorArcKernelBounds

/-!
# Integrating the decay-weighted major-arc error

This file splits each centered major arc at `P^(-5)`, uses the central and
outer pointwise estimates, and proves the per-arc error
`10^30 * q^(-9/5) * P^9`.
-/

namespace Waring.Analytic

open MeasureTheory Set
open scoped Interval

noncomputable section

private theorem integral_rpow_neg_fourteen_fifths_le
    {h r : Real} (hh : 0 < h) (hhr : h <= r) :
    (∫ z in h..r, z ^ (-14 / 5 : Real)) <=
      (5 / 9 : Real) * h ^ (-9 / 5 : Real) := by
  have hzero : (0 : Real) ∉ Set.uIcc h r := by
    rw [Set.uIcc_of_le hhr]
    intro hz
    linarith [hz.1]
  rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
  have hrpow : 0 <= r ^ (-9 / 5 : Real) :=
    Real.rpow_nonneg (hh.le.trans hhr) _
  ring_nf
  nlinarith

private theorem central_scale_rpow_identities {P : Nat} (hP : 1 <= P) :
    let h : Real := (P : Real) ^ (-5 : Real)
    h * (P : Real) ^ 14 = (P : Real) ^ 9 ∧
      h ^ (-9 / 5 : Real) = (P : Real) ^ 9 := by
  dsimp
  have hPR : (0 : Real) < P := by positivity
  constructor
  · rw [← Real.rpow_natCast, ← Real.rpow_natCast]
    rw [← Real.rpow_add hPR]
    norm_num
  · rw [← Real.rpow_mul hPR.le]
    norm_num

private def chenTenTranslatedMajorArcError
    (P N : Nat) (i : ChenTenArcIndex P) (z : Real) : Complex :=
  chenTenRepresentationIntegrand P N (chenTenMajorArcCenter i + z) -
    chenTenMajorArcModelIntegrand P N i z

private theorem continuous_chenTenTranslatedMajorArcError
    (P N : Nat) (i : ChenTenArcIndex P) :
    Continuous (chenTenTranslatedMajorArcError P N i) := by
  unfold chenTenTranslatedMajorArcError
  exact ((continuous_chenTenRepresentationIntegrand P N).comp
    (continuous_const.add continuous_id)).sub
      (continuous_chenTenMajorArcModelIntegrand P N i)

private theorem norm_intervalIntegral_majorArcError_outer_pos_le
    {P : Nat} (hP : 1 <= P) (N : Nat) (i : ChenTenArcIndex P)
    {h r : Real} (hh : 0 < h) (hhr : h <= r)
    (hradius : r <= chenTenMajorArcRadius P i) :
    ‖∫ z in h..r, chenTenTranslatedMajorArcError P N i z‖ <=
      ((90 * 46 ^ 14 : Real) *
          (i.denominator : Real) ^ (-9 / 5 : Real)) *
        2 ^ 14 * ((5 / 9 : Real) * h ^ (-9 / 5 : Real)) := by
  let A : Real := (90 * 46 ^ 14 : Real) *
    (i.denominator : Real) ^ (-9 / 5 : Real)
  have hcont := continuous_chenTenTranslatedMajorArcError P N i
  calc
    ‖∫ z in h..r, chenTenTranslatedMajorArcError P N i z‖ <=
        ∫ z in h..r, ‖chenTenTranslatedMajorArcError P N i z‖ :=
      intervalIntegral.norm_integral_le_integral_norm hhr
    _ <= ∫ z in h..r, A * 2 ^ 14 * z ^ (-14 / 5 : Real) := by
      apply intervalIntegral.integral_mono_on hhr
      · exact hcont.norm.intervalIntegrable h r
      · apply IntervalIntegrable.const_mul
        apply intervalIntegral.intervalIntegrable_rpow
        right
        rw [Set.uIcc_of_le hhr]
        intro hz
        linarith [hz.1]
      · intro z hz
        have hzpos : 0 < z := hh.trans_le hz.1
        have hzinArc : z ∈ Set.Icc
            (-chenTenMajorArcRadius P i) (chenTenMajorArcRadius P i) := by
          constructor
          · linarith [chenTenMajorArcRadius_pos (Nat.zero_lt_of_lt hP) i]
          · exact hz.2.trans hradius
        have hout :=
          norm_chenTenRepresentationIntegrand_sub_modelIntegrand_le_outer
            hP N i z hzpos.ne' hzinArc
        change ‖chenTenTranslatedMajorArcError P N i z‖ <= _ at hout ⊢
        rw [abs_of_pos hzpos] at hout
        have hzpow :
            (z ^ (-1 / 5 : Real)) ^ (14 : Nat) =
              z ^ (-14 / 5 : Real) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
          norm_num
        dsimp [A]
        rw [mul_pow, hzpow] at hout
        nlinarith
    _ = A * 2 ^ 14 * (∫ z in h..r, z ^ (-14 / 5 : Real)) := by
      rw [intervalIntegral.integral_const_mul]
    _ <= A * 2 ^ 14 * ((5 / 9 : Real) * h ^ (-9 / 5 : Real)) := by
      gcongr
      exact integral_rpow_neg_fourteen_fifths_le hh hhr
    _ = _ := by rfl

private theorem norm_intervalIntegral_majorArcError_outer_neg_le
    {P : Nat} (hP : 1 <= P) (N : Nat) (i : ChenTenArcIndex P)
    {h r : Real} (hh : 0 < h) (hhr : h <= r)
    (hradius : r <= chenTenMajorArcRadius P i) :
    ‖∫ z in -r..-h, chenTenTranslatedMajorArcError P N i z‖ <=
      ((90 * 46 ^ 14 : Real) *
          (i.denominator : Real) ^ (-9 / 5 : Real)) *
        2 ^ 14 * ((5 / 9 : Real) * h ^ (-9 / 5 : Real)) := by
  let A : Real := (90 * 46 ^ 14 : Real) *
    (i.denominator : Real) ^ (-9 / 5 : Real)
  have hcont := continuous_chenTenTranslatedMajorArcError P N i
  rw [← intervalIntegral.integral_comp_neg]
  calc
    ‖∫ z in h..r, chenTenTranslatedMajorArcError P N i (-z)‖ <=
        ∫ z in h..r, ‖chenTenTranslatedMajorArcError P N i (-z)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hhr
    _ <= ∫ z in h..r, A * 2 ^ 14 * z ^ (-14 / 5 : Real) := by
      apply intervalIntegral.integral_mono_on hhr
      · exact (hcont.comp continuous_neg).norm.intervalIntegrable h r
      · apply IntervalIntegrable.const_mul
        apply intervalIntegral.intervalIntegrable_rpow
        right
        rw [Set.uIcc_of_le hhr]
        intro hz
        linarith [hz.1]
      · intro z hz
        have hzpos : 0 < z := hh.trans_le hz.1
        have hnegInArc : -z ∈ Set.Icc
            (-chenTenMajorArcRadius P i) (chenTenMajorArcRadius P i) := by
          constructor
          · linarith [hz.2.trans hradius]
          · linarith [chenTenMajorArcRadius_pos (Nat.zero_lt_of_lt hP) i]
        have hout :=
          norm_chenTenRepresentationIntegrand_sub_modelIntegrand_le_outer
            hP N i (-z) (neg_ne_zero.mpr hzpos.ne') hnegInArc
        change ‖chenTenTranslatedMajorArcError P N i (-z)‖ <= _ at hout ⊢
        rw [abs_neg, abs_of_pos hzpos] at hout
        have hzpow :
            (z ^ (-1 / 5 : Real)) ^ (14 : Nat) =
              z ^ (-14 / 5 : Real) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
          norm_num
        dsimp [A]
        rw [mul_pow, hzpow] at hout
        nlinarith
    _ = A * 2 ^ 14 * (∫ z in h..r, z ^ (-14 / 5 : Real)) := by
      rw [intervalIntegral.integral_const_mul]
    _ <= A * 2 ^ 14 * ((5 / 9 : Real) * h ^ (-9 / 5 : Real)) := by
      gcongr
      exact integral_rpow_neg_fourteen_fifths_le hh hhr
    _ = _ := by rfl

private theorem norm_intervalIntegral_majorArcError_central_le
    {P : Nat} (hP : 1 <= P) (N : Nat) (i : ChenTenArcIndex P)
    {h : Real} (hh : 0 <= h)
    (hradius : h <= chenTenMajorArcRadius P i) :
    ‖∫ z in -h..h, chenTenTranslatedMajorArcError P N i z‖ <=
      2 * ((90 * 46 ^ 14 : Real) *
          (i.denominator : Real) ^ (-9 / 5 : Real)) *
        h * (P : Real) ^ 14 := by
  let A : Real := (90 * 46 ^ 14 : Real) *
    (i.denominator : Real) ^ (-9 / 5 : Real)
  calc
    ‖∫ z in -h..h, chenTenTranslatedMajorArcError P N i z‖ <=
        (A * (P : Real) ^ 14) * |h - (-h)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro z hz
      have hz' := Set.uIoc_subset_uIcc hz
      rw [Set.uIcc_of_le (by linarith : -h <= h)] at hz'
      have hzinArc : z ∈ Set.Icc
          (-chenTenMajorArcRadius P i) (chenTenMajorArcRadius P i) := by
        constructor <;> linarith [hz'.1, hz'.2]
      have hcentral :=
        norm_chenTenRepresentationIntegrand_sub_modelIntegrand_le_central
          hP N i z hzinArc
      change ‖chenTenTranslatedMajorArcError P N i z‖ <= _ at hcentral ⊢
      exact hcentral
    _ = 2 * A * h * (P : Real) ^ 14 := by
      rw [abs_of_nonneg (by linarith)]
      ring
    _ = _ := by rfl

/-- The centered translated major-arc error integrates to at most
`10^30 * q^(-9/5) * P^9`. -/
theorem norm_intervalIntegral_chenTenTranslatedMajorArcError_le
    {P : Nat} (hP : 1 <= P) (N : Nat) (i : ChenTenArcIndex P) :
    ‖∫ z in -chenTenMajorArcRadius P i..chenTenMajorArcRadius P i,
        chenTenTranslatedMajorArcError P N i z‖ <=
      (10 : Real) ^ 30 *
        (i.denominator : Real) ^ (-9 / 5 : Real) *
          (P : Real) ^ 9 := by
  let r : Real := chenTenMajorArcRadius P i
  let h : Real := (P : Real) ^ (-5 : Real)
  let A : Real := (90 * 46 ^ 14 : Real) *
    (i.denominator : Real) ^ (-9 / 5 : Real)
  have hPpos : (0 : Real) < P := by positivity
  have hr : 0 < r := chenTenMajorArcRadius_pos
    (Nat.zero_lt_of_lt hP) i
  have hh : 0 < h := Real.rpow_pos_of_pos hPpos _
  have hscale := central_scale_rpow_identities hP
  change h * (P : Real) ^ 14 = (P : Real) ^ 9 ∧
    h ^ (-9 / 5 : Real) = (P : Real) ^ 9 at hscale
  have hcentralScale :
      2 * A * h * (P : Real) ^ 14 =
        2 * A * (P : Real) ^ 9 := by
    calc
      2 * A * h * (P : Real) ^ 14 =
          2 * A * (h * (P : Real) ^ 14) := by ring
      _ = 2 * A * (P : Real) ^ 9 := by rw [hscale.1]
  change ‖∫ z in -r..r, chenTenTranslatedMajorArcError P N i z‖ <= _
  by_cases hrh : r <= h
  · have hcentral := norm_intervalIntegral_majorArcError_central_le
      hP N i (h := r) hr.le le_rfl
    change ‖∫ z in -r..r, chenTenTranslatedMajorArcError P N i z‖ <= _
      at hcentral
    calc
      ‖∫ z in -r..r, chenTenTranslatedMajorArcError P N i z‖ <=
          2 * A * r * (P : Real) ^ 14 := hcentral
      _ <= 2 * A * h * (P : Real) ^ 14 := by gcongr
      _ = (2 * (90 * 46 ^ 14 : Real)) *
          (i.denominator : Real) ^ (-9 / 5 : Real) *
            (P : Real) ^ 9 := by
        rw [hcentralScale]
        dsimp [A]
        ring
      _ <= (10 : Real) ^ 30 *
          (i.denominator : Real) ^ (-9 / 5 : Real) *
            (P : Real) ^ 9 := by
        gcongr
        norm_num
  · have hhr : h <= r := (lt_of_not_ge hrh).le
    have hcont := continuous_chenTenTranslatedMajorArcError P N i
    have hnegInt : IntervalIntegrable (chenTenTranslatedMajorArcError P N i)
        MeasureTheory.volume (-r) (-h) := hcont.intervalIntegrable _ _
    have hcentralInt : IntervalIntegrable (chenTenTranslatedMajorArcError P N i)
        MeasureTheory.volume (-h) h := hcont.intervalIntegrable _ _
    have hposInt : IntervalIntegrable (chenTenTranslatedMajorArcError P N i)
        MeasureTheory.volume h r := hcont.intervalIntegrable _ _
    have hsplit :
        (∫ z in -r..r, chenTenTranslatedMajorArcError P N i z) =
          (∫ z in -r..-h, chenTenTranslatedMajorArcError P N i z) +
            (∫ z in -h..h, chenTenTranslatedMajorArcError P N i z) +
              ∫ z in h..r, chenTenTranslatedMajorArcError P N i z := by
      calc
        (∫ z in -r..r, chenTenTranslatedMajorArcError P N i z) =
            (∫ z in -r..-h, chenTenTranslatedMajorArcError P N i z) +
              ∫ z in -h..r, chenTenTranslatedMajorArcError P N i z :=
          (intervalIntegral.integral_add_adjacent_intervals hnegInt
            (hcentralInt.trans hposInt)).symm
        _ = (∫ z in -r..-h, chenTenTranslatedMajorArcError P N i z) +
            ((∫ z in -h..h, chenTenTranslatedMajorArcError P N i z) +
              ∫ z in h..r, chenTenTranslatedMajorArcError P N i z) := by
          rw [intervalIntegral.integral_add_adjacent_intervals
            hcentralInt hposInt]
        _ = _ := by ring
    have hneg := norm_intervalIntegral_majorArcError_outer_neg_le
      hP N i hh hhr le_rfl
    have hpos := norm_intervalIntegral_majorArcError_outer_pos_le
      hP N i hh hhr le_rfl
    have hcentral := norm_intervalIntegral_majorArcError_central_le
      hP N i hh.le hhr
    change
      ‖∫ z in -r..-h, chenTenTranslatedMajorArcError P N i z‖ <=
        A * 2 ^ 14 * ((5 / 9 : Real) * h ^ (-9 / 5 : Real)) at hneg
    change
      ‖∫ z in h..r, chenTenTranslatedMajorArcError P N i z‖ <=
        A * 2 ^ 14 * ((5 / 9 : Real) * h ^ (-9 / 5 : Real)) at hpos
    change
      ‖∫ z in -h..h, chenTenTranslatedMajorArcError P N i z‖ <=
        2 * A * h * (P : Real) ^ 14 at hcentral
    rw [hsplit]
    calc
      ‖(∫ z in -r..-h, chenTenTranslatedMajorArcError P N i z) +
            (∫ z in -h..h, chenTenTranslatedMajorArcError P N i z) +
              ∫ z in h..r, chenTenTranslatedMajorArcError P N i z‖ <=
          ‖∫ z in -r..-h, chenTenTranslatedMajorArcError P N i z‖ +
            ‖∫ z in -h..h, chenTenTranslatedMajorArcError P N i z‖ +
              ‖∫ z in h..r, chenTenTranslatedMajorArcError P N i z‖ := by
        calc
          _ <= ‖(∫ z in -r..-h, chenTenTranslatedMajorArcError P N i z) +
              (∫ z in -h..h, chenTenTranslatedMajorArcError P N i z)‖ +
                ‖∫ z in h..r, chenTenTranslatedMajorArcError P N i z‖ :=
            norm_add_le _ _
          _ <= _ := by
            gcongr
            exact norm_add_le _ _
      _ <= A * 2 ^ 14 * ((5 / 9 : Real) * h ^ (-9 / 5 : Real)) +
            2 * A * h * (P : Real) ^ 14 +
              A * 2 ^ 14 * ((5 / 9 : Real) * h ^ (-9 / 5 : Real)) :=
        add_le_add (add_le_add hneg hcentral) hpos
      _ = A * ((2 : Real) + 2 ^ 15 * (5 / 9 : Real)) *
          (P : Real) ^ 9 := by
        rw [hscale.2, hcentralScale]
        ring
      _ <= (10 : Real) ^ 30 *
          (i.denominator : Real) ^ (-9 / 5 : Real) *
            (P : Real) ^ 9 := by
        have hconstant :
            (90 * 46 ^ 14 : Real) *
                ((2 : Real) + 2 ^ 15 * (5 / 9 : Real)) <=
              (10 : Real) ^ 30 := by norm_num
        calc
          A * ((2 : Real) + 2 ^ 15 * (5 / 9 : Real)) *
              (P : Real) ^ 9 =
              ((90 * 46 ^ 14 : Real) *
                ((2 : Real) + 2 ^ 15 * (5 / 9 : Real))) *
                (i.denominator : Real) ^ (-9 / 5 : Real) *
                  (P : Real) ^ 9 := by
            dsimp [A]
            ring
          _ <= _ := by gcongr

/-- One reduced major arc contributes at most
`10^30 * q^(-9/5) * P^9` to the actual-minus-model error. -/
theorem norm_setIntegral_chenTenRepresentationIntegrand_sub_model_le_decay
    {P : Nat} (hP : 1 <= P) (N : Nat) (i : ChenTenArcIndex P) :
    ‖(∫ alpha in chenTenArc P i,
          chenTenRepresentationIntegrand P N alpha) -
        ∫ z in -chenTenMajorArcRadius P i..chenTenMajorArcRadius P i,
          chenTenMajorArcModelIntegrand P N i z‖ <=
      (10 : Real) ^ 30 *
        (i.denominator : Real) ^ (-9 / 5 : Real) *
          (P : Real) ^ 9 := by
  have hPpos : 0 < P := Nat.zero_lt_of_lt hP
  rw [setIntegral_chenTenArc_eq_intervalIntegral_add hPpos]
  have hactual : IntervalIntegrable
      (fun z : Real => chenTenRepresentationIntegrand P N
        (chenTenMajorArcCenter i + z)) MeasureTheory.volume
      (-chenTenMajorArcRadius P i) (chenTenMajorArcRadius P i) :=
    ((continuous_chenTenRepresentationIntegrand P N).comp
      (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hmodel : IntervalIntegrable
      (fun z : Real => chenTenMajorArcModelIntegrand P N i z)
      MeasureTheory.volume (-chenTenMajorArcRadius P i)
      (chenTenMajorArcRadius P i) :=
    (continuous_chenTenMajorArcModelIntegrand P N i).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hactual hmodel]
  exact norm_intervalIntegral_chenTenTranslatedMajorArcError_le hP N i

end

end Waring.Analytic
