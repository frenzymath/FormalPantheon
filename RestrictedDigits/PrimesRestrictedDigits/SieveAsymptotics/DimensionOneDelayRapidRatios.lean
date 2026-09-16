import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayRapidFirstZero

/-!
# Ratio data at a first zero of the dimension-one rapid defect

This derives the logarithmic, exponential, and finite-integral inequalities used in the
explicit Lemma 16 contradiction.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

private theorem dimensionOneDelayLogWeight_monoOn :
    MonotoneOn dimensionOneDelayLogWeight (Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  unfold dimensionOneDelayLogWeight
  apply Real.strictMonoOn_log.monotoneOn
  · exact div_pos hx (by norm_num)
  · exact div_pos hy (by norm_num)
  · exact div_le_div_of_nonneg_right hxy (by norm_num)

theorem dimensionOneDelayRapidWeight_pos (s : Real) :
    0 < dimensionOneDelayRapidWeight s := by
  unfold dimensionOneDelayRapidWeight
  exact Real.exp_pos _

private theorem dimensionOneDelayRapidWeight_neg_inv_hasDerivAt
    {s : Real} (hs : 0 < s) :
    HasDerivAt (fun x => -1 / dimensionOneDelayRapidWeight x)
      (dimensionOneDelayLogWeight s / dimensionOneDelayRapidWeight s) s := by
  have h := (hasDerivAt_const s (-1 : Real)).div
    (dimensionOneDelayRapidWeight_hasDerivAt hs)
    (ne_of_gt (dimensionOneDelayRapidWeight_pos s))
  apply h.congr_deriv
  field_simp [ne_of_gt (dimensionOneDelayRapidWeight_pos s)]
  ring

private theorem dimensionOneDelayLogWeight_gt_half_of_defect_eq_zero
    {u : Real} (hu : 128 < u)
    (hD : dimensionOneDelayRapidDefect u = 0) :
    1 / 2 < dimensionOneDelayLogWeight u := by
  have hu0 : 0 < u := by linarith
  have hDu : u * dimensionOneDelaySum u * dimensionOneDelayLogWeight u =
      dimensionOneDelaySum (u - 1) := by
    unfold dimensionOneDelayRapidDefect at hD
    linarith
  have hWeighted := dimensionOneDelaySum_weighted_shift_le
    (s := u) (by linarith)
  rw [<- hDu] at hWeighted
  have hCoeff : 0 < u * dimensionOneDelaySum u :=
    mul_pos hu0 (dimensionOneDelaySum_pos hu0)
  have hCancel : dimensionOneDelayConjugateWeight u <=
      dimensionOneDelayLogWeight u *
        dimensionOneDelayConjugateWeight (u + 1) := by
    apply (mul_le_mul_iff_of_pos_left hCoeff).mp
    calc
      (u * dimensionOneDelaySum u) * dimensionOneDelayConjugateWeight u =
          u * dimensionOneDelaySum u *
            dimensionOneDelayConjugateWeight u := by ring
      _ <= u * dimensionOneDelaySum u * dimensionOneDelayLogWeight u *
          dimensionOneDelayConjugateWeight (u + 1) := hWeighted
      _ = (u * dimensionOneDelaySum u) *
          (dimensionOneDelayLogWeight u *
            dimensionOneDelayConjugateWeight (u + 1)) := by ring
  have hGPos : 0 < dimensionOneDelayConjugateWeight (u + 1) :=
    dimensionOneDelayConjugateWeight_pos (by linarith)
  have hHalfG : (1 / 2 : Real) *
      dimensionOneDelayConjugateWeight (u + 1) <
        dimensionOneDelayConjugateWeight u := by
    unfold dimensionOneDelayConjugateWeight
    nlinarith [sq_nonneg (u - 3)]
  exact (mul_lt_mul_iff_of_pos_right hGPos).mp (hHalfG.trans_le hCancel)

private theorem dimensionOneDelay_scaled_log_ratio_lt_one
    {u : Real} (hu : 1 < u) :
    (u - 1) * Real.log (u / (u - 1)) < 1 := by
  have hp : 0 < u / (u - 1) := div_pos (by linarith) (by linarith)
  have hn : u / (u - 1) ≠ 1 := by
    intro h
    have : u = u - 1 :=
      (div_eq_one_iff_eq (by linarith : u - 1 ≠ 0)).mp h
    linarith
  have hm := mul_lt_mul_of_pos_left
    (Real.log_lt_sub_one_of_pos hp hn) (by linarith : 0 < u - 1)
  calc
    (u - 1) * Real.log (u / (u - 1)) <
        (u - 1) * (u / (u - 1) - 1) := hm
    _ = 1 := by
      have hne : u - 1 ≠ 0 := by linarith
      field_simp [hne]
      ring

private theorem dimensionOneDelayLogWeight_sub {u : Real} (hu : 1 < u) :
    dimensionOneDelayLogWeight u - dimensionOneDelayLogWeight (u - 1) =
      Real.log (u / (u - 1)) := by
  unfold dimensionOneDelayLogWeight
  rw [Real.log_div (by linarith : u ≠ 0)
      (by norm_num : (128 : Real) ≠ 0),
    Real.log_div (by linarith : u - 1 ≠ 0)
      (by norm_num : (128 : Real) ≠ 0),
    Real.log_div (by linarith : u ≠ 0) (by linarith : u - 1 ≠ 0)]
  ring

private theorem dimensionOneDelayLogWeight_shift_lt
    {u : Real} (hu : 128 < u)
    (hL : 1 / 2 < dimensionOneDelayLogWeight u) :
    dimensionOneDelayLogWeight u * (u - 3) / (u - 1) <
      dimensionOneDelayLogWeight (u - 1) := by
  have h := dimensionOneDelay_scaled_log_ratio_lt_one
    (u := u) (by linarith : 1 < u)
  rw [<- dimensionOneDelayLogWeight_sub
    (u := u) (by linarith : 1 < u)] at h
  rw [div_lt_iff₀ (by linarith : 0 < u - 1)]
  nlinarith

private theorem dimensionOneDelayLogWeight_reciprocal
    {u : Real} (hu : 0 < u) :
    Real.log (128 / u) = -dimensionOneDelayLogWeight u := by
  unfold dimensionOneDelayLogWeight
  rw [Real.log_div (by norm_num : (128 : Real) ≠ 0) hu.ne',
    Real.log_div hu.ne' (by norm_num : (128 : Real) ≠ 0)]
  ring

private theorem dimensionOneDelayRapidWeight_ratio
    {u : Real} (hu : 128 < u) :
    128 / u < dimensionOneDelayRapidWeight (u - 1) /
      dimensionOneDelayRapidWeight u := by
  have hu1 : 1 < u := by linarith
  have hs := dimensionOneDelay_scaled_log_ratio_lt_one (u := u) hu1
  have hl := dimensionOneDelayLogWeight_sub (u := u) hu1
  have hr := dimensionOneDelayLogWeight_reciprocal
    (u := u) (by linarith : 0 < u)
  have he : Real.log (128 / u) <
      (u - 1) * (dimensionOneDelayLogWeight (u - 1) - 1) -
        u * (dimensionOneDelayLogWeight u - 1) := by
    rw [hr]
    nlinarith
  calc
    128 / u = Real.exp (Real.log (128 / u)) := by
      rw [Real.exp_log (div_pos (by norm_num) (by linarith))]
    _ < Real.exp ((u - 1) *
        (dimensionOneDelayLogWeight (u - 1) - 1) -
          u * (dimensionOneDelayLogWeight u - 1)) := Real.exp_lt_exp.mpr he
    _ = dimensionOneDelayRapidWeight (u - 1) /
        dimensionOneDelayRapidWeight u := by
      rw [Real.exp_sub]
      rfl

theorem dimensionOneDelayRapid_recip_integrable
    {u : Real} (hu : 1 < u) :
    IntervalIntegrable
      (fun x => 1 / (dimensionOneDelayRapidWeight x * x ^ 2))
      volume (u - 1) u := by
  have hi : u - 1 <= u := by linarith
  have hp : Icc (u - 1) u ⊆ Ioi (0 : Real) := by
    intro x hx
    change 0 < x
    linarith [hx.1]
  have hr := dimensionOneDelayRapidWeight_continuousOn.mono hp
  have hd := hr.mul (continuousOn_id.pow 2)
  exact (continuousOn_const.div hd fun x hx =>
    mul_ne_zero (ne_of_gt (dimensionOneDelayRapidWeight_pos x))
      (pow_ne_zero _ (hp hx).ne')).intervalIntegrable_of_Icc hi

private theorem dimensionOneDelayRapid_integral_majorization
    {u : Real} (hu : 128 < u)
    (hShift : dimensionOneDelayLogWeight u * (u - 3) / (u - 1) <
      dimensionOneDelayLogWeight (u - 1)) :
    dimensionOneDelayLogWeight u * (u - 3) * (u - 1) *
        (∫ x in u - 1..u,
          1 / (dimensionOneDelayRapidWeight x * x ^ 2)) <=
      1 / dimensionOneDelayRapidWeight (u - 1) -
        1 / dimensionOneDelayRapidWeight u := by
  have hi : u - 1 <= u := by linarith
  have hp : Icc (u - 1) u ⊆ Ioi (0 : Real) := by
    intro x hx
    change 0 < x
    linarith [hx.1]
  have hr := dimensionOneDelayRapidWeight_continuousOn.mono hp
  have hl := dimensionOneDelayLogWeight_continuousOn.mono hp
  have hri := dimensionOneDelayRapid_recip_integrable
    (u := u) (by linarith : 1 < u)
  have hqi : IntervalIntegrable
      (fun x => dimensionOneDelayLogWeight x /
        dimensionOneDelayRapidWeight x)
      volume (u - 1) u :=
    (hl.div hr fun x _ => ne_of_gt (dimensionOneDelayRapidWeight_pos x))
      |>.intervalIntegrable_of_Icc hi
  have hfc : ContinuousOn (fun x => -1 / dimensionOneDelayRapidWeight x)
      (Icc (u - 1) u) :=
    continuousOn_const.div hr fun x _ =>
      ne_of_gt (dimensionOneDelayRapidWeight_pos x)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hi hfc
    (fun x hx => dimensionOneDelayRapidWeight_neg_inv_hasDerivAt
      (by linarith [hx.1] : 0 < x)) hqi
  have hLu : 0 < dimensionOneDelayLogWeight u := by
    unfold dimensionOneDelayLogWeight
    exact Real.log_pos (by
      rw [one_lt_div (by norm_num : (0 : Real) < 128)]
      exact hu)
  have hpw : ∀ x ∈ Icc (u - 1) u,
      dimensionOneDelayLogWeight u * (u - 3) * (u - 1) *
          (1 / (dimensionOneDelayRapidWeight x * x ^ 2)) <=
        dimensionOneDelayLogWeight x /
          dimensionOneDelayRapidWeight x := by
    intro x hx
    have hx0 : 0 < x := hp hx
    have hle := dimensionOneDelayLogWeight_monoOn
      (by linarith : 0 < u - 1) hx0 hx.1
    have hb := hShift.trans_le hle
    have hbp : 0 < dimensionOneDelayLogWeight u * (u - 3) / (u - 1) :=
      div_pos (mul_pos hLu (by linarith)) (by linarith)
    have hs : (u - 1) ^ 2 <= x ^ 2 :=
      (sq_le_sq₀ (by linarith) hx0.le).2 hx.1
    have huOneNe : u - 1 ≠ 0 := by linarith
    have he : dimensionOneDelayLogWeight u * (u - 3) * (u - 1) =
        (u - 1) ^ 2 *
          (dimensionOneDelayLogWeight u * (u - 3) / (u - 1)) := by
      field_simp [huOneNe]
    have hc : dimensionOneDelayLogWeight u * (u - 3) * (u - 1) <
        x ^ 2 * dimensionOneDelayLogWeight x := by
      rw [he]
      exact (mul_lt_mul_of_pos_left hb (sq_pos_of_pos (by linarith))).trans_le
        (mul_le_mul_of_nonneg_right hs (hbp.trans hb).le)
    have hd : 0 < dimensionOneDelayRapidWeight x * x ^ 2 :=
      mul_pos (dimensionOneDelayRapidWeight_pos x) (sq_pos_of_pos hx0)
    calc
      _ = (dimensionOneDelayLogWeight u * (u - 3) * (u - 1)) /
          (dimensionOneDelayRapidWeight x * x ^ 2) := by ring
      _ <= dimensionOneDelayLogWeight x /
          dimensionOneDelayRapidWeight x := by
        rw [div_le_div_iff₀ hd (dimensionOneDelayRapidWeight_pos x)]
        calc
          _ <= (x ^ 2 * dimensionOneDelayLogWeight x) *
              dimensionOneDelayRapidWeight x :=
            mul_le_mul_of_nonneg_right hc.le
              (dimensionOneDelayRapidWeight_pos x).le
          _ = _ := by ring
  have hm := intervalIntegral.integral_mono_on hi
    (hri.const_mul (dimensionOneDelayLogWeight u * (u - 3) * (u - 1)))
    hqi hpw
  calc
    _ = ∫ x in u - 1..u,
        dimensionOneDelayLogWeight u * (u - 3) * (u - 1) *
          (1 / (dimensionOneDelayRapidWeight x * x ^ 2)) := by
      rw [intervalIntegral.integral_const_mul]
    _ <= ∫ x in u - 1..u,
        dimensionOneDelayLogWeight x / dimensionOneDelayRapidWeight x := hm
    _ = _ := by
      rw [hFTC]
      ring

/-- The four exact ratio bounds available at a putative first zero of the
rapid defect. -/
theorem dimensionOneDelayRapid_firstZero_ratio_data
    {u : Real} (hu : 128 < u)
    (hD : dimensionOneDelayRapidDefect u = 0) :
    1 / 2 < dimensionOneDelayLogWeight u ∧
      dimensionOneDelayLogWeight u * (u - 3) / (u - 1) <
        dimensionOneDelayLogWeight (u - 1) ∧
      128 / u < dimensionOneDelayRapidWeight (u - 1) /
        dimensionOneDelayRapidWeight u ∧
      dimensionOneDelayLogWeight u * (u - 3) * (u - 1) *
          (∫ x in u - 1..u,
            1 / (dimensionOneDelayRapidWeight x * x ^ 2)) <=
        1 / dimensionOneDelayRapidWeight (u - 1) -
          1 / dimensionOneDelayRapidWeight u := by
  have hHalf := dimensionOneDelayLogWeight_gt_half_of_defect_eq_zero hu hD
  have hShift := dimensionOneDelayLogWeight_shift_lt hu hHalf
  exact ⟨hHalf, hShift, dimensionOneDelayRapidWeight_ratio hu,
    dimensionOneDelayRapid_integral_majorization hu hShift⟩

end PrimesRestrictedDigits
