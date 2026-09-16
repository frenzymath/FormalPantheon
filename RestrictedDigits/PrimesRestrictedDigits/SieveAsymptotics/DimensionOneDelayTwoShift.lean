import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayFiniteTails

/-!
# Two-step decay of the dimension-one delay functions

This turns the same-sign logarithmic shift into the explicit two-step bound used in the
bounded continuation of the second Rosser kernel.
-/

open Set

namespace PrimesRestrictedDigits

private theorem dimensionOneDelayScaled_log_shift_lt
    (Q scaled : Real -> Real)
    (hscale : ∀ {x : Real}, x ≠ 0 -> x ^ 2 * Q x = scaled x)
    (hpos : ∀ {x : Real}, 0 < x -> 0 < Q x)
    {t : Real} (ht : 2 <= t)
    (hshift : t * Real.log t * Q t < 48 * Q (t - 1)) :
    t * Real.log t * scaled t < 192 * scaled (t - 1) := by
  have ht0 : 0 < t := by linarith
  have hprev0 : 0 < t - 1 := by linarith
  have hsq : t ^ 2 <= 4 * (t - 1) ^ 2 := by
    have hprod : 0 <= (t - 2) * (3 * t - 2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  rw [<- hscale ht0.ne', <- hscale hprev0.ne']
  calc
    t * Real.log t * (t ^ 2 * Q t) =
        t ^ 2 * (t * Real.log t * Q t) := by ring
    _ < t ^ 2 * (48 * Q (t - 1)) :=
      mul_lt_mul_of_pos_left hshift (sq_pos_of_pos ht0)
    _ <= (4 * (t - 1) ^ 2) * (48 * Q (t - 1)) :=
      mul_le_mul_of_nonneg_right hsq
        (mul_nonneg (by norm_num) (hpos hprev0).le)
    _ = 192 * ((t - 1) ^ 2 * Q (t - 1)) := by ring

private theorem dimensionOneDelayScaled_one_shift_lt
    (scaled : Real -> Real)
    (hpos : ∀ {x : Real}, 0 < x -> 0 < scaled x)
    {t : Real} (ht : Real.exp 5000 <= t)
    (hshift : t * Real.log t * scaled t < 192 * scaled (t - 1)) :
    25 * t * scaled t < scaled (t - 1) := by
  have ht0 : 0 < t := (Real.exp_pos 5000).trans_le ht
  have hlog : 5000 <= Real.log t :=
    (Real.le_log_iff_exp_le ht0).2 ht
  have hcurrent : 0 < t * scaled t := mul_pos ht0 (hpos ht0)
  have hlogMul := mul_le_mul_of_nonneg_right hlog hcurrent.le
  have hcore : 5000 * (t * scaled t) < 192 * scaled (t - 1) := by
    calc
      5000 * (t * scaled t) <= Real.log t * (t * scaled t) := hlogMul
      _ = t * Real.log t * scaled t := by ring
      _ < 192 * scaled (t - 1) := hshift
  nlinarith

private theorem dimensionOneDelayScaledPlus_one_shift_lt
    {t : Real} (ht : Real.exp 5000 <= t) :
    25 * t * dimensionOneDelayScaledPlus t <
      dimensionOneDelayScaledPlus (t - 1) := by
  have ht2 : 2 <= t := by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  apply dimensionOneDelayScaled_one_shift_lt dimensionOneDelayScaledPlus
    (fun h => dimensionOneDelayScaledPlus_pos h) ht
  exact dimensionOneDelayScaled_log_shift_lt
    dimensionOneDelayQPlus dimensionOneDelayScaledPlus
    sq_mul_dimensionOneDelayQPlus (fun h => dimensionOneDelayQPlus_pos h) ht2
    (dimensionOneDelayQPlus_log_shift_lt ht2)

private theorem dimensionOneDelayScaledMinus_one_shift_lt
    {t : Real} (ht : Real.exp 5000 <= t) :
    25 * t * dimensionOneDelayScaledMinus t <
      dimensionOneDelayScaledMinus (t - 1) := by
  have ht2 : 2 <= t := by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  apply dimensionOneDelayScaled_one_shift_lt dimensionOneDelayScaledMinus
    (fun h => dimensionOneDelayScaledMinus_pos h) ht
  exact dimensionOneDelayScaled_log_shift_lt
    dimensionOneDelayQMinus dimensionOneDelayScaledMinus
    sq_mul_dimensionOneDelayQMinus (fun h => dimensionOneDelayQMinus_pos h) ht2
    (dimensionOneDelayQMinus_log_shift_lt ht2)

private theorem dimensionOneDelayScaled_two_shift_lt
    (scaled : Real -> Real)
    (hpos : ∀ {x : Real}, 0 < x -> 0 < scaled x)
    {lower : Real} (hanti : AntitoneOn scaled (Ici lower))
    {s u : Real} (hs : lower <= s)
    (hu : Real.exp 5000 + 1 <= u) (hsu : s + 2 <= u)
    (hone : ∀ {t : Real}, Real.exp 5000 <= t ->
      25 * t * scaled t < scaled (t - 1)) :
    625 * u ^ 2 * scaled u < 2 * scaled s := by
  have hu0 : 0 < u := by nlinarith [Real.exp_pos (5000 : Real)]
  have huPrev0 : 0 < u - 1 := by nlinarith [Real.exp_pos (5000 : Real)]
  have huTwo : Real.exp 5000 <= u := by linarith
  have huPrev : Real.exp 5000 <= u - 1 := by linarith
  have hfirst := hone huTwo
  have hsecond := hone huPrev
  have hfactor : 0 < 25 * (u - 1) := mul_pos (by norm_num) huPrev0
  have hmul := mul_lt_mul_of_pos_left hfirst hfactor
  have hchain : 625 * u * (u - 1) * scaled u < scaled (u - 2) := by
    calc
      625 * u * (u - 1) * scaled u =
          (25 * (u - 1)) * (25 * u * scaled u) := by ring
      _ < (25 * (u - 1)) * scaled (u - 1) := hmul
      _ < scaled (u - 2) := by
        have hsub : u - 1 - 1 = u - 2 := by ring
        rw [hsub] at hsecond
        exact hsecond
  have huLe : u <= 2 * (u - 1) := by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith [hu]
  have hscalePos : 0 <= 625 * u * scaled u :=
    (mul_pos (mul_pos (by norm_num) hu0) (hpos hu0)).le
  have hcoeff := mul_le_mul_of_nonneg_right huLe hscalePos
  have hsu' : s <= u - 2 := by linarith
  have huMinusTwo : lower <= u - 2 := hs.trans hsu'
  have htail : scaled (u - 2) <= scaled s :=
    hanti (show s ∈ Ici lower by exact hs)
      (show u - 2 ∈ Ici lower by exact huMinusTwo) hsu'
  calc
    625 * u ^ 2 * scaled u = u * (625 * u * scaled u) := by ring
    _ <= (2 * (u - 1)) * (625 * u * scaled u) := hcoeff
    _ = 2 * (625 * u * (u - 1) * scaled u) := by ring
    _ < 2 * scaled (u - 2) := mul_lt_mul_of_pos_left hchain (by norm_num)
    _ <= 2 * scaled s := mul_le_mul_of_nonneg_left htail (by norm_num)

/-- Explicit two-step decay for the scaled upper delay function. -/
theorem dimensionOneDelayScaledPlus_two_shift_lt
    {s u : Real} (hs : 3 <= s)
    (hu : Real.exp 5000 + 1 <= u) (hsu : s + 2 <= u) :
    625 * u ^ 2 * dimensionOneDelayScaledPlus u <
      2 * dimensionOneDelayScaledPlus s := by
  exact dimensionOneDelayScaled_two_shift_lt (lower := (1 : Real))
    dimensionOneDelayScaledPlus
    (fun h => dimensionOneDelayScaledPlus_pos h)
    dimensionOneDelayScaledPlus_antitoneOn (by linarith) hu hsu
    dimensionOneDelayScaledPlus_one_shift_lt

/-- Explicit two-step decay for the scaled lower delay function. -/
theorem dimensionOneDelayScaledMinus_two_shift_lt
    {s u : Real} (hs : 2 <= s)
    (hu : Real.exp 5000 + 1 <= u) (hsu : s + 2 <= u) :
    625 * u ^ 2 * dimensionOneDelayScaledMinus u <
      2 * dimensionOneDelayScaledMinus s := by
  exact dimensionOneDelayScaled_two_shift_lt (lower := (2 : Real))
    dimensionOneDelayScaledMinus
    (fun h => dimensionOneDelayScaledMinus_pos h)
    dimensionOneDelayScaledMinus_antitoneOn hs hu hsu
    dimensionOneDelayScaledMinus_one_shift_lt

end PrimesRestrictedDigits
