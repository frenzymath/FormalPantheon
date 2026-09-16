import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayRapidRatios

/-!
# Explicit rapid decay of the dimension-one delay sum

This completes the repaired first-zero contradiction in Iwaniec's Lemma 16 and proves global
negativity of its logarithmic derivative numerator. See `IWANIEC-ROSSER-SIEVE-1980`, printed
pp. 191--193.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

private theorem dimensionOneDelayRapid_averaging_recip_lower
    {u : Real} (hu : 128 < u)
    (hD : dimensionOneDelayRapidDefect u = 0)
    (hAnti : StrictAntiOn dimensionOneDelayRapidWeightedSum (Icc 3 u))
    (hLPos : 0 < dimensionOneDelayLogWeight u) :
    dimensionOneDelayConjugateWeight u / dimensionOneDelayLogWeight u <=
      dimensionOneDelayRapidWeight (u - 1) * (u - 1) ^ 2 *
        dimensionOneDelayConjugateWeight (u + 1) *
          (∫ x in u - 1..u,
            1 / (dimensionOneDelayRapidWeight x * x ^ 2)) := by
  have hu0 : 0 < u := by linarith
  have hi : u - 1 <= u := by linarith
  have hp : Icc (u - 1) u ⊆ Ioi (0 : Real) := by
    intro x hx
    change 0 < x
    linarith [hx.1]
  have hwin : Icc (u - 1) u ⊆ Icc (3 : Real) u := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hleft : u - 1 ∈ Icc (3 : Real) u :=
    ⟨by linarith, by linarith⟩
  have hgc : Continuous (fun x : Real =>
      dimensionOneDelayConjugateWeight (x + 1)) :=
    dimensionOneDelayConjugateWeight_continuous.comp
      (continuous_id.add continuous_const)
  have hfi : IntervalIntegrable (fun x : Real =>
      dimensionOneDelaySum x * dimensionOneDelayConjugateWeight (x + 1))
      volume (u - 1) u :=
    ((dimensionOneDelaySum_continuousOn.mono hp).mul hgc.continuousOn)
      |>.intervalIntegrable_of_Icc hi
  have hri := dimensionOneDelayRapid_recip_integrable
    (u := u) (by linarith : 1 < u)
  let K := dimensionOneDelayRapidWeight (u - 1) * (u - 1) ^ 2 *
    dimensionOneDelaySum (u - 1) *
      dimensionOneDelayConjugateWeight (u + 1)
  have hpw : ∀ x ∈ Icc (u - 1) u,
      dimensionOneDelaySum x * dimensionOneDelayConjugateWeight (x + 1) <=
        K * (1 / (dimensionOneDelayRapidWeight x * x ^ 2)) := by
    intro x hx
    have hx0 : 0 < x := hp hx
    have hd : 0 < dimensionOneDelayRapidWeight x * x ^ 2 :=
      mul_pos (dimensionOneDelayRapidWeight_pos x) (sq_pos_of_pos hx0)
    have hA := hAnti.antitoneOn hleft (hwin hx) hx.1
    have ha : dimensionOneDelaySum x <=
        dimensionOneDelayRapidWeightedSum (u - 1) /
          (dimensionOneDelayRapidWeight x * x ^ 2) := by
      rw [le_div_iff₀ hd]
      calc
        dimensionOneDelaySum x *
            (dimensionOneDelayRapidWeight x * x ^ 2) =
            dimensionOneDelayRapidWeightedSum x := by
          unfold dimensionOneDelayRapidWeightedSum
          ring
        _ <= dimensionOneDelayRapidWeightedSum (u - 1) := hA
    have hg : dimensionOneDelayConjugateWeight (x + 1) <=
        dimensionOneDelayConjugateWeight (u + 1) :=
      dimensionOneDelayConjugateWeight_monoOn
        (by change 1 <= x + 1; linarith [hx.1])
        (by change 1 <= u + 1; linarith)
        (by linarith [hx.2])
    have hAp : 0 <= dimensionOneDelayRapidWeightedSum (u - 1) := by
      unfold dimensionOneDelayRapidWeightedSum
      exact mul_nonneg (dimensionOneDelayRapidWeight_pos (u - 1)).le
        (mul_nonneg (sq_nonneg (u - 1))
          (dimensionOneDelaySum_pos (by linarith : 0 < u - 1)).le)
    have hAf : 0 <= dimensionOneDelayRapidWeightedSum (u - 1) /
        (dimensionOneDelayRapidWeight x * x ^ 2) := div_nonneg hAp hd.le
    calc
      _ <= (dimensionOneDelayRapidWeightedSum (u - 1) /
          (dimensionOneDelayRapidWeight x * x ^ 2)) *
            dimensionOneDelayConjugateWeight (x + 1) :=
        mul_le_mul_of_nonneg_right ha
          (dimensionOneDelayConjugateWeight_pos (by linarith [hx.1])).le
      _ <= (dimensionOneDelayRapidWeightedSum (u - 1) /
          (dimensionOneDelayRapidWeight x * x ^ 2)) *
            dimensionOneDelayConjugateWeight (u + 1) :=
        mul_le_mul_of_nonneg_left hg hAf
      _ = K * (1 / (dimensionOneDelayRapidWeight x * x ^ 2)) := by
        unfold K dimensionOneDelayRapidWeightedSum
        ring
  have hint := intervalIntegral.integral_mono_on hi hfi
    (hri.const_mul K) hpw
  have havg : u * dimensionOneDelaySum u *
      dimensionOneDelayConjugateWeight u <=
      K * (∫ x in u - 1..u,
        1 / (dimensionOneDelayRapidWeight x * x ^ 2)) := by
    calc
      _ = ∫ x in u - 1..u,
          dimensionOneDelaySum x *
            dimensionOneDelayConjugateWeight (x + 1) :=
        dimensionOneDelaySum_averaging (by linarith)
      _ <= ∫ x in u - 1..u,
          K * (1 / (dimensionOneDelayRapidWeight x * x ^ 2)) := hint
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  have hDu : u * dimensionOneDelaySum u * dimensionOneDelayLogWeight u =
      dimensionOneDelaySum (u - 1) := by
    unfold dimensionOneDelayRapidDefect at hD
    linarith
  let B := dimensionOneDelayRapidWeight (u - 1) * (u - 1) ^ 2 *
    dimensionOneDelayConjugateWeight (u + 1) *
      (∫ x in u - 1..u,
        1 / (dimensionOneDelayRapidWeight x * x ^ 2))
  have hc : 0 < u * dimensionOneDelaySum u :=
    mul_pos hu0 (dimensionOneDelaySum_pos hu0)
  have hGB : dimensionOneDelayConjugateWeight u <=
      dimensionOneDelayLogWeight u * B := by
    apply (mul_le_mul_iff_of_pos_left hc).mp
    calc
      _ = u * dimensionOneDelaySum u *
          dimensionOneDelayConjugateWeight u := by ring
      _ <= K * (∫ x in u - 1..u,
          1 / (dimensionOneDelayRapidWeight x * x ^ 2)) := havg
      _ = (u * dimensionOneDelaySum u) *
          (dimensionOneDelayLogWeight u * B) := by
        unfold K B
        rw [<- hDu]
        ring
  rw [div_le_iff₀ hLPos]
  change dimensionOneDelayConjugateWeight u <=
    B * dimensionOneDelayLogWeight u
  exact hGB.trans_eq (mul_comm _ _)

private theorem dimensionOneDelayConjugateWeight_final_ratio
    {u : Real} (hu : 128 < u) :
    (u - 128) / u <
      (u - 3) * dimensionOneDelayConjugateWeight u /
        ((u - 1) * dimensionOneDelayConjugateWeight (u + 1)) := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  have hg : 0 < dimensionOneDelayConjugateWeight (u + 1) :=
    dimensionOneDelayConjugateWeight_pos (by linarith)
  rw [div_lt_div_iff₀ hu0 (mul_pos hu1 hg)]
  unfold dimensionOneDelayConjugateWeight
  have hs : 128 * u < u ^ 2 := by
    have h := mul_lt_mul_of_pos_right hu (by linarith : 0 < u)
    nlinarith
  have hf : 1 < 124 * u - 121 := by linarith
  have hp : u ^ 2 < u ^ 2 * (124 * u - 121) := by
    simpa only [mul_one] using
      mul_lt_mul_of_pos_left hf (sq_pos_of_pos hu0)
  nlinarith

private theorem dimensionOneDelayRapid_firstZero_contradiction
    {u : Real} (hu : 128 < u)
    (hD : dimensionOneDelayRapidDefect u = 0)
    (hAnti : StrictAntiOn dimensionOneDelayRapidWeightedSum (Icc 3 u)) :
    False := by
  rcases dimensionOneDelayRapid_firstZero_ratio_data hu hD with
    ⟨hhalf, _hShift, hratio, hup⟩
  have hL : 0 < dimensionOneDelayLogWeight u := by linarith
  let I := ∫ x in u - 1..u,
    1 / (dimensionOneDelayRapidWeight x * x ^ 2)
  have hlo : dimensionOneDelayConjugateWeight u /
      dimensionOneDelayLogWeight u <=
      dimensionOneDelayRapidWeight (u - 1) * (u - 1) ^ 2 *
        dimensionOneDelayConjugateWeight (u + 1) * I :=
    dimensionOneDelayRapid_averaging_recip_lower hu hD hAnti hL
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  have hg : 0 < dimensionOneDelayConjugateWeight (u + 1) :=
    dimensionOneDelayConjugateWeight_pos (by linarith)
  have hrp : 0 < dimensionOneDelayRapidWeight (u - 1) :=
    dimensionOneDelayRapidWeight_pos _
  have hru : 0 < dimensionOneDelayRapidWeight u :=
    dimensionOneDelayRapidWeight_pos _
  let C := dimensionOneDelayLogWeight u * (u - 3) * (u - 1)
  let K := dimensionOneDelayRapidWeight (u - 1) * (u - 1) ^ 2 *
    dimensionOneDelayConjugateWeight (u + 1)
  have hCp : 0 < C := by
    unfold C
    exact mul_pos (mul_pos hL (by linarith)) (by linarith)
  have hKp : 0 < K := by
    unfold K
    exact mul_pos (mul_pos hrp (sq_pos_of_pos hu1)) hg
  have hlm := mul_le_mul_of_nonneg_left hlo hCp.le
  have hum := mul_le_mul_of_nonneg_left hup hKp.le
  have hc : dimensionOneDelayConjugateWeight u * (u - 3) * (u - 1) <=
      (u - 1) ^ 2 * dimensionOneDelayConjugateWeight (u + 1) *
        (1 - dimensionOneDelayRapidWeight (u - 1) /
          dimensionOneDelayRapidWeight u) := by
    calc
      dimensionOneDelayConjugateWeight u * (u - 3) * (u - 1) =
          C * (dimensionOneDelayConjugateWeight u /
            dimensionOneDelayLogWeight u) := by
        unfold C
        field_simp [hL.ne']
      _ <= C * (K * I) := hlm
      _ = K * (C * I) := by ring
      _ <= K * (1 / dimensionOneDelayRapidWeight (u - 1) -
          1 / dimensionOneDelayRapidWeight u) := hum
      _ = (u - 1) ^ 2 * dimensionOneDelayConjugateWeight (u + 1) *
          (1 - dimensionOneDelayRapidWeight (u - 1) /
            dimensionOneDelayRapidWeight u) := by
        unfold K
        field_simp [hrp.ne', hru.ne']
  have hc' : dimensionOneDelayConjugateWeight u * (u - 3) <=
      (u - 1) * dimensionOneDelayConjugateWeight (u + 1) *
        (1 - dimensionOneDelayRapidWeight (u - 1) /
          dimensionOneDelayRapidWeight u) := by
    apply (mul_le_mul_iff_of_pos_right hu1).mp
    calc
      _ = dimensionOneDelayConjugateWeight u * (u - 3) * (u - 1) := by ring
      _ <= (u - 1) ^ 2 * dimensionOneDelayConjugateWeight (u + 1) *
          (1 - dimensionOneDelayRapidWeight (u - 1) /
            dimensionOneDelayRapidWeight u) := hc
      _ = ((u - 1) * dimensionOneDelayConjugateWeight (u + 1) *
          (1 - dimensionOneDelayRapidWeight (u - 1) /
            dimensionOneDelayRapidWeight u)) * (u - 1) := by ring
  have hd : 0 < (u - 1) * dimensionOneDelayConjugateWeight (u + 1) :=
    mul_pos hu1 hg
  have hbad0 : (u - 3) * dimensionOneDelayConjugateWeight u /
      ((u - 1) * dimensionOneDelayConjugateWeight (u + 1)) <=
        1 - dimensionOneDelayRapidWeight (u - 1) /
          dimensionOneDelayRapidWeight u := by
    rw [div_le_iff₀ hd]
    nlinarith
  have hbad1 : 1 - dimensionOneDelayRapidWeight (u - 1) /
      dimensionOneDelayRapidWeight u < 1 - 128 / u := by linarith
  have he : 1 - 128 / u = (u - 128) / u := by
    field_simp [hu0.ne']
  have hbad : (u - 3) * dimensionOneDelayConjugateWeight u /
      ((u - 1) * dimensionOneDelayConjugateWeight (u + 1)) <
        (u - 128) / u := by
    rw [<- he]
    exact hbad0.trans_lt hbad1
  exact (dimensionOneDelayConjugateWeight_final_ratio hu).asymm hbad

/-- The explicit rapid defect is strictly negative on its complete source
domain. -/
theorem dimensionOneDelayRapidDefect_neg
    {s : Real} (hs : 3 <= s) :
    dimensionOneDelayRapidDefect s < 0 := by
  by_contra h
  obtain ⟨u, hu, _hus, hDu, hAnti⟩ :=
    dimensionOneDelayRapidDefect_firstZero hs (le_of_not_gt h)
  exact dimensionOneDelayRapid_firstZero_contradiction hu hDu hAnti

/-- Iwaniec's Lemma 16 for the explicit absolute rapid weight fixed above. -/
theorem dimensionOneDelayRapidWeightedSum_strictAntiOn :
    StrictAntiOn dimensionOneDelayRapidWeightedSum (Ici 3) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg
    (D := Ici (3 : Real))
    (f' := fun s => dimensionOneDelayRapidWeight s * s *
      dimensionOneDelayRapidDefect s)
    (convex_Ici 3)
    (dimensionOneDelayRapidWeightedSum_continuousOn.mono fun s hs => by
      change 3 <= s at hs
      change 0 < s
      linarith) ?_ ?_
  · intro s hs
    rw [interior_Ici] at hs
    change 3 < s at hs
    exact (dimensionOneDelayRapidWeightedSum_hasDerivAt hs).hasDerivWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    change 3 < s at hs
    exact mul_neg_of_pos_of_neg
      (mul_pos (dimensionOneDelayRapidWeight_pos s) (by linarith))
      (dimensionOneDelayRapidDefect_neg hs.le)

end PrimesRestrictedDigits
