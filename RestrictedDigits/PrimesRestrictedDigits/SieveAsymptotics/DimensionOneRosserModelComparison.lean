import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelComparisonFoundations
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelRecurrences

/-!
# Uniform comparison of finite dimension-one Rosser model sums

This proves Iwaniec's Lemma 17 at `kappa=1`, `beta=2`, with one constant uniform in rank,
sign, and argument. See `IWANIEC-ROSSER-SIEVE-1980`, printed pp. 194--195.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

private theorem dimensionOneRosserModelMinus_comparisonStep
    {c : Real} (hc : 0 < c) (R : Nat)
    (hplus : forall {u : Real}, 1 < u ->
      dimensionOneRosserModelPlusPartialSum R u <
        c * dimensionOneDelayScaledPlus u)
    {s : Real} (hs : 2 <= s) :
    dimensionOneRosserModelMinusPartialSum (R + 1) s <
      c * dimensionOneDelayScaledMinus s := by
  have hsource : IntegrableOn
      (fun t => dimensionOneRosserModelPlusPartialSum R (t - 1) / (t - 1))
      (Ioi s) :=
    (integrable_shiftedRosserKernel_plusPartialSum R).integrableOn.congr_fun
      (fun t ht => rfl) measurableSet_Ioi
  have hmajor : IntegrableOn
      (fun t => c * ((t - 1) * dimensionOneDelayQPlus (t - 1)))
      (Ioi s) :=
    (dimensionOneDelayMinusRosserKernel_integrableOn hs).const_mul c
  have hle : (∫ t in Ioi s,
      dimensionOneRosserModelPlusPartialSum R (t - 1) / (t - 1)) <=
      ∫ t in Ioi s,
        c * ((t - 1) * dimensionOneDelayQPlus (t - 1)) := by
    apply integral_mono_ae hsource hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change s < t at ht
    have ht1 : 0 < t - 1 := by linarith
    have hp := (hplus (u := t - 1) (by linarith)).le
    rw [<- sq_mul_dimensionOneDelayQPlus ht1.ne'] at hp
    calc
      dimensionOneRosserModelPlusPartialSum R (t - 1) / (t - 1) <=
          (c * ((t - 1) ^ 2 * dimensionOneDelayQPlus (t - 1))) /
            (t - 1) :=
        (div_le_div_iff_of_pos_right ht1).2 hp
      _ = c * ((t - 1) * dimensionOneDelayQPlus (t - 1)) := by
        field_simp
  calc
    dimensionOneRosserModelMinusPartialSum (R + 1) s =
        ∫ t in Ioi s,
          dimensionOneRosserModelPlusPartialSum R (t - 1) / (t - 1) :=
      dimensionOneRosserModelMinusPartialSum_succ_integral R hs
    _ <= ∫ t in Ioi s,
        c * ((t - 1) * dimensionOneDelayQPlus (t - 1)) := hle
    _ = c * (∫ t in Ioi s,
        (t - 1) * dimensionOneDelayQPlus (t - 1)) := by
      rw [integral_const_mul]
    _ < c * dimensionOneDelayScaledMinus s :=
      mul_lt_mul_of_pos_left
        (dimensionOneDelayMinusRosserKernel_integral_lt hs) hc

private theorem dimensionOneRosserModelPlus_tail_le
    {c : Real} (R : Nat)
    (hminus : forall {u : Real}, 2 <= u ->
      dimensionOneRosserModelMinusPartialSum R u <
        c * dimensionOneDelayScaledMinus u)
    {s : Real} (hs : 3 <= s) :
    dimensionOneRosserModelPlusPartialSum R s <=
      c * (∫ t in Ioi s,
        (t - 1) * dimensionOneDelayQMinus (t - 1)) := by
  have hsource : IntegrableOn
      (fun t => dimensionOneRosserModelMinusPartialSum R (t - 1) / (t - 1))
      (Ioi s) :=
    (integrable_shiftedRosserKernel_minusPartialSum R).integrableOn.congr_fun
      (fun t ht => rfl) measurableSet_Ioi
  have hmajor : IntegrableOn
      (fun t => c * ((t - 1) * dimensionOneDelayQMinus (t - 1)))
      (Ioi s) :=
    (dimensionOneDelayPlusRosserKernel_integrableOn hs).const_mul c
  have hle : (∫ t in Ioi s,
      dimensionOneRosserModelMinusPartialSum R (t - 1) / (t - 1)) <=
      ∫ t in Ioi s,
        c * ((t - 1) * dimensionOneDelayQMinus (t - 1)) := by
    apply integral_mono_ae hsource hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change s < t at ht
    have ht1 : 0 < t - 1 := by linarith
    have hm := (hminus (u := t - 1) (by linarith)).le
    rw [<- sq_mul_dimensionOneDelayQMinus ht1.ne'] at hm
    calc
      dimensionOneRosserModelMinusPartialSum R (t - 1) / (t - 1) <=
          (c * ((t - 1) ^ 2 * dimensionOneDelayQMinus (t - 1))) /
            (t - 1) :=
        (div_le_div_iff_of_pos_right ht1).2 hm
      _ = c * ((t - 1) * dimensionOneDelayQMinus (t - 1)) := by
        field_simp
  calc
    dimensionOneRosserModelPlusPartialSum R s =
        ∫ t in Ioi s,
          dimensionOneRosserModelMinusPartialSum R (t - 1) / (t - 1) :=
      dimensionOneRosserModelPlusPartialSum_integral R hs
    _ <= ∫ t in Ioi s,
        c * ((t - 1) * dimensionOneDelayQMinus (t - 1)) := hle
    _ = c * (∫ t in Ioi s,
        (t - 1) * dimensionOneDelayQMinus (t - 1)) := by
      rw [integral_const_mul]

private theorem dimensionOneRosserModelPlus_comparisonStep
    {c : Real} (hc : 0 < c)
    (hreserve : 3 < c *
      (dimensionOneDelayScaledPlus 3 -
        ∫ t in Ioi (3 : Real),
          (t - 1) * dimensionOneDelayQMinus (t - 1)))
    (R : Nat)
    (hminus : forall {u : Real}, 2 <= u ->
      dimensionOneRosserModelMinusPartialSum R u <
        c * dimensionOneDelayScaledMinus u)
    {s : Real} (hs1 : 1 < s) :
    dimensionOneRosserModelPlusPartialSum R s <
      c * dimensionOneDelayScaledPlus s := by
  by_cases hs3 : 3 <= s
  · exact (dimensionOneRosserModelPlus_tail_le R hminus hs3).trans_lt
      (mul_lt_mul_of_pos_left
        (dimensionOneDelayPlusRosserKernel_integral_lt hs3) hc)
  · have hs3' : s <= 3 := le_of_not_ge hs3
    have hboundary :=
      dimensionOneRosserModelPlusPartialSum_boundary R hs1 hs3'
    have hseam := dimensionOneRosserModelPlus_tail_le R hminus
      (s := (3 : Real)) le_rfl
    have hps : dimensionOneDelayScaledPlus s = 1 / 2 :=
      dimensionOneDelayScaledPlus_eq_half_of_le hs3'
    have hp3 : dimensionOneDelayScaledPlus 3 = 1 / 2 :=
      dimensionOneDelayScaledPlus_eq_half_of_le (by norm_num)
    rw [hps]
    rw [hp3] at hreserve
    nlinarith

/-- Iwaniec's Lemma 17 at dimension one, with one comparison constant chosen
uniformly before rank, sign, and argument. -/
theorem exists_dimensionOneRosserModelPartialSums_lt_delay :
    exists c : Real, 0 < c /\
      (forall (R : Nat) {s : Real}, 1 < s ->
        dimensionOneRosserModelPlusPartialSum R s <
          c * dimensionOneDelayScaledPlus s) /\
      (forall (R : Nat) {s : Real}, 2 <= s ->
        dimensionOneRosserModelMinusPartialSum R s <
          c * dimensionOneDelayScaledMinus s) := by
  let delta := dimensionOneDelayScaledPlus 3 -
    ∫ t in Ioi (3 : Real),
      (t - 1) * dimensionOneDelayQMinus (t - 1)
  let c := 4 / delta
  have hdelta : 0 < delta := by
    unfold delta
    exact sub_pos.mpr (dimensionOneDelayPlusRosserKernel_integral_lt le_rfl)
  have hc : 0 < c := div_pos (by norm_num) hdelta
  have hreserve : 3 < c * delta := by
    have heq : c * delta = 4 := by
      unfold c
      field_simp [hdelta.ne']
    linarith
  have hcomparison : forall R : Nat,
      (forall {s : Real}, 2 <= s ->
        dimensionOneRosserModelMinusPartialSum R s <
          c * dimensionOneDelayScaledMinus s) /\
      (forall {s : Real}, 1 < s ->
        dimensionOneRosserModelPlusPartialSum R s <
          c * dimensionOneDelayScaledPlus s) := by
    intro R
    induction R with
    | zero =>
        have hminus : forall {s : Real}, 2 <= s ->
            dimensionOneRosserModelMinusPartialSum 0 s <
              c * dimensionOneDelayScaledMinus s := by
          intro s hs
          rw [dimensionOneRosserModelMinusPartialSum_zero]
          have hs0 : 0 < s := by linarith
          have hscaled : 0 < dimensionOneDelayScaledMinus s := by
            rw [<- sq_mul_dimensionOneDelayQMinus hs0.ne']
            exact mul_pos (sq_pos_of_pos hs0)
              (dimensionOneDelayQMinus_pos hs0)
          exact mul_pos hc hscaled
        exact ⟨hminus, fun hs =>
          dimensionOneRosserModelPlus_comparisonStep hc hreserve 0 hminus hs⟩
    | succ R ih =>
        have hminus : forall {s : Real}, 2 <= s ->
            dimensionOneRosserModelMinusPartialSum (R + 1) s <
              c * dimensionOneDelayScaledMinus s :=
          fun hs => dimensionOneRosserModelMinus_comparisonStep hc R ih.2 hs
        exact ⟨hminus, fun hs =>
          dimensionOneRosserModelPlus_comparisonStep hc hreserve
            (R + 1) hminus hs⟩
  refine ⟨c, hc, ?_, ?_⟩
  · intro R s hs
    exact (hcomparison R).2 hs
  · intro R s hs
    exact (hcomparison R).1 hs

end PrimesRestrictedDigits
