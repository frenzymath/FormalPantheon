import BoundedGaps.Maynard.ConcreteS2RestrictedYSquarePerturbation

set_option maxRecDepth 14000
set_option maxHeartbeats 3000000

noncomputable section

/-!
# Strong restricted-Y square perturbation

The coordinate-one restricted transform is compared with its full fiber on
the exact exponent-106 square scale. Unlike the older logarithmic-scale
bound, this proof retains both pre-sieve-density factors in the finite
envelope before taking the limit.

This is the restricted-Y part of SEM-396, corresponding to Maynard2013v3,
Lemma 5.2 and the restricted-transform calculation in Section 5.
-/

namespace BoundedGaps.Maynard

open Filter
open scoped BigOperators

theorem tendsto_engelsmaS2CoordinateOneSquarePerturbationEnvelope_div_squareScale_zero
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun N : ℕ =>
      maynardS2CoordinateOneSquarePerturbationEnvelope
        BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
        (tripleLogCutoff (N - 1)) m smallKCandidateBound /
      ((preSieveSingularSeries (tripleLogCutoff (N - 1)) : ℝ) ^ 2 *
        Real.log (engelsmaMaynardRadius alpha N) ^ 2))
      atTop (nhds 0) := by
  let B : ℝ := smallKCandidateBound
  let k : ℝ := ((Finset.univ.erase m).card : ℝ)
  let L : ℕ → ℝ := fun N => Real.log (engelsmaMaynardRadius alpha N)
  let D : ℕ → ℝ := fun N => tripleLogCutoff (N - 1)
  let S : ℕ → ℝ := fun N =>
    preSieveSingularSeries (tripleLogCutoff (N - 1))
  let A : ℕ → ℝ := fun N =>
    8 / D N + (8 * Real.exp 8 / D N) *
      (1 + 8 * Real.exp 8 / D N) ^ ((Finset.univ.erase m).card - 1)
  have hL : Tendsto L atTop atTop := by
    simpa [L] using tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hD : Tendsto D atTop atTop := by
    change Tendsto (fun N : ℕ => (tripleLogCutoff (N - 1) : ℝ)) atTop atTop
    exact tendsto_natCast_atTop_atTop.comp tendsto_shifted_tripleLogCutoff
  have hA : Tendsto A atTop (nhds 0) := by
    have hi : Tendsto (fun N => (1 : ℝ) / D N) atTop (nhds 0) := by
      simpa [one_div] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
          atTop (nhds 1)).div_atTop hD)
    have ht : Tendsto (fun N => 8 * Real.exp 8 / D N)
        atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using hi.const_mul (8 * Real.exp 8)
    have hp : Tendsto (fun N =>
        (1 + 8 * Real.exp 8 / D N) ^ ((Finset.univ.erase m).card - 1))
        atTop (nhds 1) := by
      simpa [add_comm] using (ht.add_const 1).pow
        ((Finset.univ.erase m).card - 1)
    simpa [A, div_eq_mul_inv] using
      (hi.const_mul 8).add (by simpa [div_eq_mul_inv] using ht.mul hp)
  have hsmallA : ∀ᶠ N : ℕ in atTop, 0 ≤ A N ∧ A N ≤ 1 := by
    filter_upwards [hA.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos),
      hD.eventually (eventually_gt_atTop 0)] with N hN hDN
    have h0 : 0 ≤ A N := by
      dsimp [A]
      positivity
    exact ⟨h0, le_of_lt (by
      simpa [Real.dist_eq, abs_of_nonneg h0] using hN)⟩
  have hLone : ∀ᶠ N : ℕ in atTop, 1 ≤ L N :=
    hL.eventually (eventually_ge_atTop 1)
  have hWL := eventually_engelsmaMaynardCrossBound_conditions halpha
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hupper : Tendsto (fun N : ℕ =>
      (512 * (smallKCandidateBound : ℝ) ^ 2 *
        ((Finset.univ.erase m).card : ℝ) *
        (1 + (Finset.univ.erase m).card)) * A N)
      atTop (nhds 0) := by
    simpa using hA.const_mul (512 * (smallKCandidateBound : ℝ) ^ 2 *
      ((Finset.univ.erase m).card : ℝ) *
      (1 + (Finset.univ.erase m).card))
  apply squeeze_zero' (Eventually.of_forall (fun N => abs_nonneg _)) ?_ hupper
  filter_upwards [hsmallA, hLone, hWL] with N ⟨hA0, hA1⟩ hL1 hcond
  let R := engelsmaMaynardRadius alpha N
  let DD := tripleLogCutoff (N - 1)
  let SS := preSieveSingularSeries DD
  let LL := L N
  let MM := preSievedCoordinateInvTotientMass (primorial DD) R
  let AA := A N
  have hS : 0 < SS := preSieveSingularSeries_pos DD
  have hLpos : 0 < LL := lt_of_lt_of_le zero_lt_one hL1
  have hB : 0 ≤ B := by simpa [B] using smallKCandidateBound_nonneg
  have hk : 0 ≤ k := by positivity
  have hAA0 : 0 ≤ AA := by simpa [AA] using hA0
  have hAA1 : AA ≤ 1 := by simpa [AA] using hA1
  have hSeq : SS = (Nat.totient (primorial DD) : ℝ) /
      (primorial DD : ℝ) := by
    simpa [SS] using preSieveSingularSeries_eq_totient_div DD
  have hM : MM ≤ 8 * SS * (1 + LL) := by
    have hp : MM ≤ squarefreeCoprimeInvTotientMean (primorial DD) R := by
      simpa [MM, preSievedCoordinateInvTotientMass] using
        preSievedCoordinateInvTotientSum_le (primorial DD) R
    have hm := squarefreeCoprimeInvTotientMean_le_log
      (W := primorial DD) (Q := R) (primorial_pos DD) (by
        simpa [R, DD, engelsmaMaynardModulus] using hcond.2.2)
    simpa [MM, SS, LL, R, DD, preSieveSingularSeries_eq_totient_div] using
      hp.trans hm
  have hratio : (1 + LL) / LL ≤ 2 := by
    apply (div_le_iff₀ hLpos).2
    linarith
  have hMr : MM / (SS * LL) ≤ 8 * ((1 + LL) / LL) := by
    calc
      MM / (SS * LL) ≤ (8 * SS * (1 + LL)) / (SS * LL) :=
        div_le_div_of_nonneg_right hM (by positivity)
      _ = 8 * ((1 + LL) / LL) := by field_simp [hS.ne', hLpos.ne']
  have hMr0 : 0 ≤ MM / (SS * LL) := by
    unfold MM preSievedCoordinateInvTotientMass
    positivity
  have hMM0 : 0 ≤ MM := by
    unfold MM preSievedCoordinateInvTotientMass
    positivity
  have hfac : 0 ≤ 8 * ((1 + LL) / LL) := by positivity
  have hfacLe : 8 * ((1 + LL) / LL) ≤ 16 := by nlinarith
  have hfirst : B * (MM / (SS * LL)) +
      B * k * 8 * ((1 + LL) / LL) * AA ≤ 16 * B * (1 + k) := by
    have ht : B * k * 8 * ((1 + LL) / LL) * AA ≤ 16 * B * k := by
      calc
        B * k * 8 * ((1 + LL) / LL) * AA ≤
            B * k * 8 * ((1 + LL) / LL) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                (mul_le_mul_of_nonneg_left hAA1
                  (mul_nonneg (mul_nonneg hB hk) hfac))
        _ ≤ 16 * B * k := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (mul_le_mul_of_nonneg_left hfacLe (mul_nonneg hB hk))
    calc
      _ ≤ B * (8 * ((1 + LL) / LL)) + 16 * B * k :=
        add_le_add (mul_le_mul_of_nonneg_left hMr hB) ht
      _ ≤ 16 * B + 16 * B * k := by
        exact add_le_add
          (by simpa [mul_assoc, mul_left_comm, mul_comm] using
            (mul_le_mul_of_nonneg_left hfacLe hB)) le_rfl
      _ = 16 * B * (1 + k) := by ring
  have hsecond : B * k * 8 * ((1 + LL) / LL) * AA ≤
      16 * B * k * AA := by
    have ht : B * k * 8 * ((1 + LL) / LL) ≤ 16 * B * k := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_left hfacLe (mul_nonneg hB hk))
    exact mul_le_mul_of_nonneg_right ht hAA0
  have hratioBound :
      2 * (B * (MM / (SS * LL)) +
        B * k * 8 * ((1 + LL) / LL) * AA) *
        (B * k * 8 * ((1 + LL) / LL) * AA) ≤
      512 * B ^ 2 * k * (1 + k) * AA := by
    calc
      _ ≤ (2 * (16 * B * (1 + k))) * (16 * B * k * AA) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hfirst (by positivity))
          hsecond (by positivity) (by positivity)
      _ = _ := by ring
  have hEid :
      maynardS2CoordinateOneSquarePerturbationEnvelope
          BoundedGaps.engelsmaTuple R DD m B /
        (SS ^ 2 * LL ^ 2) =
      2 * (B * (MM / (SS * LL)) +
        B * k * 8 * ((1 + LL) / LL) * AA) *
        (B * k * 8 * ((1 + LL) / LL) * AA) := by
    unfold maynardS2CoordinateOneSquarePerturbationEnvelope
    rw [← hSeq]
    field_simp [hS.ne', hLpos.ne']
    ring
  have hE0 : 0 ≤ maynardS2CoordinateOneSquarePerturbationEnvelope
      BoundedGaps.engelsmaTuple R DD m B := by
    unfold maynardS2CoordinateOneSquarePerturbationEnvelope
    rw [← hSeq]
    positivity
  have hbound :
      0 ≤ maynardS2CoordinateOneSquarePerturbationEnvelope
          BoundedGaps.engelsmaTuple R DD m B ∧
      maynardS2CoordinateOneSquarePerturbationEnvelope
          BoundedGaps.engelsmaTuple R DD m B /
        (SS ^ 2 * LL ^ 2) ≤ 512 * B ^ 2 * k * (1 + k) * AA := by
    refine ⟨hE0, ?_⟩
    rw [hEid]
    simpa using hratioBound
  rw [abs_of_nonneg (div_nonneg hbound.1 (by positivity))]
  simpa [S, L, A, B, k, R, DD, SS, LL, AA] using hbound.2

theorem tendsto_engelsmaS2CoordinateOneSquarePerturbation_div_squareScale_zero
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun N : ℕ =>
      (∑ r ∈ (maynardDivisorTupleSupport BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)).filter
          (fun r => r m = 1),
        maynardS2CoordinateOneSquarePerturbationEnvelope
          BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
          (tripleLogCutoff (N - 1)) m smallKCandidateBound /
          |∏ h : BoundedGaps.engelsmaTuple,
            (maynardS2G (r h) : ℝ)|) /
      (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
        Real.log (engelsmaMaynardRadius alpha N)) ^ 106)
      atTop (nhds 0) := by
  let H := engelsmaOffFaceFinset m
  let k := Fintype.card H
  let L : ℕ → ℝ := fun N => Real.log (engelsmaMaynardRadius alpha N)
  let S : ℕ → ℝ := fun N =>
    preSieveSingularSeries (tripleLogCutoff (N - 1))
  let Q : ℕ → ℝ := fun N => S N * L N
  let M : ℕ → ℝ := fun N =>
    maynardS2ReciprocalGSquarefreeMean
      (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N)
  have hL : Tendsto L atTop atTop := by
    simpa [L] using tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hS : ∀ᶠ N : ℕ in atTop, 0 < S N := by
    filter_upwards [] with N
    exact preSieveSingularSeries_pos _
  have hQ : ∀ᶠ N : ℕ in atTop, 0 < Q N := by
    filter_upwards [hS, hL.eventually (eventually_gt_atTop 0)] with N hSN hLN
    exact mul_pos hSN hLN
  have hcoord : ∀ h : H, Tendsto (fun N : ℕ => M N / Q N)
      atTop (nhds 1) := by
    intro h
    simpa [M, Q, S, L] using
      tendsto_engelsmaReciprocalGSquarefreeMean_div_leadingTerm_one halpha
  have hprod : Tendsto (fun N : ℕ => ∏ h : H, M N / Q N)
      atTop (nhds 1) := by
    have hp : Tendsto (fun N : ℕ => ∏ h : H, M N / Q N) atTop
        (nhds (∏ _h : H, (1 : ℝ))) := by
      apply tendsto_finsetProd Finset.univ
      intro h hh
      exact hcoord h
    simpa using hp
  have hboxNorm : Tendsto (fun N : ℕ =>
      (∏ h : H, M N) / (Q N) ^ k) atTop (nhds 1) := by
    apply hprod.congr'
    filter_upwards [] with N
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const]
    rfl
  have hboxLe : ∀ᶠ N : ℕ in atTop,
      (∏ h : H, M N) / (Q N) ^ k ≤ 2 := by
    filter_upwards [hboxNorm.eventually
      (Metric.ball_mem_nhds (1 : ℝ) one_pos)] with N hN
    have hd : |(∏ h : H, M N) / (Q N) ^ k - 1| < 1 := by
      simpa [Real.dist_eq] using hN
    linarith [le_abs_self ((∏ h : H, M N) / (Q N) ^ k - 1)]
  have hmassLe : ∀ᶠ N : ℕ in atTop,
      engelsmaS2CoordinateOneReciprocalGMass
          (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m /
        (Q N) ^ k ≤ 2 := by
    filter_upwards [hboxLe, hQ] with N hboxN hQN
    rw [engelsmaS2CoordinateOneReciprocalGMass_eq_offFace]
    have hmass := engelsmaS2OffFaceReciprocalGMass_le_box
      (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m
    exact (div_le_div_of_nonneg_right hmass (by positivity)).trans (by
      simpa [Q, S, L, M, H, k, engelsmaMaynardModulus] using hboxN)
  have hmass0 : ∀ᶠ N : ℕ in atTop,
      0 ≤ engelsmaS2CoordinateOneReciprocalGMass
          (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m := by
    filter_upwards [] with N
    unfold engelsmaS2CoordinateOneReciprocalGMass
    exact Finset.sum_nonneg (fun r hr => by positivity)
  have hcondEvent := eventually_engelsmaMaynardCrossBound_conditions halpha
  have henv :=
    tendsto_engelsmaS2CoordinateOneSquarePerturbationEnvelope_div_squareScale_zero
      halpha m
  have hupper : Tendsto (fun N : ℕ =>
      2 * (maynardS2CoordinateOneSquarePerturbationEnvelope
        BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
        (tripleLogCutoff (N - 1)) m smallKCandidateBound /
        ((preSieveSingularSeries (tripleLogCutoff (N - 1)) : ℝ) ^ 2 *
          L N ^ 2))) atTop (nhds 0) := by
    simpa using henv.const_mul 2
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun N => abs_nonneg _)) ?_ hupper
  filter_upwards [hmassLe, hmass0, hQ, hS,
      hL.eventually (eventually_gt_atTop 0), hcondEvent] with
      N hmassN hmassNonneg hQN hSN hLN hcond
  let E := maynardS2CoordinateOneSquarePerturbationEnvelope
    BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
    (tripleLogCutoff (N - 1)) m smallKCandidateBound
  let T := engelsmaS2CoordinateOneReciprocalGMass
    (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m
  let SS := S N
  let LL := L N
  have hSpos : 0 < SS := hSN
  have hLpos : 0 < LL := hLN
  have hQpos : 0 < Q N := hQN
  have hT0 : 0 ≤ T := by simpa [T] using hmassNonneg
  have hQk : 0 < (Q N) ^ k := by positivity
  have hsum :
      (∑ r ∈ engelsmaS2CoordinateFiberCoordinateOneSupport
          (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m,
        E / |∏ h : BoundedGaps.engelsmaTuple,
          (maynardS2G (r h) : ℝ)|) = E * T := by
    calc
      (∑ r ∈ engelsmaS2CoordinateFiberCoordinateOneSupport
          (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m,
        E / |∏ h : BoundedGaps.engelsmaTuple,
          (maynardS2G (r h) : ℝ)|) =
          ∑ r ∈ engelsmaS2CoordinateFiberCoordinateOneSupport
            (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m,
            E * (1 / |∏ h : BoundedGaps.engelsmaTuple,
              (maynardS2G (r h) : ℝ)|) := by
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ = E * T := by
        rw [← Finset.mul_sum]
        rfl
  have hsum' :
      (∑ r ∈ (maynardDivisorTupleSupport BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha N) (primorial (tripleLogCutoff (N - 1)))).filter
          (fun r => r m = 1),
        E / |∏ h : BoundedGaps.engelsmaTuple,
          (maynardS2G (r h) : ℝ)|) = E * T := by
    simpa [engelsmaS2CoordinateFiberCoordinateOneSupport] using hsum
  have hratio :
      (E * T) / (Q N) ^ 106 =
        (E / (SS ^ 2 * LL ^ 2)) * (T / (Q N) ^ k) := by
    have hk : k = 104 := by
      simp [k, H, engelsmaOffFaceFinset,
        Finset.card_erase_of_mem m.property,
        BoundedGaps.engelsmaTuple_card]
    rw [hk]
    field_simp [hSpos.ne', hLpos.ne', hQpos.ne']
    ring
  have hE0 : 0 ≤ E := by
    have hM0 : 0 ≤ preSievedCoordinateInvTotientMass
        (primorial (tripleLogCutoff (N - 1)))
        (engelsmaMaynardRadius alpha N) := by
      unfold preSievedCoordinateInvTotientMass
      positivity
    have hSeq : preSieveSingularSeries (tripleLogCutoff (N - 1)) =
        (Nat.totient (primorial (tripleLogCutoff (N - 1))) : ℝ) /
          (primorial (tripleLogCutoff (N - 1)) : ℝ) := by
      exact preSieveSingularSeries_eq_totient_div _
    have hSdirect : 0 ≤
        preSieveSingularSeries (tripleLogCutoff (N - 1)) :=
      (preSieveSingularSeries_pos _).le
    have hDdirect : 0 < (tripleLogCutoff (N - 1) : ℝ) := by
      exact_mod_cast hcond.2.1
    have hLdirect : 0 ≤ Real.log (engelsmaMaynardRadius alpha N) :=
      hLN.le
    have hBdirect : 0 ≤ (smallKCandidateBound : ℝ) :=
      smallKCandidateBound_nonneg
    unfold E maynardS2CoordinateOneSquarePerturbationEnvelope
    rw [← hSeq]
    positivity
  have hratio0 : 0 ≤ E / (SS ^ 2 * LL ^ 2) := by positivity
  have hsum'' :
      (∑ r ∈ (maynardDivisorTupleSupport BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)).filter
          (fun r => r m = 1),
        maynardS2CoordinateOneSquarePerturbationEnvelope
          BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
          (tripleLogCutoff (N - 1)) m smallKCandidateBound /
          |∏ h : BoundedGaps.engelsmaTuple,
            (maynardS2G (r h) : ℝ)|) /
        (Q N) ^ 106 = (E * T) / (Q N) ^ 106 := by
    rw [show engelsmaMaynardModulus N =
      primorial (tripleLogCutoff (N - 1)) by rfl]
    rw [hsum']
  rw [hsum'']
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hE0 hT0) (by positivity))]
  rw [hratio]
  have hmul := mul_le_mul_of_nonneg_left hmassN hratio0
  simpa [SS, LL, S, L, E, T, mul_comm] using hmul

theorem tendsto_normalizedEngelsmaS2CoordinateOneYDiagonal_sub_fiberSquareDiagonal_zero
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun N : ℕ =>
      (engelsmaMaynardS2CoordinateOneYDiagonal alpha N m -
        engelsmaMaynardS2CoordinateOneFiberSquareDiagonal alpha N m) /
      (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
        Real.log (engelsmaMaynardRadius alpha N)) ^ 106)
      atTop (nhds 0) := by
  have henv :=
    tendsto_engelsmaS2CoordinateOneSquarePerturbation_div_squareScale_zero
      halpha m
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun N => abs_nonneg _)) ?_ henv
  filter_upwards [eventually_engelsmaMaynardCrossBound_conditions halpha,
      (tendsto_log_engelsmaMaynardRadius_atTop halpha).eventually
        (eventually_gt_atTop 0)] with N hC hL
  have hS := preSieveSingularSeries_pos (tripleLogCutoff (N - 1))
  have hden : 0 <
      (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
        Real.log (engelsmaMaynardRadius alpha N)) ^ 106 :=
    pow_pos (mul_pos hS hL) _
  rw [abs_div, abs_of_pos hden]
  exact div_le_div_of_nonneg_right
    (abs_engelsmaMaynardS2CoordinateOneYDiagonal_sub_fiberSquareDiagonal_le_log
      N m hC.2.1 hC.2.2) hden.le

end BoundedGaps.Maynard
