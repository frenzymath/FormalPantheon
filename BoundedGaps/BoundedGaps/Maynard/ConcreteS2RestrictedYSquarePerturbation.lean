import BoundedGaps.Maynard.ConcreteS2ReciprocalGCoordinateOneMass
import BoundedGaps.Maynard.ConcreteS2CoordinateOneSquareBridge

noncomputable section

namespace BoundedGaps.Maynard

open Filter
open scoped BigOperators

def normalizedEngelsmaS2CoordinateOneSquarePerturbation
    (alpha : ℝ) (N : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  (∑ r ∈ (maynardDivisorTupleSupport BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N)).filter (fun r => r m = 1),
    maynardS2CoordinateOneSquarePerturbationEnvelope
      BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
      (tripleLogCutoff (N - 1)) m smallKCandidateBound /
      |∏ h : BoundedGaps.engelsmaTuple,
        (maynardS2G (r h) : ℝ)|) /
    ((preSieveSingularSeries (tripleLogCutoff (N - 1)) *
        Real.log (engelsmaMaynardRadius alpha N)) ^
      (Finset.univ.erase m).card *
      Real.log (engelsmaMaynardRadius alpha N) ^ 2)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem tendsto_engelsmaS2CoordinateOneSquarePerturbationEnvelope_div_log_sq_zero
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun N : ℕ =>
      maynardS2CoordinateOneSquarePerturbationEnvelope
        BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
        (tripleLogCutoff (N - 1)) m smallKCandidateBound /
        Real.log (engelsmaMaynardRadius alpha N) ^ 2)
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
    change Tendsto (fun N : ℕ =>
      (tripleLogCutoff (N - 1) : ℝ)) atTop atTop
    exact tendsto_natCast_atTop_atTop.comp tendsto_shifted_tripleLogCutoff
  have hinvD : Tendsto (fun N => (1 : ℝ) / D N) atTop (nhds 0) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (nhds 1)).div_atTop hD
    simpa [one_div] using h
  have hterm : Tendsto (fun N => 8 * Real.exp 8 / D N)
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinvD.const_mul (8 * Real.exp 8)
  have hpow : Tendsto (fun N =>
      (1 + 8 * Real.exp 8 / D N) ^ ((Finset.univ.erase m).card - 1))
      atTop (nhds 1) := by
    simpa [add_comm] using (hterm.add_const 1).pow
      ((Finset.univ.erase m).card - 1)
  have hA : Tendsto A atTop (nhds 0) := by
    have hfirst : Tendsto (fun N => 8 / D N) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using hinvD.const_mul 8
    have hsecond : Tendsto (fun N =>
        (8 * Real.exp 8 / D N) *
          (1 + 8 * Real.exp 8 / D N) ^
            ((Finset.univ.erase m).card - 1)) atTop (nhds 0) := by
      simpa using hterm.mul hpow
    simpa [A] using hfirst.add hsecond
  have hsmallA : ∀ᶠ N : ℕ in atTop, 0 ≤ A N ∧ A N ≤ 1 := by
    filter_upwards [hA.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos),
      hD.eventually (eventually_gt_atTop 0)] with N hN hDN
    have hnonneg : 0 ≤ A N := by
      dsimp [A]
      positivity
    have hle : A N ≤ 1 := by
      exact le_of_lt (by simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hN)
    exact ⟨hnonneg, hle⟩
  have hLone : ∀ᶠ N : ℕ in atTop, 1 ≤ L N :=
    hL.eventually (eventually_ge_atTop 1)
  have hWL := eventually_engelsmaMaynardCrossBound_conditions halpha
  have hbound : ∀ᶠ N : ℕ in atTop,
      (0 ≤ maynardS2CoordinateOneSquarePerturbationEnvelope
          BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
          (tripleLogCutoff (N - 1)) m smallKCandidateBound) ∧
      ((maynardS2CoordinateOneSquarePerturbationEnvelope
          BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
          (tripleLogCutoff (N - 1)) m smallKCandidateBound) /
        L N ^ 2 ≤
        (512 * B ^ 2 * k * (1 + k)) * A N) := by
    filter_upwards [hsmallA, hLone, hWL] with N ⟨hA0, hA1⟩ hL1 hcond
    let R := engelsmaMaynardRadius alpha N
    let DD := tripleLogCutoff (N - 1)
    let SS := preSieveSingularSeries DD
    let LL := L N
    let MM := preSievedCoordinateInvTotientMass (primorial DD) R
    let AA := A N
    have hR : 1 < R := by
      have hlog : 0 < Real.log (R : ℝ) := by simpa [R, LL] using
        (lt_of_lt_of_le zero_lt_one hL1)
      exact_mod_cast (Real.log_pos_iff (by positivity)).mp hlog
    have hDpos : (0 : ℝ) < DD := by
      exact_mod_cast (show 0 < DD by
        simpa [DD] using hcond.2.1)
    have hS0 : 0 ≤ SS := (preSieveSingularSeries_pos DD).le
    have hS1 : SS ≤ 1 := preSieveSingularSeries_le_one DD
    have hS_eq : SS = (Nat.totient (primorial DD) : ℝ) /
        (primorial DD : ℝ) := by
      simpa [SS] using preSieveSingularSeries_eq_totient_div DD
    have hpre : MM ≤ squarefreeCoprimeInvTotientMean (primorial DD) R := by
      simpa [MM, preSievedCoordinateInvTotientMass] using
        preSievedCoordinateInvTotientSum_le (primorial DD) R
    have hmean := squarefreeCoprimeInvTotientMean_le_log
      (W := primorial DD) (Q := R) (primorial_pos DD) (by
        simpa [R, DD, engelsmaMaynardModulus] using hcond.2.2)
    have hM : MM ≤ 8 * SS * (1 + LL) := by
      simpa [MM, SS, LL, R, DD, preSieveSingularSeries_eq_totient_div] using
        hpre.trans hmean
    have hM' : MM ≤ 16 * LL := by
      calc
        MM ≤ 8 * SS * (1 + LL) := hM
        _ ≤ 8 * 1 * (1 + LL) := by
          gcongr
        _ ≤ 16 * LL := by nlinarith
    have hB : 0 ≤ B := by
      simpa [B] using smallKCandidateBound_nonneg
    have hk : 0 ≤ k := by positivity
    have hAA0 : 0 ≤ AA := by
      simpa [AA] using hA0
    have hAA1 : AA ≤ 1 := by
      simpa [AA] using hA1
    have hMM0 : 0 ≤ MM := by
      unfold MM preSievedCoordinateInvTotientMass
      positivity
    have hnonneg : 0 ≤
        maynardS2CoordinateOneSquarePerturbationEnvelope
          BoundedGaps.engelsmaTuple R DD m B := by
      unfold maynardS2CoordinateOneSquarePerturbationEnvelope
      rw [← hS_eq]
      positivity
    have hfirst : B * MM + B * k * (8 * SS * (1 + LL)) * AA ≤
        16 * B * (1 + k) * LL := by
      have hterm : B * k * (8 * SS * (1 + LL)) * AA ≤
          16 * B * k * LL := by
        have hbase : 8 * SS * (1 + LL) ≤ 16 * LL := by nlinarith
        have hBk : 0 ≤ B * k := mul_nonneg hB hk
        have hX : 0 ≤ 8 * SS * (1 + LL) := by positivity
        calc
          B * k * (8 * SS * (1 + LL)) * AA ≤
              B * k * (8 * SS * (1 + LL)) := by
                simpa only [mul_one] using
                  mul_le_mul_of_nonneg_left hAA1 (mul_nonneg hBk hX)
          _ ≤ B * k * (16 * LL) := by
            exact mul_le_mul_of_nonneg_left hbase hBk
          _ = 16 * B * k * LL := by ring
      calc
        B * MM + B * k * (8 * SS * (1 + LL)) * AA ≤
            16 * B * LL + 16 * B * k * LL :=
          add_le_add
            (by
              have h := mul_le_mul_of_nonneg_left hM' hB
              simpa [mul_assoc, mul_comm, mul_left_comm] using h) hterm
        _ = 16 * B * (1 + k) * LL := by ring
    have hsecond : B * k * (8 * SS * (1 + LL)) * AA ≤
        16 * B * k * LL * AA := by
      have hbase : 8 * SS * (1 + LL) ≤ 16 * LL := by nlinarith
      have hBk : 0 ≤ B * k := mul_nonneg hB hk
      calc
        B * k * (8 * SS * (1 + LL)) * AA ≤
            B * k * (16 * LL) * AA := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hbase hBk) hAA0
        _ = 16 * B * k * LL * AA := by ring
    have hcalc :
        2 * (B * MM + B * k * (8 * SS * (1 + LL)) * AA) *
            (B * k * (8 * SS * (1 + LL)) * AA) ≤
          512 * B ^ 2 * k * (1 + k) * LL ^ 2 * AA := by
      calc
        2 * (B * MM + B * k * (8 * SS * (1 + LL)) * AA) *
              (B * k * (8 * SS * (1 + LL)) * AA) ≤
            2 * (16 * B * (1 + k) * LL) *
              (16 * B * k * LL * AA) := by
                exact mul_le_mul
                  (mul_le_mul_of_nonneg_left hfirst (by positivity))
                  hsecond (by positivity) (by positivity)
        _ = 512 * B ^ 2 * k * (1 + k) * LL ^ 2 * AA := by ring
    have hcalc' :
        maynardS2CoordinateOneSquarePerturbationEnvelope
          BoundedGaps.engelsmaTuple R DD m B ≤
        512 * B ^ 2 * k * (1 + k) * LL ^ 2 * AA := by
      unfold maynardS2CoordinateOneSquarePerturbationEnvelope
      rw [← hS_eq]
      simpa [B, k, L, A, D, S, R, DD, SS, LL, MM, AA] using hcalc
    constructor
    · simpa [B] using hnonneg
    · apply (div_le_iff₀ (by positivity : (0 : ℝ) < LL ^ 2)).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hcalc'
  have hzero : Tendsto (fun N : ℕ =>
      (512 * B ^ 2 * k * (1 + k)) * A N) atTop (nhds 0) := by
    simpa using hA.const_mul (512 * B ^ 2 * k * (1 + k))
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun N => abs_nonneg _)) ?_ hzero
  filter_upwards [hbound, hL.eventually (eventually_gt_atTop 0)] with
      N ⟨hnonneg, hN⟩ hLN
  rw [abs_of_nonneg (div_nonneg hnonneg (sq_nonneg _))]
  exact hN

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
theorem tendsto_normalizedEngelsmaS2CoordinateOneSquarePerturbation_zero
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaS2CoordinateOneSquarePerturbation alpha N m)
      atTop (nhds 0) := by
  let H := engelsmaOffFaceFinset m
  let k := Fintype.card H
  let L : ℕ → ℝ := fun N =>
    Real.log (engelsmaMaynardRadius alpha N)
  let S : ℕ → ℝ := fun N =>
    preSieveSingularSeries (tripleLogCutoff (N - 1))
  let M : ℕ → ℝ := fun N =>
    maynardS2ReciprocalGSquarefreeMean
      (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N)
  let Q : ℕ → ℝ := fun N => S N * L N
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
  have hprod : Tendsto (fun N : ℕ =>
      ∏ h : H, M N / Q N) atTop (nhds 1) := by
    have hp : Tendsto (fun N : ℕ =>
        ∏ h : H, M N / Q N) atTop
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
    have hdist : |(∏ h : H, M N) / (Q N) ^ k - 1| < 1 := by
      simpa [Real.dist_eq] using hN
    linarith [le_abs_self ((∏ h : H, M N) / (Q N) ^ k - 1)]
  have hmassLe : ∀ᶠ N : ℕ in atTop,
      engelsmaS2CoordinateOneReciprocalGMass
          (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m /
        (Q N) ^ k ≤ 2 := by
    filter_upwards [hboxLe, hQ] with N hboxN hQN
    have hmass := engelsmaS2CoordinateOneReciprocalGMass_eq_offFace
      (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m
    have hmassBound := engelsmaS2OffFaceReciprocalGMass_le_box
      (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m
    rw [hmass]
    have hQk : 0 ≤ (Q N) ^ k := by positivity
    exact (div_le_div_of_nonneg_right hmassBound
      hQk).trans (by simpa [Q, S, L, M, H, k, engelsmaMaynardModulus]
        using hboxN)
  have hmassNonneg : ∀ᶠ N : ℕ in atTop,
      0 ≤ engelsmaS2CoordinateOneReciprocalGMass
          (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m := by
    filter_upwards [] with N
    unfold engelsmaS2CoordinateOneReciprocalGMass
    exact Finset.sum_nonneg (fun r hr => by positivity)
  have hDpos : ∀ᶠ N : ℕ in atTop,
      0 < tripleLogCutoff (N - 1) := by
    filter_upwards [eventually_engelsmaMaynardCrossBound_conditions halpha]
      with N hN
    exact hN.2.1
  have henv :=
    tendsto_engelsmaS2CoordinateOneSquarePerturbationEnvelope_div_log_sq_zero
      halpha m
  have htwo : Tendsto (fun N : ℕ =>
      2 * (maynardS2CoordinateOneSquarePerturbationEnvelope
        BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
        (tripleLogCutoff (N - 1)) m smallKCandidateBound /
        L N ^ 2)) atTop (nhds 0) := by
    simpa [L] using henv.const_mul 2
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun N => abs_nonneg _)) ?_ htwo
  filter_upwards [hmassLe, hmassNonneg, hQ, hL.eventually
      (eventually_gt_atTop 0), hDpos, hS] with
      N hmassN hmass0 hQN hLN hDN hSN
  have hDNreal : (0 : ℝ) < tripleLogCutoff (N - 1) := by
    exact_mod_cast hDN
  let E := maynardS2CoordinateOneSquarePerturbationEnvelope
    BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
    (tripleLogCutoff (N - 1)) m smallKCandidateBound
  let T := engelsmaS2CoordinateOneReciprocalGMass
    (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m
  have hSqrt : 0 < (Q N) ^ k := by positivity
  have hE0 : 0 ≤ E := by
    have hM0 : 0 ≤ preSievedCoordinateInvTotientMass
        (primorial (tripleLogCutoff (N - 1)))
        (engelsmaMaynardRadius alpha N) := by
      unfold preSievedCoordinateInvTotientMass
      positivity
    have hSeq : S N = (Nat.totient
        (primorial (tripleLogCutoff (N - 1))) : ℝ) /
        (primorial (tripleLogCutoff (N - 1)) : ℝ) := by
      simpa [S] using preSieveSingularSeries_eq_totient_div
        (tripleLogCutoff (N - 1))
    unfold E maynardS2CoordinateOneSquarePerturbationEnvelope
    rw [← hSeq]
    have hB0 : 0 ≤ smallKCandidateBound := smallKCandidateBound_nonneg
    have hK0 : 0 ≤ ((Finset.univ.erase m).card : ℝ) := by positivity
    have hA0' : 0 ≤
        8 / (tripleLogCutoff (N - 1) : ℝ) +
          (8 * Real.exp 8 / (tripleLogCutoff (N - 1) : ℝ)) *
            (1 + 8 * Real.exp 8 / (tripleLogCutoff (N - 1) : ℝ)) ^
              ((Finset.univ.erase m).card - 1) := by
      exact add_nonneg
        (div_nonneg (by positivity) hDNreal.le)
        (mul_nonneg (div_nonneg (by positivity) hDNreal.le)
          (pow_nonneg (by positivity) _))
    have hleft : 0 ≤
        smallKCandidateBound *
            preSievedCoordinateInvTotientMass
              (primorial (tripleLogCutoff (N - 1)))
              (engelsmaMaynardRadius alpha N) +
          smallKCandidateBound * ((Finset.univ.erase m).card : ℝ) *
            (8 * S N * (1 + L N)) *
            (8 / (tripleLogCutoff (N - 1) : ℝ) +
              (8 * Real.exp 8 / (tripleLogCutoff (N - 1) : ℝ)) *
                (1 + 8 * Real.exp 8 / (tripleLogCutoff (N - 1) : ℝ)) ^
                  ((Finset.univ.erase m).card - 1)) := by
      have hfactor : 0 ≤ 8 * S N * (1 + L N) := by positivity
      have hsecond : 0 ≤
          smallKCandidateBound * ((Finset.univ.erase m).card : ℝ) *
            (8 * S N * (1 + L N)) *
            (8 / (tripleLogCutoff (N - 1) : ℝ) +
              (8 * Real.exp 8 / (tripleLogCutoff (N - 1) : ℝ)) *
                (1 + 8 * Real.exp 8 / (tripleLogCutoff (N - 1) : ℝ)) ^
                  ((Finset.univ.erase m).card - 1)) := by
        exact mul_nonneg
          (mul_nonneg (mul_nonneg hB0 hK0) hfactor) hA0'
      exact add_nonneg (mul_nonneg hB0 hM0) hsecond
    have hright : 0 ≤
        smallKCandidateBound * ((Finset.univ.erase m).card : ℝ) *
          (8 * S N * (1 + L N)) *
          (8 / (tripleLogCutoff (N - 1) : ℝ) +
            (8 * Real.exp 8 / (tripleLogCutoff (N - 1) : ℝ)) *
              (1 + 8 * Real.exp 8 / (tripleLogCutoff (N - 1) : ℝ)) ^
                ((Finset.univ.erase m).card - 1)) := by
      have hfactor : 0 ≤ 8 * S N * (1 + L N) := by positivity
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hB0 hK0) hfactor) hA0'
    exact mul_nonneg (mul_nonneg (by norm_num) hleft) hright
  have hratio0 : 0 ≤ T / (Q N) ^ k :=
    div_nonneg hmass0 hSqrt.le
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
  have hident :
      (E * T) / ((Q N) ^ k * L N ^ 2) =
        (E / L N ^ 2) * (T / (Q N) ^ k) := by
    field_simp [ne_of_gt hSqrt, ne_of_gt (sq_pos_of_pos hLN)]
  have hbound :
      0 ≤ (E * T) / ((Q N) ^ k * L N ^ 2) ∧
      (E * T) / ((Q N) ^ k * L N ^ 2) ≤
        2 * (E / L N ^ 2) := by
    rw [hident]
    constructor
    · have hEL0 : 0 ≤ E / L N ^ 2 := div_nonneg hE0 (sq_nonneg _)
      exact mul_nonneg hEL0 hratio0
    · have hEL0 : 0 ≤ E / L N ^ 2 := div_nonneg hE0 (sq_nonneg _)
      calc
        (E / L N ^ 2) * (T / (Q N) ^ k) ≤
            (E / L N ^ 2) * 2 :=
          mul_le_mul_of_nonneg_left hmassN hEL0
        _ = 2 * (E / L N ^ 2) := by ring
  have hk : ((Finset.univ : Finset BoundedGaps.engelsmaTuple).erase m).card = k := by
    simp [k, H, engelsmaOffFaceFinset,
      Finset.card_erase_of_mem m.property, BoundedGaps.engelsmaTuple_card]
  have hk' : BoundedGaps.engelsmaTuple.card - 1 = k := by
    simpa [Finset.card_erase_of_mem m.property,
      BoundedGaps.engelsmaTuple_card] using hk
  have hsum' :
      (∑ r ∈ (maynardDivisorTupleSupport BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha N)
          (primorial (tripleLogCutoff (N - 1)))).filter (fun r => r m = 1),
        E / |∏ h : BoundedGaps.engelsmaTuple,
          (maynardS2G (r h) : ℝ)|) = E * T := by
    simpa [engelsmaS2CoordinateFiberCoordinateOneSupport] using hsum
  rw [show normalizedEngelsmaS2CoordinateOneSquarePerturbation alpha N m =
      (E * T) / ((Q N) ^ k * L N ^ 2) by
        unfold normalizedEngelsmaS2CoordinateOneSquarePerturbation
        simp only [engelsmaMaynardModulus]
        rw [hsum']
        simp [Q, S, L, hk']]
  rw [abs_of_nonneg hbound.1]
  exact hbound.2

end BoundedGaps.Maynard
