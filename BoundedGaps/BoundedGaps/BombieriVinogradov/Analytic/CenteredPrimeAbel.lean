import BoundedGaps.BombieriVinogradov.Analytic.CenteredPrimePowerRemoval
import Mathlib.Analysis.SpecialFunctions.Log.InvLog

/-!
# Centered prime-counting Abel bridge

This file applies finite Abel summation directly to the signed prime-log
coefficient centered at the global prime count. The negative derivative of
`1 / log` produces the positive integral kernel. This corrects the sign in
the unnumbered partial-summation display on `AkbaryHambrook2013v2`, printed
p. 26. Semantic review: `SEM-573`.
-/

namespace BoundedGaps.Maynard

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- The centered theta floor-step integrand is genuinely interval-integrable
on every natural source interval. -/
theorem intervalIntegrable_centeredThetaProgressionError_div_id_mul_log_sq
    {x q a : ℕ} (hx : 2 ≤ x) :
    IntervalIntegrable
      (fun t : ℝ ↦
        centeredThetaProgressionError ⌊t⌋₊ q a /
          (t * Real.log t ^ 2))
      MeasureTheory.volume (2 : ℝ) (x : ℝ) := by
  classical
  let progressionCoefficient : ℕ → ℝ := fun n ↦
    Set.indicator {n : ℕ | n.Prime ∧ n % q = a % q}
        (fun n ↦ Real.log (n : ℝ)) n
  let globalCoefficient : ℕ → ℝ := fun n ↦
    Set.indicator {n : ℕ | n.Prime} (fun n ↦ Real.log (n : ℝ)) n
  let c : ℕ → ℝ := fun n ↦
    progressionCoefficient n - (q.totient : ℝ)⁻¹ * globalCoefficient n
  have hProgressionSum (m : ℕ) :
      (∑ n ∈ Finset.Icc 0 m, progressionCoefficient n) =
        thetaProgressionSum m q a := by
    rw [thetaProgressionSum, Nat.primesLE_eq_filter_Icc_zero]
    simp [progressionCoefficient, Set.indicator_apply, Finset.sum_filter,
      Finset.filter_filter, and_comm]
  have hGlobalSum (m : ℕ) :
      (∑ n ∈ Finset.Icc 0 m, globalCoefficient n) =
        Chebyshev.theta (m : ℝ) := by
    rw [Chebyshev.theta_eq_sum_Icc]
    simp [globalCoefficient, Set.indicator_apply, Finset.sum_filter]
  have hCenteredSum (m : ℕ) :
      (∑ n ∈ Finset.Icc 0 m, c n) =
        centeredThetaProgressionError m q a := by
    simp only [c, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hProgressionSum, hGlobalSum, centeredThetaProgressionError]
    simp only [div_eq_mul_inv]
    ring
  have hxReal : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hDerivIntegrable : IntegrableOn
      (deriv fun t : ℝ ↦ (Real.log t)⁻¹) (Set.Icc (2 : ℝ) (x : ℝ)) := by
    refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one ?_ ?_)
      · linarith [ht.1]
      · linarith [ht.1]
    exact ContinuousAt.continuousWithinAt <| by fun_prop
  have hProductIntegrable : IntegrableOn
      (fun t : ℝ ↦
        deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t *
          ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n)
      (Set.Icc (2 : ℝ) (x : ℝ)) :=
    integrableOn_mul_sum_Icc c (a := (2 : ℝ)) (b := (x : ℝ))
      (m := 0) (by norm_num) hDerivIntegrable
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxReal]
  apply hProductIntegrable.neg.congr_fun _ measurableSet_Icc
  intro t ht
  change -(deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t *
      ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) = _
  rw [hCenteredSum, Real.deriv_inv_log_apply]
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
  field_simp

/-- Finite Abel summation for the prime-counting error centered by the total
prime count. The integral has a plus sign because the inverse-log derivative
is negative. -/
theorem
    primeCountUpTo_sub_primeCountTotal_div_totient_eq_centeredThetaAbel
    {x q a : ℕ} (hx : 2 ≤ x) :
    (primeCountUpTo x q a : ℝ) -
        (primeCountTotal x : ℝ) / (q.totient : ℝ) =
      centeredThetaProgressionError x q a / Real.log (x : ℝ) +
        ∫ t in (2 : ℝ)..(x : ℝ),
          centeredThetaProgressionError ⌊t⌋₊ q a /
            (t * Real.log t ^ 2) := by
  classical
  let progressionCoefficient : ℕ → ℝ := fun n ↦
    Set.indicator {n : ℕ | n.Prime ∧ n % q = a % q}
        (fun n ↦ Real.log (n : ℝ)) n
  let globalCoefficient : ℕ → ℝ := fun n ↦
    Set.indicator {n : ℕ | n.Prime} (fun n ↦ Real.log (n : ℝ)) n
  let c : ℕ → ℝ := fun n ↦
    progressionCoefficient n - (q.totient : ℝ)⁻¹ * globalCoefficient n
  have hProgressionSum (m : ℕ) :
      (∑ n ∈ Finset.Icc 0 m, progressionCoefficient n) =
        thetaProgressionSum m q a := by
    rw [thetaProgressionSum, Nat.primesLE_eq_filter_Icc_zero]
    simp [progressionCoefficient, Set.indicator_apply, Finset.sum_filter,
      Finset.filter_filter, and_comm]
  have hGlobalSum (m : ℕ) :
      (∑ n ∈ Finset.Icc 0 m, globalCoefficient n) =
        Chebyshev.theta (m : ℝ) := by
    rw [Chebyshev.theta_eq_sum_Icc]
    simp [globalCoefficient, Set.indicator_apply, Finset.sum_filter]
  have hCenteredSum (m : ℕ) :
      (∑ n ∈ Finset.Icc 0 m, c n) =
        centeredThetaProgressionError m q a := by
    simp only [c, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hProgressionSum, hGlobalSum, centeredThetaProgressionError]
    simp only [div_eq_mul_inv]
    ring
  have hProgressionWeighted :
      (∑ n ∈ Finset.Icc 0 x,
        (Real.log (n : ℝ))⁻¹ * progressionCoefficient n) =
          (primeCountUpTo x q a : ℝ) := by
    rw [primeCountUpTo, Finset.card_eq_sum_ones,
      Nat.range_succ_eq_Icc_zero, Finset.sum_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro n _hn
    split_ifs with h
    · have hlog : Real.log (n : ℝ) ≠ 0 := h.1.log_ne_zero
      simp [progressionCoefficient, h, hlog]
    · simp [progressionCoefficient, h]
  have hGlobalWeighted :
      (∑ n ∈ Finset.Icc 0 x,
        (Real.log (n : ℝ))⁻¹ * globalCoefficient n) =
          (primeCountTotal x : ℝ) := by
    rw [primeCountTotal, ← Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_eq_filter_Icc_zero, Finset.card_eq_sum_ones,
      Finset.sum_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro n _hn
    split_ifs with h
    · have hlog : Real.log (n : ℝ) ≠ 0 := h.log_ne_zero
      simp [globalCoefficient, h, hlog]
    · simp [globalCoefficient, h]
  have hWeighted :
      (∑ n ∈ Finset.Icc 0 x, (Real.log (n : ℝ))⁻¹ * c n) =
        (primeCountUpTo x q a : ℝ) -
          (primeCountTotal x : ℝ) / (q.totient : ℝ) := by
    calc
      (∑ n ∈ Finset.Icc 0 x, (Real.log (n : ℝ))⁻¹ * c n) =
          (∑ n ∈ Finset.Icc 0 x,
              (Real.log (n : ℝ))⁻¹ * progressionCoefficient n) -
            (q.totient : ℝ)⁻¹ *
              ∑ n ∈ Finset.Icc 0 x,
                (Real.log (n : ℝ))⁻¹ * globalCoefficient n := by
        simp only [c, mul_sub, Finset.sum_sub_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        ring
      _ = (primeCountUpTo x q a : ℝ) -
          (primeCountTotal x : ℝ) / (q.totient : ℝ) := by
        rw [hProgressionWeighted, hGlobalWeighted]
        simp only [div_eq_mul_inv]
        ring
  have hxReal : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hDifferentiable : ∀ t ∈ Set.Icc (2 : ℝ) (x : ℝ),
      DifferentiableAt ℝ (fun u : ℝ ↦ (Real.log u)⁻¹) t := by
    intro t ht
    exact Real.differentiableAt_inv_log (by linarith [ht.1])
      (by linarith [ht.1]) (by linarith [ht.1])
  have hDerivIntegrable : IntegrableOn
      (deriv fun t : ℝ ↦ (Real.log t)⁻¹) (Set.Icc (2 : ℝ) (x : ℝ)) := by
    refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one ?_ ?_)
      · linarith [ht.1]
      · linarith [ht.1]
    exact ContinuousAt.continuousWithinAt <| by fun_prop
  have hAbel := sum_mul_eq_sub_integral_mul₁ c
    (f := fun t : ℝ ↦ (Real.log t)⁻¹) (by
      norm_num [c, progressionCoefficient, globalCoefficient,
        Set.indicator_apply]) (by
      norm_num [c, progressionCoefficient, globalCoefficient,
        Set.indicator_apply]) (x : ℝ) hDifferentiable hDerivIntegrable
  rw [← intervalIntegral.integral_of_le hxReal] at hAbel
  have hIntegral :
      (∫ t in (2 : ℝ)..(x : ℝ),
          deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t *
            ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) =
        -(∫ t in (2 : ℝ)..(x : ℝ),
          centeredThetaProgressionError ⌊t⌋₊ q a /
            (t * Real.log t ^ 2)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc (2 : ℝ) (x : ℝ) := by
      simpa [Set.uIcc_of_le hxReal] using ht
    change deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t *
        (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) =
      -(centeredThetaProgressionError ⌊t⌋₊ q a /
        (t * Real.log t ^ 2))
    rw [hCenteredSum, Real.deriv_inv_log_apply]
    have ht0 : t ≠ 0 := by linarith [htIcc.1]
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [htIcc.1])
        (by linarith [htIcc.1])
    field_simp
  rw [Nat.floor_natCast, hWeighted, hCenteredSum, hIntegral] at hAbel
  calc
    (primeCountUpTo x q a : ℝ) -
        (primeCountTotal x : ℝ) / (q.totient : ℝ) =
      (Real.log (x : ℝ))⁻¹ * centeredThetaProgressionError x q a -
        -(∫ t in (2 : ℝ)..(x : ℝ),
          centeredThetaProgressionError ⌊t⌋₊ q a /
            (t * Real.log t ^ 2)) := hAbel
    _ = centeredThetaProgressionError x q a / Real.log (x : ℝ) +
        ∫ t in (2 : ℝ)..(x : ℝ),
          centeredThetaProgressionError ⌊t⌋₊ q a /
            (t * Real.log t ^ 2) := by
      simp only [div_eq_mul_inv]
      ring

/-- The total mass of the endpoint term and positive Abel kernel is exactly
`1 / log 2`. -/
theorem primeCountingAbelKernel_mass {x : ℕ} (hx : 2 ≤ x) :
    (Real.log (x : ℝ))⁻¹ +
        ∫ t in (2 : ℝ)..(x : ℝ),
          (t * Real.log t ^ 2)⁻¹ =
      (Real.log 2)⁻¹ := by
  have hxReal : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hDifferentiable : ∀ t ∈ Set.uIcc (2 : ℝ) (x : ℝ),
      DifferentiableAt ℝ (fun u : ℝ ↦ (Real.log u)⁻¹) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc (2 : ℝ) (x : ℝ) := by
      simpa [Set.uIcc_of_le hxReal] using ht
    exact Real.differentiableAt_inv_log (by linarith [htIcc.1])
      (by linarith [htIcc.1]) (by linarith [htIcc.1])
  have hDerivIntegrable : IntervalIntegrable
      (deriv fun t : ℝ ↦ (Real.log t)⁻¹) MeasureTheory.volume
      (2 : ℝ) (x : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxReal]
    refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one ?_ ?_)
      · linarith [ht.1]
      · linarith [ht.1]
    exact ContinuousAt.continuousWithinAt <| by fun_prop
  have hFundamental := intervalIntegral.integral_deriv_eq_sub
    hDifferentiable hDerivIntegrable
  have hDerivativeIntegral :
      (∫ t in (2 : ℝ)..(x : ℝ),
          deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t) =
        -(∫ t in (2 : ℝ)..(x : ℝ),
          (t * Real.log t ^ 2)⁻¹) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc (2 : ℝ) (x : ℝ) := by
      simpa [Set.uIcc_of_le hxReal] using ht
    rw [Real.deriv_inv_log_apply]
    have ht0 : t ≠ 0 := by linarith [htIcc.1]
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [htIcc.1])
        (by linarith [htIcc.1])
    field_simp
  rw [hDerivativeIntegral] at hFundamental
  linarith

/-- Abel summation transfers the endpoint-uniform centered theta maximum to
the public prime-counting maximum with the exact kernel mass. -/
theorem
    maxProgressionDiscrepancy_le_inv_log_two_mul_maxCenteredThetaUpTo
    {x q : ℕ} (hx : 2 ≤ x) (hq : 1 ≤ q) :
    maxProgressionDiscrepancy x q ≤
      (Real.log 2)⁻¹ *
        maxCenteredThetaProgressionDiscrepancyUpTo x q := by
  classical
  have hqpos : 0 < q := by omega
  rw [maxProgressionDiscrepancy, dif_pos hqpos]
  apply Finset.sup'_le
  intro a ha
  rw [progressionDiscrepancy,
    primeCountUpTo_sub_primeCountTotal_div_totient_eq_centeredThetaAbel hx]
  let M := maxCenteredThetaProgressionDiscrepancyUpTo x q
  change |centeredThetaProgressionError x q a / Real.log (x : ℝ) +
      ∫ t in (2 : ℝ)..(x : ℝ),
        centeredThetaProgressionError ⌊t⌋₊ q a /
          (t * Real.log t ^ 2)| ≤ (Real.log 2)⁻¹ * M
  have hError (y : ℕ) (hy : y ∈ Finset.Icc 2 x) :
      |centeredThetaProgressionError y q a| ≤ M := by
    dsimp only [M]
    rw [maxCenteredThetaProgressionDiscrepancyUpTo_eq_sup_endpoint_residues
      hx hqpos]
    exact Finset.le_sup'_of_le
      (fun z ↦
        (coprimeResidues q).sup' (coprimeResidues_nonempty hqpos) (fun b ↦
          |thetaProgressionSum z q b -
            Chebyshev.theta (z : ℝ) / (q.totient : ℝ)|)) hy
      (Finset.le_sup'_of_le
        (fun b ↦ |thetaProgressionSum y q b -
          Chebyshev.theta (y : ℝ) / (q.totient : ℝ)|) ha (by
            simp only [centeredThetaProgressionError]
            exact le_rfl))
  have hxMember : x ∈ Finset.Icc 2 x := Finset.mem_Icc.mpr ⟨hx, le_rfl⟩
  have hxOne : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (show 1 < x by omega)
  have hInvLogX : 0 ≤ (Real.log (x : ℝ))⁻¹ :=
    (inv_pos.mpr (Real.log_pos hxOne)).le
  have hEndpoint :
      |centeredThetaProgressionError x q a / Real.log (x : ℝ)| ≤
        M * (Real.log (x : ℝ))⁻¹ := by
    rw [abs_div, abs_of_pos (Real.log_pos hxOne), div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hError x hxMember) hInvLogX
  have hxReal : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hDisplayed :=
    intervalIntegrable_centeredThetaProgressionError_div_id_mul_log_sq
      (q := q) (a := a) hx
  have hKernelIntegrable : IntervalIntegrable
      (fun t : ℝ ↦ (t * Real.log t ^ 2)⁻¹) MeasureTheory.volume
      (2 : ℝ) (x : ℝ) := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦
      ContinuousAt.continuousWithinAt ?_
    have htIcc : t ∈ Set.Icc (2 : ℝ) (x : ℝ) := by
      simpa [Set.uIcc_of_le hxReal] using ht
    have ht0 : t ≠ 0 := by linarith [htIcc.1]
    have hlog : Real.log t ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one ?_ ?_)
      · linarith [htIcc.1]
      · linarith [htIcc.1]
    have hdenom : t * Real.log t ^ 2 ≠ 0 := mul_ne_zero ht0 hlog
    fun_prop
  have hMajorant : IntervalIntegrable
      (fun t : ℝ ↦ M * (t * Real.log t ^ 2)⁻¹) MeasureTheory.volume
      (2 : ℝ) (x : ℝ) := hKernelIntegrable.const_mul M
  have hPointwise (t : ℝ) (ht : t ∈ Set.Icc (2 : ℝ) (x : ℝ)) :
      ‖centeredThetaProgressionError ⌊t⌋₊ q a /
          (t * Real.log t ^ 2)‖ ≤
        M * (t * Real.log t ^ 2)⁻¹ := by
    have htOne : (1 : ℝ) < t := by linarith [ht.1]
    have hlogPos : 0 < Real.log t := Real.log_pos htOne
    have hdenomPos : 0 < t * Real.log t ^ 2 :=
      mul_pos (by linarith [ht.1]) (sq_pos_of_pos hlogPos)
    have hFloor : ⌊t⌋₊ ∈ Finset.Icc 2 x := by
      refine Finset.mem_Icc.mpr ⟨Nat.le_floor ht.1, ?_⟩
      simpa using Nat.floor_le_floor ht.2
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hdenomPos, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hError ⌊t⌋₊ hFloor)
      (inv_nonneg.mpr hdenomPos.le)
  have hIntegral :
      |∫ t in (2 : ℝ)..(x : ℝ),
          centeredThetaProgressionError ⌊t⌋₊ q a /
            (t * Real.log t ^ 2)| ≤
        M * ∫ t in (2 : ℝ)..(x : ℝ),
          (t * Real.log t ^ 2)⁻¹ := by
    calc
      |∫ t in (2 : ℝ)..(x : ℝ),
          centeredThetaProgressionError ⌊t⌋₊ q a /
            (t * Real.log t ^ 2)| =
          ‖∫ t in (2 : ℝ)..(x : ℝ),
            centeredThetaProgressionError ⌊t⌋₊ q a /
              (t * Real.log t ^ 2)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ t in (2 : ℝ)..(x : ℝ),
          ‖centeredThetaProgressionError ⌊t⌋₊ q a /
            (t * Real.log t ^ 2)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hxReal
      _ ≤ ∫ t in (2 : ℝ)..(x : ℝ),
          M * (t * Real.log t ^ 2)⁻¹ :=
        intervalIntegral.integral_mono_on hxReal hDisplayed.norm hMajorant
          hPointwise
      _ = M * ∫ t in (2 : ℝ)..(x : ℝ),
          (t * Real.log t ^ 2)⁻¹ := by
        rw [intervalIntegral.integral_const_mul]
  calc
    |centeredThetaProgressionError x q a / Real.log (x : ℝ) +
        ∫ t in (2 : ℝ)..(x : ℝ),
          centeredThetaProgressionError ⌊t⌋₊ q a /
            (t * Real.log t ^ 2)| ≤
      |centeredThetaProgressionError x q a / Real.log (x : ℝ)| +
        |∫ t in (2 : ℝ)..(x : ℝ),
          centeredThetaProgressionError ⌊t⌋₊ q a /
            (t * Real.log t ^ 2)| := abs_add_le _ _
    _ ≤ M * (Real.log (x : ℝ))⁻¹ +
        M * ∫ t in (2 : ℝ)..(x : ℝ),
          (t * Real.log t ^ 2)⁻¹ := add_le_add hEndpoint hIntegral
    _ = M * ((Real.log (x : ℝ))⁻¹ +
        ∫ t in (2 : ℝ)..(x : ℝ),
          (t * Real.log t ^ 2)⁻¹) := by ring
    _ = M * (Real.log 2)⁻¹ := by rw [primeCountingAbelKernel_mass hx]
    _ = (Real.log 2)⁻¹ * M := by ring

/-- Sum the pointwise Abel transfer over the positive modulus range. -/
theorem
    sum_maxProgressionDiscrepancy_le_inv_log_two_mul_sum_maxCenteredThetaUpTo
    {x Q : ℕ} (hx : 2 ≤ x) :
    (∑ q ∈ Finset.Icc 1 Q,
      maxProgressionDiscrepancy x q) ≤
      (Real.log 2)⁻¹ *
        ∑ q ∈ Finset.Icc 1 Q,
          maxCenteredThetaProgressionDiscrepancyUpTo x q := by
  calc
    (∑ q ∈ Finset.Icc 1 Q, maxProgressionDiscrepancy x q) ≤
        ∑ q ∈ Finset.Icc 1 Q,
          (Real.log 2)⁻¹ *
            maxCenteredThetaProgressionDiscrepancyUpTo x q := by
      apply Finset.sum_le_sum
      intro q hq
      exact
        maxProgressionDiscrepancy_le_inv_log_two_mul_maxCenteredThetaUpTo
          hx (Finset.mem_Icc.mp hq).1
    _ = (Real.log 2)⁻¹ *
        ∑ q ∈ Finset.Icc 1 Q,
          maxCenteredThetaProgressionDiscrepancyUpTo x q := by
      rw [Finset.mul_sum]

end

end BoundedGaps.Maynard
