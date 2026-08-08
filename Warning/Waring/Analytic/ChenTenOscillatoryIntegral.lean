import Waring.Analytic.ChenSevenResidueIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Oscillatory decay for Chen's fifth-power kernel

This file proves the explicit van der Corput-style estimate used in the
outer part of the Lemma 10 major arcs.  The proof is integration by parts
after the scale `h = |z|^(-1/5)`; the zero frequency is intentionally
excluded.
-/

namespace Waring.Analytic

open MeasureTheory Set
open scoped Interval ComplexConjugate

noncomputable section

private def oscPhase (z t : Real) : Complex :=
  Complex.exp (Complex.I * ((2 * Real.pi * z * t ^ 5 : Real) : Complex))

private def oscAmplitude (z t : Real) : Real :=
  (10 * Real.pi * z)⁻¹ * t ^ (-4 : Int)

private def oscAmplitudeDeriv (z t : Real) : Real :=
  -4 * (10 * Real.pi * z)⁻¹ * t ^ (-5 : Int)

private def oscPhaseDeriv (z t : Real) : Complex :=
  Complex.I * ((10 * Real.pi * z * t ^ 4 : Real) : Complex) * oscPhase z t

private theorem hasDerivAt_oscAmplitude {z t : Real} (ht : t ≠ 0) :
    HasDerivAt (oscAmplitude z) (oscAmplitudeDeriv z t) t := by
  unfold oscAmplitude oscAmplitudeDeriv
  have h := HasDerivAt.const_smul ((10 * Real.pi * z)⁻¹)
    (hasDerivAt_zpow (-4 : Int) t (Or.inl ht))
  rw [Pi.smul_def] at h
  have hexp : (-4 : Int) - 1 = -5 := by norm_num
  have hcast : ((-4 : Int) : Real) = -4 := by norm_num
  rw [hexp, hcast] at h
  have heq : -4 * (10 * Real.pi * z)⁻¹ * t ^ (-5 : Int) =
      (10 * Real.pi * z)⁻¹ * ((-4 : Real) * t ^ (-5 : Int)) := by ring
  rw [heq]
  simpa only [smul_eq_mul] using h

private theorem hasDerivAt_oscPhase (z t : Real) :
    HasDerivAt (oscPhase z) (oscPhaseDeriv z t) t := by
  change HasDerivAt
    (fun y : Real =>
      Complex.exp (Complex.I * ((2 * Real.pi * z * y ^ 5 : Real) : Complex)))
    (Complex.I * ((10 * Real.pi * z * t ^ 4 : Real) : Complex) *
      Complex.exp (Complex.I * ((2 * Real.pi * z * t ^ 5 : Real) : Complex))) t
  have hr : HasDerivAt
      (fun y : Real => 2 * Real.pi * z * y ^ 5)
      (10 * Real.pi * z * t ^ 4) t := by
    have h := (hasDerivAt_pow 5 t).const_mul (2 * Real.pi * z)
    have hexp : (5 : Nat) - 1 = 4 := by norm_num
    rw [hexp] at h
    have hcast : ((5 : Nat) : Real) = 5 := by norm_num
    rw [hcast] at h
    have heq : 2 * Real.pi * z * (5 * t ^ 4) =
        10 * Real.pi * z * t ^ 4 := by ring
    rw [← heq]
    exact h
  have hc0 := Complex.ofRealCLM.hasFDerivAt.comp t hr.hasFDerivAt
  have hc : HasDerivAt
      (fun y : Real => ((2 * Real.pi * z * y ^ 5 : Real) : Complex))
      ((10 * Real.pi * z * t ^ 4 : Real) : Complex) t := by
    simpa [Function.comp_def, Complex.ofRealCLM_apply] using hc0.hasDerivAt
  have hexp := (hc.const_mul Complex.I).cexp
  have heq : Complex.I * ((10 * Real.pi * z * t ^ 4 : Real) : Complex) *
      Complex.exp (Complex.I * ((2 * Real.pi * z * t ^ 5 : Real) : Complex)) =
      Complex.exp (Complex.I * ((2 * Real.pi * z * t ^ 5 : Real) : Complex)) *
        (Complex.I * ((10 * Real.pi * z * t ^ 4 : Real) : Complex)) := by
    rw [mul_comm]
  rw [heq]
  exact hexp

private theorem oscAmplitude_smul_oscPhaseDeriv
    {z t : Real} (hz : z ≠ 0) (ht : t ≠ 0) :
    oscAmplitude z t • oscPhaseDeriv z t = Complex.I * oscPhase z t := by
  simp only [oscAmplitude, oscPhaseDeriv, Complex.real_smul]
  push_cast
  field_simp [hz, ht, Real.pi_ne_zero]

private theorem norm_oscPhase (z t : Real) : ‖oscPhase z t‖ = 1 := by
  unfold oscPhase
  rw [Complex.norm_exp_I_mul_ofReal]

private theorem norm_oscAmplitude {z t : Real} (hz : 0 < z) (ht : 0 < t) :
    ‖oscAmplitude z t‖ = (10 * Real.pi * z)⁻¹ * t ^ (-4 : Int) := by
  have hc : 0 < 10 * Real.pi * z := by positivity
  have htpow : 0 < t ^ (-4 : Int) := zpow_pos ht _
  rw [Real.norm_eq_abs, abs_of_pos]
  · rfl
  · exact mul_pos (inv_pos.mpr hc) htpow

private theorem norm_oscAmplitudeDeriv {z t : Real} (hz : 0 < z) (ht : 0 < t) :
    ‖oscAmplitudeDeriv z t‖ =
      4 * (10 * Real.pi * z)⁻¹ * t ^ (-5 : Int) := by
  have hc : 0 < 10 * Real.pi * z := by positivity
  have htpow : 0 < t ^ (-5 : Int) := zpow_pos ht _
  have hpos : 0 < (10 * Real.pi * z)⁻¹ * t ^ (-5 : Int) :=
    mul_pos (inv_pos.mpr hc) htpow
  have hneg : -4 * (10 * Real.pi * z)⁻¹ * t ^ (-5 : Int) < 0 := by
    nlinarith
  simp only [oscAmplitudeDeriv]
  rw [Real.norm_eq_abs, abs_of_neg hneg]
  ring

private theorem intervalIntegrable_oscAmplitudeDeriv
    {z a b : Real} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (oscAmplitudeDeriv z) volume a b := by
  have hzero : (0 : Real) ∉ [[a, b]] := by
    rw [uIcc_of_le hab]
    intro h
    have := h.1
    linarith
  unfold oscAmplitudeDeriv
  exact ((intervalIntegral.intervalIntegrable_zpow
    (n := (-5 : Int)) (Or.inr hzero)).const_mul
      (-4 * (10 * Real.pi * z)⁻¹))

private theorem intervalIntegrable_oscPhaseDeriv (z a b : Real) :
    IntervalIntegrable (oscPhaseDeriv z) volume a b := by
  apply Continuous.intervalIntegrable
  unfold oscPhaseDeriv oscPhase
  fun_prop

private theorem intervalIntegrable_oscPhase (z a b : Real) :
    IntervalIntegrable (oscPhase z) volume a b := by
  apply Continuous.intervalIntegrable
  unfold oscPhase
  fun_prop

private theorem integral_norm_oscAmplitudeDeriv
    {z h P : Real} (hz : 0 < z) (hh : 0 < h) (hP : h ≤ P) :
    (∫ t in h..P, ‖oscAmplitudeDeriv z t‖) =
      (10 * Real.pi * z)⁻¹ * (h ^ (-4 : Int) - P ^ (-4 : Int)) := by
  have ht (t : Real) (ht : t ∈ Set.Icc h P) : 0 < t := hh.trans_le ht.1
  rw [intervalIntegral.integral_congr
    (fun t htmem => by
      have ht' : t ∈ Icc h P := by simpa [uIcc_of_le hP] using htmem
      exact norm_oscAmplitudeDeriv hz (ht t ht'))]
  rw [show (fun t : Real => 4 * (10 * Real.pi * z)⁻¹ * t ^ (-5 : Int)) =
      fun t : Real => (4 * (10 * Real.pi * z)⁻¹) * t ^ (-5 : Int) by rfl]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_zpow]
  · norm_num
    ring
  · right
    constructor
    · norm_num
    · rw [uIcc_of_le hP]
      intro hzero
      linarith [hzero.1]

private theorem norm_integral_oscAmplitudeDeriv_smul_oscPhase_le
    {z h P : Real} (hz : 0 < z) (hh : 0 < h) (hP : h ≤ P) :
    ‖∫ t in h..P, oscAmplitudeDeriv z t • oscPhase z t‖ ≤
      (10 * Real.pi * z)⁻¹ * (h ^ (-4 : Int) - P ^ (-4 : Int)) := by
  calc
    ‖∫ t in h..P, oscAmplitudeDeriv z t • oscPhase z t‖ ≤
        ∫ t in h..P, ‖oscAmplitudeDeriv z t • oscPhase z t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hP
    _ = ∫ t in h..P, ‖oscAmplitudeDeriv z t‖ := by
      apply intervalIntegral.integral_congr
      intro t _ht
      simp [norm_oscPhase]
    _ = _ := integral_norm_oscAmplitudeDeriv hz hh hP

private theorem norm_integral_oscPhase_tail_le
    {z h P : Real} (hz : 0 < z) (hh : 0 < h) (hP : h ≤ P)
    (hscale : z * h ^ 5 = 1) :
    ‖∫ t in h..P, oscPhase z t‖ ≤ h := by
  have hPpos : 0 < P := hh.trans_le hP
  have hparts := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (a := h) (b := P)
    (u := oscAmplitude z) (u' := oscAmplitudeDeriv z)
    (v := oscPhase z) (v' := oscPhaseDeriv z)
    (fun t ht => hasDerivAt_oscAmplitude
      (ne_of_gt (hh.trans_le (by
        have ht' : t ∈ Icc h P := by simpa [uIcc_of_le hP] using ht
        exact ht'.1))))
    (fun t _ht => hasDerivAt_oscPhase z t)
    (intervalIntegrable_oscAmplitudeDeriv hh hP)
    (intervalIntegrable_oscPhaseDeriv z h P)
  have hleft :
      (∫ t in h..P, oscAmplitude z t • oscPhaseDeriv z t) =
        Complex.I * ∫ t in h..P, oscPhase z t := by
    calc
      (∫ t in h..P, oscAmplitude z t • oscPhaseDeriv z t) =
          ∫ t in h..P, Complex.I * oscPhase z t := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc h P := by simpa [uIcc_of_le hP] using ht
        exact oscAmplitude_smul_oscPhaseDeriv hz.ne'
          (ne_of_gt (hh.trans_le ht'.1))
      _ = Complex.I * ∫ t in h..P, oscPhase z t := by
        rw [intervalIntegral.integral_const_mul]
  have hnormLeft :
      ‖∫ t in h..P, oscAmplitude z t • oscPhaseDeriv z t‖ =
        ‖∫ t in h..P, oscPhase z t‖ := by
    rw [hleft, norm_mul, Complex.norm_I, one_mul]
  rw [← hnormLeft, hparts]
  have hrem := norm_integral_oscAmplitudeDeriv_smul_oscPhase_le hz hh hP
  have hAmpP := norm_oscAmplitude hz hPpos
  have hAmph := norm_oscAmplitude hz hh
  have hbound :
      ‖oscAmplitude z P • oscPhase z P -
          oscAmplitude z h • oscPhase z h -
          ∫ t in h..P, oscAmplitudeDeriv z t • oscPhase z t‖ ≤
        (10 * Real.pi * z)⁻¹ * P ^ (-4 : Int) +
          (10 * Real.pi * z)⁻¹ * h ^ (-4 : Int) +
            (10 * Real.pi * z)⁻¹ *
              (h ^ (-4 : Int) - P ^ (-4 : Int)) := by
    calc
      ‖oscAmplitude z P • oscPhase z P -
          oscAmplitude z h • oscPhase z h -
          ∫ t in h..P, oscAmplitudeDeriv z t • oscPhase z t‖ ≤
          ‖oscAmplitude z P • oscPhase z P‖ +
            ‖oscAmplitude z h • oscPhase z h‖ +
              ‖∫ t in h..P, oscAmplitudeDeriv z t • oscPhase z t‖ := by
        calc
          ‖oscAmplitude z P • oscPhase z P - oscAmplitude z h • oscPhase z h -
              ∫ t in h..P, oscAmplitudeDeriv z t • oscPhase z t‖ ≤
              ‖oscAmplitude z P • oscPhase z P -
                oscAmplitude z h • oscPhase z h‖ +
                ‖∫ t in h..P, oscAmplitudeDeriv z t • oscPhase z t‖ :=
            norm_sub_le _ _
          _ ≤ ‖oscAmplitude z P • oscPhase z P‖ +
              ‖oscAmplitude z h • oscPhase z h‖ +
                ‖∫ t in h..P, oscAmplitudeDeriv z t • oscPhase z t‖ := by
            gcongr
            exact norm_sub_le _ _
      _ ≤ (10 * Real.pi * z)⁻¹ * P ^ (-4 : Int) +
          (10 * Real.pi * z)⁻¹ * h ^ (-4 : Int) +
            (10 * Real.pi * z)⁻¹ *
              (h ^ (-4 : Int) - P ^ (-4 : Int)) := by
        rw [norm_smul, norm_smul, norm_oscPhase, norm_oscPhase,
          mul_one, mul_one, hAmpP, hAmph]
        linarith
  have hsimplify :
      (10 * Real.pi * z)⁻¹ * P ^ (-4 : Int) +
          (10 * Real.pi * z)⁻¹ * h ^ (-4 : Int) +
            (10 * Real.pi * z)⁻¹ *
              (h ^ (-4 : Int) - P ^ (-4 : Int)) =
        2 * (10 * Real.pi * z)⁻¹ * h ^ (-4 : Int) := by ring
  rw [hsimplify] at hbound
  have hscale' : (10 * Real.pi * z)⁻¹ * h ^ (-4 : Int) =
      h / (10 * Real.pi) := by
    change (10 * Real.pi * z)⁻¹ * (h ^ 4)⁻¹ = h / (10 * Real.pi)
    field_simp [hz.ne', hh.ne', Real.pi_ne_zero]
    nlinarith
  have hbound' :
      ‖oscAmplitude z P • oscPhase z P - oscAmplitude z h • oscPhase z h -
          ∫ t in h..P, oscAmplitudeDeriv z t • oscPhase z t‖ ≤
        2 * (h / (10 * Real.pi)) := by
    calc
      _ ≤ 2 * (10 * Real.pi * z)⁻¹ * h ^ (-4 : Int) := hbound
      _ = _ := by
        rw [show 2 * (10 * Real.pi * z)⁻¹ * h ^ (-4 : Int) =
          2 * ((10 * Real.pi * z)⁻¹ * h ^ (-4 : Int)) by ring]
        rw [hscale']
  have hpi : 2 * (h / (10 * Real.pi)) ≤ h := by
    have hden : 0 < 10 * Real.pi := by positivity
    have hcoef : (2 : Real) / (10 * Real.pi) ≤ 1 := by
      apply (div_le_iff₀ hden).2
      nlinarith [Real.pi_gt_three]
    calc
      2 * (h / (10 * Real.pi)) = h * (2 / (10 * Real.pi)) := by ring
      _ ≤ h * 1 := mul_le_mul_of_nonneg_left hcoef hh.le
      _ = h := by ring
  exact hbound'.trans hpi

private theorem norm_integral_oscPhase_initial_le
    {z h : Real} (hh : 0 ≤ h) :
    ‖∫ t in (0 : Real)..h, oscPhase z t‖ ≤ h := by
  calc
    ‖∫ t in (0 : Real)..h, oscPhase z t‖ ≤ 1 * |h - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t _ht
      rw [norm_oscPhase]
    _ = h := by simp [abs_of_nonneg hh]

private theorem norm_fifthPerturbationIntegral_le_two_mul_rpow_of_pos
    (z : Real) (hz : 0 < z) (P : Nat) :
    ‖fifthPerturbationIntegral z P‖ ≤
      2 * z ^ (-(1 : Real) / 5) := by
  let h : Real := z ^ (-(1 : Real) / 5)
  have hh : 0 < h := Real.rpow_pos_of_pos hz _
  have hscale : z * h ^ 5 = 1 := by
    have hp : h ^ 5 = z⁻¹ := by
      dsimp [h]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hz.le]
      have hcast : ((5 : Nat) : Real) = 5 := by norm_num
      rw [hcast, show (-(1 : Real) / 5) * 5 = -1 by norm_num]
      exact Real.rpow_neg_one z
    rw [hp]
    exact mul_inv_cancel₀ hz.ne'
  by_cases hPh : (P : Real) ≤ h
  · calc
      ‖fifthPerturbationIntegral z P‖ ≤ (P : Real) :=
        norm_fifthPerturbationIntegral_le z P
      _ ≤ h := hPh
      _ ≤ 2 * h := by linarith
      _ = 2 * z ^ (-(1 : Real) / 5) := by rfl
  · have hhP : h ≤ (P : Real) := (lt_of_not_ge hPh).le
    have hsplit :
        fifthPerturbationIntegral z P =
          (∫ t in (0 : Real)..h, oscPhase z t) +
            ∫ t in h..(P : Real), oscPhase z t := by
      unfold fifthPerturbationIntegral oscPhase
      symm
      exact intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_oscPhase z 0 h)
        (intervalIntegrable_oscPhase z h P)
    rw [hsplit]
    calc
      ‖(∫ t in (0 : Real)..h, oscPhase z t) +
          ∫ t in h..(P : Real), oscPhase z t‖ ≤
          ‖∫ t in (0 : Real)..h, oscPhase z t‖ +
            ‖∫ t in h..(P : Real), oscPhase z t‖ :=
        norm_add_le _ _
      _ ≤ h + h := add_le_add
        (norm_integral_oscPhase_initial_le hh.le)
        (norm_integral_oscPhase_tail_le hz hh hhP hscale)
      _ = 2 * z ^ (-(1 : Real) / 5) := by
        dsimp [h]
        ring

/-- Away from zero frequency, Chen's fifth-power perturbation integral has
the explicit decay `2 * |z|^(-1/5)`. -/
theorem norm_fifthPerturbationIntegral_le_two_mul_abs_rpow
    (z : Real) (P : Nat) (hz : z ≠ 0) :
    ‖fifthPerturbationIntegral z P‖ ≤
      2 * |z| ^ (-(1 : Real) / 5) := by
  by_cases hzpos : 0 < z
  · simpa [abs_of_pos hzpos] using
      norm_fifthPerturbationIntegral_le_two_mul_rpow_of_pos z hzpos P
  · have hzneg : z < 0 := lt_of_le_of_ne (le_of_not_gt hzpos) hz
    have hnorm :
        ‖fifthPerturbationIntegral z P‖ =
          ‖fifthPerturbationIntegral (-z) P‖ := by
      rw [← conj_fifthPerturbationIntegral z P, Complex.norm_conj]
    calc
      ‖fifthPerturbationIntegral z P‖ =
          ‖fifthPerturbationIntegral (-z) P‖ := hnorm
      _ ≤ 2 * (-z) ^ (-(1 : Real) / 5) :=
        norm_fifthPerturbationIntegral_le_two_mul_rpow_of_pos
          (-z) (neg_pos.mpr hzneg) P
      _ = 2 * |z| ^ (-(1 : Real) / 5) := by rw [abs_of_neg hzneg]

end

end Waring.Analytic
