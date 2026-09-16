import PrimesRestrictedDigits.PrimeNumberTheorem.LocalLogDerivative
import PrimesRestrictedDigits.PrimeNumberTheorem.LocalDivisorTranslation
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaFractionalPart
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaGrowth

/-!
# Local zeros of the Riemann zeta function

This file introduces the multiplicity-weighted local zero sum from
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, Lemma 6.4, and proves the uniform
lower bound at the center of its disk.
-/

open Complex Metric
open scoped ArithmeticFunction ComplexOrder LSeries.notation

namespace PrimesRestrictedDigits

/-- The sum over zeta zeros in the closed disk of radius `5 / 6` centered at
`3 / 2 + I * t`, with each zero weighted by its analytic multiplicity. -/
noncomputable def riemannZetaLocalZeroSum (t : Real) (s : Complex) : Complex :=
  ∑ᶠ rho : Complex,
    ((MeromorphicOn.divisor riemannZeta
      (Metric.closedBall
        (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))
        (5 / 6 : Real)) rho : Int) : Complex) / (s - rho)

/-- The value of zeta at the center `3 / 2 + I * t` has norm at least
`1 / 4`, uniformly in the height. -/
theorem one_fourth_le_norm_riemannZeta_three_halves_add_mul_I (t : Real) :
    (1 / 4 : Real) ≤
      ‖riemannZeta (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))‖ := by
  let s : Complex := ((3 / 2 : Real) : Complex) + Complex.I * t
  let x : Complex := ((3 / 2 : Real) : Complex)
  have hsRe : 1 < s.re := by
    dsimp [s]
    norm_num
  have hxRe : 0 < x.re := by
    dsimp [x]
    norm_num
  have hxOne : x ≠ 1 := by
    dsimp [x]
    norm_num
  have hxRegular := norm_riemannZeta_sub_self_div_sub_one_le hxRe hxOne
  have hxZeta : ‖riemannZeta x‖ ≤ 4 := by
    calc
      ‖riemannZeta x‖ =
          ‖(riemannZeta x - x / (x - 1)) + x / (x - 1)‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖riemannZeta x - x / (x - 1)‖ + ‖x / (x - 1)‖ :=
        norm_add_le _ _
      _ ≤ 1 + 3 := by
        gcongr
        · simpa [x] using hxRegular
        · norm_num [x]
      _ = 4 := by norm_num
  have hMu : ‖L ↗ArithmeticFunction.moebius s‖ ≤ 4 := by
    have hMuSum :
        LSeriesHasSum ↗ArithmeticFunction.moebius s
          (L ↗ArithmeticFunction.moebius s) :=
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hsRe).LSeriesHasSum
    have hOneSum : LSeriesHasSum 1 x (riemannZeta x) :=
      LSeriesHasSum_one (by norm_num [x])
    have hMuZetaRe :
        ‖L ↗ArithmeticFunction.moebius s‖ ≤ (riemannZeta x).re := by
      apply hMuSum.norm_le_of_bounded (hasSum_re hOneSum)
      intro n
      calc
        ‖LSeries.term ↗ArithmeticFunction.moebius s n‖ ≤
            ‖LSeries.term (1 : Nat → Complex) s n‖ := by
          apply LSeries.norm_term_le
          have h : ((|ArithmeticFunction.moebius n| : Int) : Real) ≤ 1 := by
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
          simpa [Complex.norm_intCast, ← Int.cast_abs] using h
        _ ≤ ‖LSeries.term (1 : Nat → Complex) x n‖ := by
          apply LSeries.norm_term_le_of_re_le_re
          simp [s, x]
        _ = (LSeries.term (1 : Nat → Complex) x n).re := by
          symm
          apply Complex.re_eq_norm.mpr
          exact LSeries.term_nonneg (by simp) (3 / 2 : Real)
    exact hMuZetaRe.trans ((Complex.re_le_norm _).trans hxZeta)
  have hProd := LSeries_one_mul_Lseries_moebius hsRe
  rw [LSeries_one_eq_riemannZeta hsRe] at hProd
  have hNormProd := congrArg norm hProd
  simp only [norm_mul, norm_one] at hNormProd
  have hOneLe : (1 : Real) ≤ ‖riemannZeta s‖ * 4 := by
    calc
      (1 : Real) =
          ‖riemannZeta s‖ * ‖L ↗ArithmeticFunction.moebius s‖ :=
        hNormProd.symm
      _ ≤ ‖riemannZeta s‖ * 4 :=
        mul_le_mul_of_nonneg_left hMu (norm_nonneg _)
  change (1 / 4 : Real) ≤ ‖riemannZeta s‖
  nlinarith

private lemma one_not_mem_riemannZeta_local_closedBall
    {t : Real} (hT : 7 / 8 ≤ |t|) :
    (1 : Complex) ∉ closedBall
      (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))
        (5 / 6 : Real) := by
  let c : Complex := ((3 / 2 : Real) : Complex) + Complex.I * t
  intro hOne
  have hDist : dist (1 : Complex) c ≤ (5 / 6 : Real) := mem_closedBall.mp hOne
  have hIm : |t| ≤ norm ((1 : Complex) - c) := by
    have h := Complex.abs_im_le_norm ((1 : Complex) - c)
    have hEq : ((1 : Complex) - c).im = -t := by
      dsimp [c]
      norm_num
    rwa [hEq, abs_neg] at h
  have : |t| ≤ (5 / 6 : Real) :=
    hIm.trans (by simpa only [dist_eq_norm] using hDist)
  norm_num at hT this
  linarith

private lemma analyticOnNhd_riemannZeta_local_closedBall
    {t : Real} (hT : 7 / 8 ≤ |t|) :
    AnalyticOnNhd Complex riemannZeta
      (closedBall
        (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))
        (5 / 6 : Real)) := by
  apply analyticOn_riemannZeta.mono
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro hzOne
  subst z
  exact one_not_mem_riemannZeta_local_closedBall hT hz

private lemma analyticOnNhd_riemannZeta_shift_local_closedBall
    {t : Real} (hT : 7 / 8 ≤ |t|) :
    AnalyticOnNhd Complex
      (fun w : Complex => riemannZeta
        (w + (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))))
      (closedBall 0 (5 / 6 : Real)) := by
  let c : Complex := ((3 / 2 : Real) : Complex) + Complex.I * t
  have hz := analyticOnNhd_riemannZeta_local_closedBall hT
  intro w hw
  have hwc : w + c ∈ closedBall c (5 / 6 : Real) := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero]
      using hw
  have hShift : AnalyticAt Complex (fun z : Complex => z + c) w := by
    fun_prop
  exact AnalyticAt.fun_comp (g := riemannZeta)
    (f := fun z : Complex => z + c) (x := w) (hz (w + c) hwc) hShift

private lemma one_not_mem_riemannZeta_shift_unit_closedBall
    {t : Real} (hT : 7 / 8 ≤ |t|) :
    (1 : Complex) ∉ closedBall
      (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex)) 1 := by
  let c : Complex := ((3 / 2 : Real) : Complex) + Complex.I * t
  intro hOne
  have hNorm : norm ((1 : Complex) - c) ≤ 1 := by
    simpa only [mem_closedBall, dist_eq_norm] using hOne
  have htSq : (7 / 8 : Real) ^ 2 ≤ t ^ 2 := by
    nlinarith [sq_abs t]
  have hNormSq : norm ((1 : Complex) - c) ^ 2 = (1 / 2 : Real) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [c]
    norm_num
    ring
  have hNormNonneg : 0 ≤ norm ((1 : Complex) - c) := norm_nonneg _
  nlinarith [sq_nonneg (norm ((1 : Complex) - c) - 1)]

private lemma analyticOnNhd_riemannZeta_shift_unit_closedBall
    {t : Real} (hT : 7 / 8 ≤ |t|) :
    AnalyticOnNhd Complex
      (fun w : Complex => riemannZeta
        (w + (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))))
      (closedBall 0 1) := by
  let c : Complex := ((3 / 2 : Real) : Complex) + Complex.I * t
  have hz : AnalyticOnNhd Complex riemannZeta (closedBall c 1) := by
    apply analyticOn_riemannZeta.mono
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hzOne
    subst z
    exact one_not_mem_riemannZeta_shift_unit_closedBall hT hz
  intro w hw
  have hwc : w + c ∈ closedBall c 1 := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero]
      using hw
  have hShift : AnalyticAt Complex (fun z : Complex => z + c) w := by
    fun_prop
  exact AnalyticAt.fun_comp (g := riemannZeta)
    (f := fun z : Complex => z + c) (x := w) (hz (w + c) hwc) hShift

/-- The logarithmic derivative of zeta is approximated uniformly by the
multiplicity-weighted zeros in the local closed disk. This is
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, Lemma 6.4. -/
theorem riemannZeta_logDeriv_localZeroSum_bound :
    ∃ C : Real, 0 < C ∧
      ∀ t sigma : Real,
        7 / 8 ≤ |t| →
        5 / 6 ≤ sigma →
        sigma ≤ 2 →
        riemannZeta
          ((sigma : Complex) + Complex.I * (t : Complex)) ≠ 0 →
        norm
          (logDeriv riemannZeta
              ((sigma : Complex) + Complex.I * (t : Complex)) -
            riemannZetaLocalZeroSum t
              ((sigma : Complex) + Complex.I * (t : Complex))) ≤
          C * Real.log (|t| + 4) := by
  refine ⟨1624, by norm_num, ?_⟩
  intro t sigma hT hSigmaLower hSigmaUpper hs
  let c : Complex := ((3 / 2 : Real) : Complex) + Complex.I * t
  let s : Complex := (sigma : Complex) + Complex.I * t
  let f : Complex → Complex := fun w => riemannZeta (w + c)
  let z : Complex := ((sigma - 3 / 2 : Real) : Complex)
  let tau : Real := |t| + 4
  let M : Real := 258 * tau
  let m : Real := 1 / 4
  have hTauFour : 4 ≤ tau := by
    dsimp [tau]
    exact le_add_of_nonneg_left (abs_nonneg t)
  have hTauPos : 0 < tau := lt_of_lt_of_le (by norm_num) hTauFour
  have hf : AnalyticOnNhd Complex f (closedBall 0 1) := by
    simpa [f, c] using analyticOnNhd_riemannZeta_shift_unit_closedBall hT
  have hM : 1 ≤ M := by
    dsimp [M]
    nlinarith
  have hm : 0 < m := by norm_num [m]
  have hmf : m ≤ ‖f 0‖ := by
    simpa [m, f, c] using
      one_fourth_le_norm_riemannZeta_three_halves_add_mul_I t
  have hf0 : f 0 ≠ 0 := by
    have : 0 < ‖f 0‖ := hm.trans_le hmf
    exact norm_pos_iff.mp this
  have hbound : ∀ u ∈ closedBall (0 : Complex) 1, ‖f u‖ ≤ M := by
    intro u hu
    have huNorm : norm u ≤ 1 := by
      simpa only [mem_closedBall, dist_zero_right] using hu
    simpa [f, c, M, tau] using
      norm_riemannZeta_le_on_shifted_unitDisk hT huNorm
  have hratio : 1 < M / m := by
    dsimp [M, m]
    norm_num
    nlinarith
  have hz : ‖z‖ ≤ (2 / 3 : Real) := by
    simp only [z, norm_real, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith
  have hzs : z + c = s := by
    dsimp [z, c, s]
    push_cast
    ring
  have hfz : f z ≠ 0 := by
    simpa [f, hzs] using hs
  have hLocal := norm_logDeriv_sub_localZeroSum_le
    hf hM hm hf0 hmf hbound hratio hz hfz
  have hsOne : s ≠ 1 := by
    intro hsOne
    have hIm := congrArg Complex.im hsOne
    dsimp [s] at hIm
    norm_num at hIm
    subst t
    norm_num at hT
  have hLogDeriv : logDeriv f z = logDeriv riemannZeta s := by
    change logDeriv (riemannZeta ∘ fun w : Complex => w + c) z = _
    rw [logDeriv_comp (differentiableAt_riemannZeta (by simpa [hzs] using hsOne))
      (by fun_prop)]
    rw [hzs]
    simp
  have hfTarget := analyticOnNhd_riemannZeta_shift_local_closedBall hT
  have hzTarget := analyticOnNhd_riemannZeta_local_closedBall hT
  have hSum :
      (∑ᶠ w : Complex,
        ((MeromorphicOn.divisor f
          (closedBall 0 (5 / 6 : Real)) w : Int) : Complex) / (z - w)) =
        riemannZetaLocalZeroSum t s := by
    have hTranslate := finsum_divisor_add_shift_eq
      riemannZeta c s (5 / 6 : Real)
      hfTarget.meromorphicOn hzTarget.meromorphicOn
    simpa [riemannZetaLocalZeroSum, f, c, z, s] using hTranslate
  rw [hLogDeriv, hSum] at hLocal
  have hRatio : M / m = 1032 * tau := by
    dsimp [M, m]
    ring
  rw [hRatio] at hLocal
  have hPowSix : (1032 : Real) ≤ tau ^ 6 := by
    calc
      (1032 : Real) ≤ 4 ^ 6 := by norm_num
      _ ≤ tau ^ 6 := pow_le_pow_left₀ (by norm_num) hTauFour 6
  have hArg : (1032 : Real) * tau ≤ tau ^ 7 := by
    calc
      (1032 : Real) * tau ≤ tau ^ 6 * tau :=
        mul_le_mul_of_nonneg_right hPowSix hTauPos.le
      _ = tau ^ 7 := by ring
  have hLog : Real.log (1032 * tau) ≤ 7 * Real.log tau := by
    have := Real.log_le_log (by positivity) hArg
    rw [Real.log_pow] at this
    norm_num at this ⊢
    exact this
  change ‖logDeriv riemannZeta s - riemannZetaLocalZeroSum t s‖ ≤
    1624 * Real.log tau
  calc
    ‖logDeriv riemannZeta s - riemannZetaLocalZeroSum t s‖ ≤
        232 * Real.log (1032 * tau) := hLocal
    _ ≤ 232 * (7 * Real.log tau) :=
      mul_le_mul_of_nonneg_left hLog (by norm_num)
    _ = 1624 * Real.log tau := by ring

end PrimesRestrictedDigits
