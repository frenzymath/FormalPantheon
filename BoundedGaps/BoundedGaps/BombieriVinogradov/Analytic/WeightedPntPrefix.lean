import BoundedGaps.BombieriVinogradov.StandardStatement
import BoundedGaps.BombieriVinogradov.Analytic.WeightedCenterBridge
import BoundedGaps.PrimeNumberTheorem.Analytic.StrongChebyshev
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The modulus-one weighted prefix

SEM-579 gives a strong natural-endpoint estimate for `psi`.  At modulus one
the standard weighted discrepancy is `|psi(y)-y|`.  The proof below first
builds an exponential envelope uniformly over `2 <= y <= x`, splitting at
`sqrt x`, and then absorbs that envelope into an arbitrary logarithmic power.
This owner deliberately does not import any prime-counting or closed
Bombieri--Vinogradov theorem.
-/

namespace BoundedGaps.BombieriVinogradov

open Filter
open scoped BigOperators

noncomputable section

private theorem exists_weighted_one_exp_envelope :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∃ X0 : ℕ, 4 ≤ X0 ∧
        ∀ x : ℕ, X0 ≤ x →
          ∀ y : ℕ, 2 ≤ y → y ≤ x →
            |Chebyshev.psi (y : ℝ) - (y : ℝ)| ≤
              C * ((x : ℝ) * Real.exp
                (-c * Real.sqrt (Real.log (x : ℝ)))) := by
  obtain ⟨C0, c0, hC0, hc0, Xs, hXs, hpoint⟩ :=
    BoundedGaps.PrimeNumberTheorem.exists_abs_chebyshevPsi_sub_natCast_le_exp_neg_sqrtLog
  let Kψ : ℝ := Real.log 4 + 4
  let C : ℝ := max (C0 + Kψ + 1) C0
  let c : ℝ := min (c0 / 2) (1 / 2 : ℝ)
  have hKψ : 0 < Kψ := by
    dsimp [Kψ]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (by positivity) (by norm_num)
  have hcHalf : c ≤ (1 / 2 : ℝ) := min_le_right _ _
  have hcC0 : c ≤ c0 / 2 := min_le_left _ _
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ x : ℕ in atTop, 4 ≤ Real.log (x : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop 4)
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨Xlog, hXlog⟩ := hevent
  let X0 : ℕ := max 4 (max Xlog (Xs ^ 2))
  refine ⟨C, c, hC, hc, X0, by simp [X0], ?_⟩
  intro x hx y hy hyx
  have hx4 : 4 ≤ x := by
    dsimp [X0] at hx
    omega
  have hXlogX : Xlog ≤ x := by
    dsimp [X0] at hx
    omega
  have hXsSqX : Xs ^ 2 ≤ x := by
    dsimp [X0] at hx
    omega
  have hLFour : 4 ≤ Real.log (x : ℝ) := hXlog x hXlogX
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hxnonneg : (0 : ℝ) ≤ (x : ℝ) := hxpos.le
  have hsqrtXpos : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.2 hxpos
  have hXsRoot : (Xs : ℝ) ≤ Real.sqrt (x : ℝ) := by
    have hsquares : (Xs : ℝ) ^ 2 ≤ (x : ℝ) := by
      exact_mod_cast hXsSqX
    have hsqrt := Real.sqrt_le_sqrt hsquares
    rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Xs)] at hsqrt
    exact hsqrt
  let L : ℝ := Real.log (x : ℝ)
  let u : ℝ := Real.sqrt L
  have hLFour' : 4 ≤ L := by simpa [L] using hLFour
  have hLnonneg : 0 ≤ L := by linarith
  have huNonneg : 0 ≤ u := by dsimp [u]; positivity
  have huSq : u ^ 2 = L := by
    dsimp [u]
    exact Real.sq_sqrt hLnonneg
  by_cases hySmall : (y : ℝ) ≤ Real.sqrt (x : ℝ)
  · have hypos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (show 0 < y by omega)
    have hynonneg : (0 : ℝ) ≤ (y : ℝ) := hypos.le
    have hpsi : Chebyshev.psi (y : ℝ) ≤ Kψ * (y : ℝ) := by
      simpa [Kψ] using Chebyshev.psi_le_const_mul_self hynonneg
    have hlinear :
        |Chebyshev.psi (y : ℝ) - (y : ℝ)| ≤
          (Kψ + 1) * Real.sqrt (x : ℝ) := by
      calc
        |Chebyshev.psi (y : ℝ) - (y : ℝ)| ≤
            Chebyshev.psi (y : ℝ) + (y : ℝ) := by
          simpa [abs_of_nonneg (Chebyshev.psi_nonneg _),
            abs_of_nonneg hynonneg] using
            (abs_sub_le (Chebyshev.psi (y : ℝ)) 0 (y : ℝ))
        _ ≤ Kψ * (y : ℝ) + (y : ℝ) := add_le_add hpsi le_rfl
        _ ≤ Kψ * Real.sqrt (x : ℝ) + Real.sqrt (x : ℝ) := by
          gcongr
        _ = (Kψ + 1) * Real.sqrt (x : ℝ) := by ring
    have hTwoLeU : (2 : ℝ) ≤ u := by
      apply (sq_le_sq₀ (by norm_num) huNonneg).mp
      nlinarith
    have huLHalf : u ≤ L / 2 := by
      nlinarith [mul_nonneg huNonneg (sub_nonneg.mpr hTwoLeU)]
    have hcu : c * u ≤ L / 2 := by
      have hcu' : c * u ≤ (1 / 2 : ℝ) * u :=
        mul_le_mul_of_nonneg_right hcHalf huNonneg
      nlinarith
    have hsqrtEnvelope :
        Real.sqrt (x : ℝ) ≤
          (x : ℝ) * Real.exp
            (-c * Real.sqrt (Real.log (x : ℝ))) := by
      calc
        Real.sqrt (x : ℝ) = Real.exp (L / 2) := by
          rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hxpos]
          congr 1
          dsimp [L]
          ring
        _ ≤ Real.exp (L - c * u) := by
          apply Real.exp_monotone
          linarith
        _ = (x : ℝ) * Real.exp
            (-c * Real.sqrt (Real.log (x : ℝ))) := by
          rw [show L - c * u = L + (-c * u) by ring,
            Real.exp_add]
          dsimp [L, u]
          rw [Real.exp_log hxpos]
    have hKC : Kψ + 1 ≤ C := by
      dsimp [C]
      calc
        Kψ + 1 ≤ C0 + Kψ + 1 := by linarith
        _ ≤ max (C0 + Kψ + 1) C0 := le_max_left _ _
    calc
      |Chebyshev.psi (y : ℝ) - (y : ℝ)| ≤
          (Kψ + 1) * Real.sqrt (x : ℝ) := hlinear
      _ ≤ (Kψ + 1) * ((x : ℝ) * Real.exp
          (-c * Real.sqrt (Real.log (x : ℝ)))) :=
        mul_le_mul_of_nonneg_left hsqrtEnvelope (by positivity)
      _ ≤ C * ((x : ℝ) * Real.exp
          (-c * Real.sqrt (Real.log (x : ℝ)))) := by
        apply mul_le_mul_of_nonneg_right hKC
        positivity
  · have hyLarge : Real.sqrt (x : ℝ) < (y : ℝ) := lt_of_not_ge hySmall
    let l : ℝ := Real.log (y : ℝ)
    have hlogHalf : L / 2 ≤ l := by
      calc
        L / 2 = Real.log (Real.sqrt (x : ℝ)) := by
          rw [Real.log_sqrt hxnonneg]
        _ ≤ Real.log (y : ℝ) := Real.log_le_log hsqrtXpos hyLarge.le
        _ = l := rfl
    have hlTwo : (2 : ℝ) ≤ l := by linarith
    have hlNonneg : 0 ≤ l := by linarith
    have hXsLtY : Xs < y := by
      exact_mod_cast hXsRoot.trans_lt hyLarge
    have hpointY := hpoint y hXsLtY.le
    have hhalfSqrt : Real.sqrt L / 2 ≤ Real.sqrt l := by
      apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg l)).mp
      rw [div_pow, Real.sq_sqrt hLnonneg, Real.sq_sqrt hlNonneg]
      nlinarith
    have hdecayScale : c * Real.sqrt L ≤ c0 * Real.sqrt l := by
      calc
        c * Real.sqrt L ≤ (c0 / 2) * Real.sqrt L :=
          mul_le_mul_of_nonneg_right hcC0 (Real.sqrt_nonneg L)
        _ = c0 * (Real.sqrt L / 2) := by ring
        _ ≤ c0 * Real.sqrt l :=
          mul_le_mul_of_nonneg_left hhalfSqrt hc0.le
    have hdecay : Real.exp (-c0 * Real.sqrt l) ≤
        Real.exp (-c * Real.sqrt L) := by
      apply Real.exp_monotone
      linarith
    have hyCast : (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast hyx
    have hC0C : C0 ≤ C := by
      dsimp [C]
      exact le_max_right _ _
    calc
      |Chebyshev.psi (y : ℝ) - (y : ℝ)| ≤
          C0 * ((y : ℝ) * Real.exp
            (-c0 * Real.sqrt (Real.log (y : ℝ)))) := hpointY
      _ ≤ C0 * ((x : ℝ) * Real.exp
          (-c * Real.sqrt (Real.log (x : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ hC0.le
        apply mul_le_mul hyCast
        · simpa [L, l] using hdecay
        · positivity
        · positivity
      _ ≤ C * ((x : ℝ) * Real.exp
          (-c * Real.sqrt (Real.log (x : ℝ)))) := by
        apply mul_le_mul_of_nonneg_right hC0C
        positivity

theorem exists_maxWeightedProgressionDiscrepancyUpTo_one_le_logSaving :
    ∀ D : ℝ, 0 ≤ D ->
      ∃ C : ℝ, 0 ≤ C ∧ ∃ X0 : ℕ, 4 ≤ X0 ∧
        ∀ x : ℕ, X0 ≤ x ->
          maxWeightedProgressionDiscrepancyUpTo x 1 <=
            C * (x : ℝ) /
              Real.rpow (Real.log (x : ℝ)) D := by
  intro D hD
  obtain ⟨C0, c, hC0, hc, Xenv, hXenv, henv⟩ :=
    exists_weighted_one_exp_envelope
  have huTop : Tendsto
      (fun x : ℕ ↦ Real.sqrt (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hdom :=
    ((isLittleO_rpow_exp_pos_mul_atTop (2 * D) hc).comp_tendsto huTop).eventuallyLE
  rw [Filter.eventually_atTop] at hdom
  obtain ⟨Xdom, hXdom⟩ := hdom
  let X0 : ℕ := max Xenv (max Xdom 4)
  refine ⟨C0, le_of_lt hC0, X0, by simp [X0], ?_⟩
  intro x hx
  have hxEnv : Xenv ≤ x := by
    dsimp [X0] at hx
    omega
  have hxDom : Xdom ≤ x := by
    dsimp [X0] at hx
    omega
  have hx4 : 4 ≤ x := by
    dsimp [X0] at hx
    omega
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hlogPos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have huNonneg : 0 ≤ Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_nonneg _
  have hpoly := hXdom x hxDom
  have hpoly' :
      Real.rpow (Real.sqrt (Real.log (x : ℝ))) (2 * D) ≤
        Real.exp (c * Real.sqrt (Real.log (x : ℝ))) := by
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg huNonneg _),
      abs_of_pos (Real.exp_pos _)] using hpoly
  have hpowIdentity :
      Real.rpow (Real.log (x : ℝ)) D =
        Real.rpow (Real.sqrt (Real.log (x : ℝ))) (2 * D) := by
    calc
      Real.rpow (Real.log (x : ℝ)) D =
          Real.rpow (Real.sqrt (Real.log (x : ℝ)) ^ 2) D := by
        rw [Real.sq_sqrt (le_of_lt hlogPos)]
      _ = Real.rpow (Real.rpow (Real.sqrt (Real.log (x : ℝ))) (2 : ℝ)) D := by
        congr 1
        exact (Real.rpow_natCast _ 2).symm
      _ = Real.rpow (Real.sqrt (Real.log (x : ℝ))) ((2 : ℝ) * D) :=
        (Real.rpow_mul (Real.sqrt_nonneg _) 2 D).symm
      _ = Real.rpow (Real.sqrt (Real.log (x : ℝ))) (2 * D) := by rfl
  have hsavePos : 0 < Real.rpow (Real.log (x : ℝ)) D :=
    Real.rpow_pos_of_pos hlogPos _
  have hdecay :
      Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) ≤
        1 / Real.rpow (Real.log (x : ℝ)) D := by
    apply (le_div_iff₀ hsavePos).2
    rw [hpowIdentity]
    calc
      Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) *
          Real.rpow (Real.sqrt (Real.log (x : ℝ))) (2 * D) ≤
        Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) *
          Real.exp (c * Real.sqrt (Real.log (x : ℝ))) :=
        mul_le_mul_of_nonneg_left hpoly' (Real.exp_pos _).le
      _ = 1 := by simp [← Real.exp_add]
  rw [maxWeightedProgressionDiscrepancyUpTo_one (by omega)]
  apply Finset.sup'_le (endpointRange_nonempty (by omega))
  intro y hy
  have hyBounds := Finset.mem_Icc.mp hy
  have hpoint := henv x hxEnv y hyBounds.1 hyBounds.2
  calc
    |Chebyshev.psi (y : ℝ) - (y : ℝ)| ≤
        C0 * ((x : ℝ) * Real.exp
          (-c * Real.sqrt (Real.log (x : ℝ)))) := hpoint
    _ ≤ C0 * ((x : ℝ) /
        Real.rpow (Real.log (x : ℝ)) D) := by
      apply mul_le_mul_of_nonneg_left _ hC0.le
      rw [div_eq_mul_inv]
      simpa [div_eq_mul_inv] using
        (mul_le_mul_of_nonneg_left hdecay hxpos.le)
    _ = C0 * (x : ℝ) /
        Real.rpow (Real.log (x : ℝ)) D := by ring

end

end BoundedGaps.BombieriVinogradov
