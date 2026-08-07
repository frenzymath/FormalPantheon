import BoundedGaps.BombieriVinogradov.Analytic.SiegelWalfisz
import BoundedGaps.BombieriVinogradov.Analytic.VaughanFiveTermEndpoint

/-!
# Siegel--Walfisz primitive endpoint maximum

This file upgrades the pointwise nonprincipal character estimate from SEM-564
to the exact primitive centered endpoint maximum used by the small-conductor
Bombieri--Vinogradov branch. Small endpoints use Chebyshev's elementary linear
bound; endpoints above `sqrt x` use SEM-564 with exponent `2 * D`.

Sources: `DavenportMNTCh22SW1980`, printed pp. 132--133;
`AkbaryHambrook2013v2`, Section 7, printed pp. 24--25. Semantic review:
`SEM-565`.
-/

namespace BoundedGaps.Maynard

open Filter

noncomputable section

/-- The nonprincipal Siegel--Walfisz estimate, uniformly maximized over the
natural endpoints `2 <= y <= x` of one primitive character. -/
theorem exists_siegelWalfisz_primitiveCenteredEndpointMaximum_le :
    ∀ D : ℝ, 0 < D →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∃ X0 : ℕ, 4 ≤ X0 ∧
          ∀ x : ℕ, X0 ≤ x →
            ∀ d : ℕ, 1 < d →
              (d : ℝ) ≤ Real.log (x : ℝ) ^ D →
                ∀ ψ : primitiveCharacters d,
                  primitiveCenteredEndpointMaximum x d ψ ≤
                    C * ((x : ℝ) * Real.exp
                      (-c * Real.sqrt (Real.log (x : ℝ)))) := by
  intro D hD
  obtain ⟨C0, c0, hC0, hc0, Xs, hXsFour, hpoint⟩ :=
    exists_siegelWalfisz_norm_twistedChebyshevSum_le
      (2 * D) (by positivity)
  let Kψ : ℝ := Real.log 4 + 4
  let C : ℝ := C0 + Kψ
  let c : ℝ := min (c0 / 2) 1
  have hKψ : 0 < Kψ := by
    dsimp [Kψ]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (by positivity) zero_lt_one
  have hcC0 : c ≤ c0 / 2 := by
    exact min_le_left _ _
  have hcOne : c ≤ 1 := by
    exact min_le_right _ _
  have hlogTop : Tendsto
      (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ x : ℕ in atTop, 4 ≤ Real.log (x : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop 4)
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨Xlog, hXlog⟩ := hevent
  let X0 : ℕ := max 4 (max Xlog (Xs ^ 2))
  refine ⟨C, c, hC, hc, X0, by simp [X0], ?_⟩
  intro x hxX0 d hd hdLog ψ
  have hxFour : 4 ≤ x := by
    dsimp [X0] at hxX0
    omega
  have hXlogX : Xlog ≤ x := by
    dsimp [X0] at hxX0
    omega
  have hXsSqX : Xs ^ 2 ≤ x := by
    dsimp [X0] at hxX0
    omega
  have hLFour : 4 ≤ Real.log (x : ℝ) := hXlog x hXlogX
  have hxpos : (0 : ℝ) < x := by
    exact_mod_cast (show 0 < x by omega)
  have hxnonneg : (0 : ℝ) ≤ x := hxpos.le
  have hXsRoot : (Xs : ℝ) ≤ Real.sqrt (x : ℝ) := by
    have hsquares : (Xs : ℝ) ^ 2 ≤ (x : ℝ) := by
      exact_mod_cast hXsSqX
    have hsqrt := Real.sqrt_le_sqrt hsquares
    rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Xs)] at hsqrt
    exact hsqrt
  rw [primitiveCenteredEndpointMaximum_eq_raw x hd ψ]
  unfold primitiveRawEndpointMaximum
  rw [dif_pos (by omega : 2 ≤ x)]
  apply Finset.sup'_le
  intro y hy
  have hyBounds : 2 ≤ y ∧ y ≤ x := Finset.mem_Icc.mp hy
  have hypos : (0 : ℝ) < y := by
    exact_mod_cast (show 0 < y by omega)
  have hynonneg : (0 : ℝ) ≤ y := hypos.le
  by_cases hySmall : (y : ℝ) ≤ Real.sqrt (x : ℝ)
  · have hlinear :
        ‖twistedChebyshevSum y d ψ.1‖ ≤
          Kψ * Real.sqrt (x : ℝ) := by
      calc
        ‖twistedChebyshevSum y d ψ.1‖ ≤ Chebyshev.psi (y : ℝ) :=
          norm_twistedChebyshevSum_le_psi y d ψ.1
        _ ≤ Kψ * (y : ℝ) := by
          simpa [Kψ] using Chebyshev.psi_le_const_mul_self hynonneg
        _ ≤ Kψ * Real.sqrt (x : ℝ) :=
          mul_le_mul_of_nonneg_left hySmall hKψ.le
    let L : ℝ := Real.log (x : ℝ)
    let u : ℝ := Real.sqrt L
    have hLFour' : 4 ≤ L := by simpa [L] using hLFour
    have hLnonneg : 0 ≤ L := by linarith
    have huNonneg : 0 ≤ u := by dsimp [u]; positivity
    have huSq : u ^ 2 = L := by
      dsimp [u]
      exact Real.sq_sqrt hLnonneg
    have hTwoLeU : (2 : ℝ) ≤ u := by
      apply (sq_le_sq₀ (by norm_num) huNonneg).mp
      nlinarith
    have huLHalf : u ≤ L / 2 := by
      nlinarith [mul_nonneg huNonneg (sub_nonneg.mpr hTwoLeU)]
    have hcu : c * u ≤ L / 2 := by
      have hcu' : c * u ≤ 1 * u :=
        mul_le_mul_of_nonneg_right hcOne huNonneg
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
    have hKψC : Kψ ≤ C := by
      dsimp [C]
      linarith
    calc
      ‖twistedChebyshevSum y d ψ.1‖ ≤
          Kψ * Real.sqrt (x : ℝ) := hlinear
      _ ≤ Kψ * ((x : ℝ) * Real.exp
          (-c * Real.sqrt (Real.log (x : ℝ)))) :=
        mul_le_mul_of_nonneg_left hsqrtEnvelope hKψ.le
      _ ≤ C * ((x : ℝ) * Real.exp
          (-c * Real.sqrt (Real.log (x : ℝ)))) := by
        apply mul_le_mul_of_nonneg_right hKψC
        positivity
  · have hyLarge : Real.sqrt (x : ℝ) < (y : ℝ) :=
      lt_of_not_ge hySmall
    let L : ℝ := Real.log (x : ℝ)
    let l : ℝ := Real.log (y : ℝ)
    have hLFour' : 4 ≤ L := by simpa [L] using hLFour
    have hLnonneg : 0 ≤ L := by linarith
    have hsqrtPos : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.2 hxpos
    have hlogHalf : L / 2 ≤ l := by
      calc
        L / 2 = Real.log (Real.sqrt (x : ℝ)) := by
          rw [Real.log_sqrt hxnonneg]
        _ ≤ Real.log (y : ℝ) :=
          Real.log_le_log hsqrtPos hyLarge.le
        _ = l := rfl
    have hlTwo : (2 : ℝ) ≤ l := by linarith
    have hlNonneg : 0 ≤ l := by linarith
    have hLleLSq : L ≤ l ^ 2 := by
      have hLleTwoL : L ≤ 2 * l := by linarith
      have hTwoLleSq : 2 * l ≤ l ^ 2 := by
        nlinarith [mul_nonneg hlNonneg (sub_nonneg.mpr hlTwo)]
      exact hLleTwoL.trans hTwoLleSq
    have hpower : L ^ D ≤ l ^ (2 * D) := by
      calc
        L ^ D ≤ (l ^ 2) ^ D :=
          Real.rpow_le_rpow hLnonneg hLleLSq hD.le
        _ = (l ^ (2 : ℝ)) ^ D := by rw [Real.rpow_two]
        _ = l ^ (2 * D) := (Real.rpow_mul hlNonneg 2 D).symm
    have hdLogY : (d : ℝ) ≤ Real.log (y : ℝ) ^ (2 * D) :=
      hdLog.trans (by simpa [L, l] using hpower)
    have hXsLtY : Xs < y := by
      exact_mod_cast hXsRoot.trans_lt hyLarge
    letI : NeZero d := ⟨by omega⟩
    have hpointY := hpoint y (by omega) d ψ.1
      (primitiveCharacter_ne_one_of_one_lt hd ψ) hdLogY
    have hquarter : L / 4 ≤ l := by linarith
    have hhalfSqrt :
        Real.sqrt L / 2 ≤ Real.sqrt l := by
      apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg l)).mp
      rw [div_pow, Real.sq_sqrt hLnonneg, Real.sq_sqrt hlNonneg]
      nlinarith
    have hdecayScale :
        c * Real.sqrt L ≤ c0 * Real.sqrt l := by
      calc
        c * Real.sqrt L ≤ (c0 / 2) * Real.sqrt L :=
          mul_le_mul_of_nonneg_right hcC0 (Real.sqrt_nonneg L)
        _ = c0 * (Real.sqrt L / 2) := by ring
        _ ≤ c0 * Real.sqrt l :=
          mul_le_mul_of_nonneg_left hhalfSqrt hc0.le
    have hdecay :
        Real.exp (-c0 * Real.sqrt l) ≤
          Real.exp (-c * Real.sqrt L) := by
      apply Real.exp_monotone
      linarith
    have hyCast : (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast hyBounds.2
    have hC0C : C0 ≤ C := by
      dsimp [C]
      linarith
    calc
      ‖twistedChebyshevSum y d ψ.1‖ ≤
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

end

end BoundedGaps.Maynard
