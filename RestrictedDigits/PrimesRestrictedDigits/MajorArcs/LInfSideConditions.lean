import PrimesRestrictedDigits.MajorArcs.NondivisorDenominator
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Source side conditions for the M1 L-infinity estimate

This supplies the strict large-scale inequalities omitted between the M1
decomposition and Lemma 10.1 in `MAYNARD-PRD-PUBLISHED`, Section 11, p. 186.
It packages only the lemma's arithmetic hypotheses; the analytic estimate
itself remains a downstream result.
-/

open Filter Asymptotics

namespace PrimesRestrictedDigits

/-- A fixed power of `log (10^k)` eventually satisfies both strict scale
hypotheses in Maynard's Lemma 10.1. -/
theorem exists_majorArcLInfSourceScaleThreshold (D : Nat) :
    ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k →
      Real.log (((10 ^ k : Nat) : Real)) ^ D <
          (((10 ^ k : Nat) : Real) ^ (1 / 3 : Real)) ∧
        Real.log (((10 ^ k : Nat) : Real)) ^ D /
            (((10 ^ k : Nat) : Real)) <
          (((10 ^ k : Nat) : Real) ^ (-2 / 3 : Real)) / 2 := by
  have hreal : ∀ᶠ x : Real in atTop,
      2 * Real.log x ^ D < x ^ (1 / 3 : Real) := by
    have hbound :=
      ((isLittleO_log_rpow_rpow_atTop (D : Real)
        (by norm_num : (0 : Real) < 1 / 3)).const_mul_left 2).bound
          (by norm_num : (0 : Real) < 1 / 2)
    filter_upwards [hbound, eventually_gt_atTop (1 : Real)] with x hx hx1
    have hleft : 0 ≤ 2 * Real.log x ^ D :=
      mul_nonneg (by norm_num) (pow_nonneg (Real.log_nonneg hx1.le) D)
    have hright : 0 < x ^ (1 / 3 : Real) :=
      Real.rpow_pos_of_pos (lt_trans zero_lt_one hx1) _
    rw [Real.rpow_natCast] at hx
    rw [Real.norm_eq_abs, abs_of_nonneg hleft, Real.norm_eq_abs,
      abs_of_pos hright] at hx
    nlinarith
  have hpow :
      Tendsto (fun k : Nat => (10 : Real) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hscale := hpow.eventually hreal
  have hscale' : ∀ᶠ k : Nat in atTop,
      2 * Real.log (((10 ^ k : Nat) : Real)) ^ D <
        (((10 ^ k : Nat) : Real)) ^ (1 / 3 : Real) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hscale
  apply eventually_atTop.mp
  filter_upwards [hscale'] with k hk
  let X : Real := ((10 ^ k : Nat) : Real)
  have hX : 0 < X := by positivity
  have hroot : 0 < X ^ (1 / 3 : Real) :=
    Real.rpow_pos_of_pos hX _
  have hdenScale : Real.log X ^ D < X ^ (1 / 3 : Real) := by
    dsimp [X] at hk hroot ⊢
    nlinarith
  have hpowIdentity :
      X ^ (-2 / 3 : Real) = X ^ (1 / 3 : Real) / X := by
    calc
      X ^ (-2 / 3 : Real) = X ^ ((1 / 3 : Real) - 1) := by ring_nf
      _ = X ^ (1 / 3 : Real) / X ^ (1 : Real) :=
        Real.rpow_sub hX _ _
      _ = X ^ (1 / 3 : Real) / X := by rw [Real.rpow_one]
  have hscaleDiv :
      2 * Real.log X ^ D / X < X ^ (1 / 3 : Real) / X :=
    (div_lt_div_iff_of_pos_right hX).2 (by simpa [X] using hk)
  have herrorScale :
      Real.log X ^ D / X < X ^ (-2 / 3 : Real) / 2 := by
    rw [hpowIdentity]
    apply (lt_div_iff₀ (by norm_num : (0 : Real) < 2)).2
    calc
      Real.log X ^ D / X * 2 =
          2 * Real.log X ^ D / X := by ring
      _ < X ^ (1 / 3 : Real) / X := hscaleDiv
  exact ⟨by simpa [X] using hdenScale, by simpa [X] using herrorScale⟩

/-- Closed canonical approximation bounds become the two strict size
hypotheses of Maynard's Lemma 10.1 at a strictly smaller scale. -/
theorem majorArcRationalApproximation_lInfSideConditions
    {X frequency : Nat} {Q : Real} {r : Rat}
    (hdenScale : Q < (X : Real) ^ (1 / 3 : Real))
    (herrorScale :
      Q / (X : Real) < (X : Real) ^ (-2 / 3 : Real) / 2)
    (hr : majorArcRationalApproximation X frequency Q r) :
    (r.den : Real) < (X : Real) ^ (1 / 3 : Real) ∧
      abs ((frequency : Real) / (X : Real) - (r : Real)) <
        (X : Real) ^ (-2 / 3 : Real) / 2 :=
  ⟨hr.2.trans_lt hdenScale, hr.1.trans_lt herrorScale⟩

/-- Beyond one threshold, every repaired M1 approximation carries all
arithmetic hypotheses required by Maynard's Lemma 10.1. -/
theorem exists_majorArcClassOneLInfSourceHypothesesThreshold (D : Nat) :
    ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k → ∀ frequency : Nat,
      majorArcClassOne (10 ^ k) frequency
          (Real.log (((10 ^ k : Nat) : Real)) ^ D) →
        ∃ r : Rat, ∃ q1 q2 : Nat,
          majorArcRationalApproximation (10 ^ k) frequency
              (Real.log (((10 ^ k : Nat) : Real)) ^ D) r ∧
          r.den = q1 * q2 ∧ q1.Prime ∧ Nat.Coprime q1 10 ∧
          1 < q1 ∧ Nat.Coprime r.num.natAbs r.den ∧
          (r.den : Real) <
            (((10 ^ k : Nat) : Real) ^ (1 / 3 : Real)) ∧
          abs ((frequency : Real) / (((10 ^ k : Nat) : Real)) -
              (r : Real)) <
            (((10 ^ k : Nat) : Real) ^ (-2 / 3 : Real)) / 2 := by
  rcases exists_majorArcPowerTenFactorThreshold D with ⟨k1, hk1⟩
  rcases exists_majorArcLInfSourceScaleThreshold D with ⟨k2, hk2⟩
  refine ⟨max k1 k2, ?_⟩
  intro k hk frequency hclass
  rcases hk2 k ((le_max_right k1 k2).trans hk) with
    ⟨hdenScale, herrorScale⟩
  rcases majorArcClassOne_exists_sourceDenominatorFactor
      (hk1 k ((le_max_left k1 k2).trans hk)) hclass with
    ⟨r, q1, q2, hr, hden, hprime, hcoprime, hq1, hreduced⟩
  rcases majorArcRationalApproximation_lInfSideConditions
      hdenScale herrorScale hr with ⟨hdenSmall, herrorSmall⟩
  exact ⟨r, q1, q2, hr, hden, hprime, hcoprime, hq1, hreduced,
    hdenSmall, herrorSmall⟩

end PrimesRestrictedDigits
