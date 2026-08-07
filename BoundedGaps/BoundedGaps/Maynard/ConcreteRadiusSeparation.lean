import BoundedGaps.Maynard.ConcreteRadiusLogAsymptotics

noncomputable section

namespace BoundedGaps.Maynard

open Filter

theorem eventually_engelsmaMaynardRadius_exponent_lt_half
    {alpha gamma : ℝ} (halpha : 0 < alpha)
    (_hgamma : 0 < gamma) (hgamma_lt : gamma < 1) :
    ∀ᶠ N : ℕ in atTop,
      2 * engelsmaMaynardRadius (alpha * gamma) N + 1 ≤
        engelsmaMaynardRadius alpha N := by
  let X : ℕ → ℝ := fun N => (N - 1 : ℕ)
  let delta : ℝ := alpha * (1 - gamma)
  have hdelta : 0 < delta := mul_pos halpha (sub_pos.mpr hgamma_lt)
  have hX : Tendsto X atTop atTop := by
    dsimp [X]
    exact tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
  have hXpos : ∀ᶠ N : ℕ in atTop, 0 < X N :=
    hX.eventually (eventually_gt_atTop 0)
  have hpowA : Tendsto (fun N : ℕ => X N ^ alpha) atTop atTop :=
    (tendsto_rpow_atTop halpha).comp hX
  have hpowGap : Tendsto (fun N : ℕ => X N ^ (-delta))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hdelta).comp hX
  have hratio : Tendsto (fun N : ℕ =>
      (X N ^ (alpha * gamma)) / (X N ^ alpha))
      atTop (nhds 0) := by
    apply hpowGap.congr'
    filter_upwards [hXpos] with N hXN
    have he : -delta = alpha * gamma - alpha := by
      dsimp [delta]
      ring
    rw [he]
    rw [← Real.rpow_sub hXN]
  have hratioEvent := hratio.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  have hpowEvent := hpowA.eventually (eventually_ge_atTop (4 : ℝ))
  filter_upwards [hXpos, hratioEvent, hpowEvent, eventually_ge_atTop 3]
    with N hXN hratioN hpowN hN
  let A : ℝ := X N ^ alpha
  let G : ℝ := X N ^ (alpha * gamma)
  have hA : 0 < A := by dsimp [A]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hGbound : G ≤ A / 4 := by
    have hlt := (div_lt_iff₀ hA).mp hratioN
    linarith
  have hreal : 2 * G + 1 ≤ A - 1 := by
    have hA4 : 4 ≤ A := by simpa [A] using hpowN
    linarith
  have hfloorA : A - 1 <
      (engelsmaMaynardRadius alpha N : ℝ) := by
    unfold A X engelsmaMaynardRadius maynardDivisorCutoff
    exact Nat.sub_one_lt_floor (R := ℝ) (X N ^ alpha)
  have hfloorG :
      (engelsmaMaynardRadius (alpha * gamma) N : ℝ) ≤ G := by
    unfold G X engelsmaMaynardRadius maynardDivisorCutoff
    exact Nat.floor_le (Real.rpow_nonneg (by positivity) (alpha * gamma))
  have hreal' :
      (2 * engelsmaMaynardRadius (alpha * gamma) N + 1 : ℕ) <=
        (engelsmaMaynardRadius alpha N : ℝ) := by
    exact_mod_cast (show
      (2 * engelsmaMaynardRadius (alpha * gamma) N + 1 : ℝ) ≤
        (engelsmaMaynardRadius alpha N : ℝ) by
      calc
        (2 * engelsmaMaynardRadius (alpha * gamma) N + 1 : ℝ) ≤
            2 * G + 1 := by linarith
        _ ≤ A - 1 := hreal
        _ ≤ (engelsmaMaynardRadius alpha N : ℝ) := hfloorA.le)
  exact_mod_cast hreal'

end BoundedGaps.Maynard
