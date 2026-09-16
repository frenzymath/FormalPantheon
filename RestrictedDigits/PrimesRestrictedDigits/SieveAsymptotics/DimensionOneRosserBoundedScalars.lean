import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondEndpoint
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondIntegral

/-!
# Scalars for bounded second Rosser continuation

This file fixes the absolute splice and level threshold used to make the bounded-coordinate
continuation after Iwaniec's Eq. (8.10) explicit. It also collects the scalar estimates shared
by the bounded integral and monotonicity arguments. See `IWANIEC-ROSSER-SIEVE-1980`, printed
pp. 199--201.
-/

namespace PrimesRestrictedDigits

/-- Absolute splice for the bounded-coordinate continuation. -/
noncomputable def dimensionOneRosserSecondSplice : Real :=
  Real.exp 5000 + 3

/-- Absolute level threshold for the bounded-coordinate continuation. -/
noncomputable def dimensionOneRosserSecondLevelThreshold : Real :=
  9792 * dimensionOneRosserSecondSplice ^ 52

/-- The fixed splice is at least one. -/
theorem one_le_dimensionOneRosserSecondSplice :
    1 <= dimensionOneRosserSecondSplice := by
  unfold dimensionOneRosserSecondSplice
  nlinarith [Real.exp_pos (5000 : Real)]

/-- The fixed level threshold is positive. -/
theorem dimensionOneRosserSecondLevelThreshold_pos :
    0 < dimensionOneRosserSecondLevelThreshold := by
  unfold dimensionOneRosserSecondLevelThreshold
  exact mul_pos (by norm_num)
    (pow_pos (lt_of_lt_of_le zero_lt_one
      one_le_dimensionOneRosserSecondSplice) _)

/-- Under the bounded-continuation threshold, the artificial factor has a
uniform first-order upper bound. -/
theorem dimensionOneRosserArtificialFactor_zero_le_one_add
    {L t u : Real} (hu : 1 <= u) (ht : 0 <= t) (htu : t <= u)
    (hgrowth : 9792 * u ^ 52 <= L) :
    dimensionOneRosserArtificialFactor L 0 t <= 1 + 1 / (12 * u) := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hL : 0 < L := by
    exact (mul_pos (by norm_num) (pow_pos hu0 52)).trans_le hgrowth
  have htPow : t ^ 50 <= u ^ 50 := pow_le_pow_left₀ ht htu 50
  have hratioNonneg : 0 <= t ^ 50 / L :=
    div_nonneg (pow_nonneg ht 50) hL.le
  have hbaseOne : 1 <= dimensionOneRosserArtificialBase L 0 t := by
    simp only [dimensionOneRosserArtificialBase, add_zero]
    linarith
  have hlogNonneg :
      0 <= Real.log (dimensionOneRosserArtificialBase L 0 t) :=
    Real.log_nonneg hbaseOne
  have hlogLe :
      Real.log (dimensionOneRosserArtificialBase L 0 t) <= t ^ 50 / L := by
    simpa [dimensionOneRosserArtificialBase] using
      Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + t ^ 50 / L)
  let r : Real := t * Real.log (dimensionOneRosserArtificialBase L 0 t)
  have hrNonneg : 0 <= r := mul_nonneg ht hlogNonneg
  have hrLePower : r <= u ^ 51 / L := by
    calc
      r <= u * (u ^ 50 / L) := by
        dsimp [r]
        exact mul_le_mul htu
          (hlogLe.trans (div_le_div_of_nonneg_right htPow hL.le))
          hlogNonneg hu0.le
      _ = u ^ 51 / L := by ring
  have hpowerLe : u ^ 51 / L <= 1 / (9792 * u) := by
    rw [div_le_iff₀ hL]
    have hscale : 0 <= 1 / (9792 * u) := by positivity
    have h := mul_le_mul_of_nonneg_left hgrowth hscale
    calc
      u ^ 51 = (1 / (9792 * u)) * (9792 * u ^ 52) := by
        field_simp
      _ <= (1 / (9792 * u)) * L := h
      _ = 1 / (9792 * u) * L := rfl
  have hrLe : r <= 1 / (9792 * u) := hrLePower.trans hpowerLe
  have hsmallOne : 1 / (9792 * u) <= 1 := by
    rw [div_le_one (by positivity : 0 < (9792 : Real) * u)]
    nlinarith
  have habs : |r| <= 1 := by
    rw [abs_of_nonneg hrNonneg]
    exact hrLe.trans hsmallOne
  have hexpError := Real.abs_exp_sub_one_le habs
  have hexpLe : Real.exp r <= 1 + 2 * r := by
    have hself : Real.exp r - 1 <= |Real.exp r - 1| := le_abs_self _
    have hrAbs : |r| = r := abs_of_nonneg hrNonneg
    rw [hrAbs] at hexpError
    linarith
  have hrelax : 2 * r <= 1 / (12 * u) := by
    calc
      2 * r <= 2 * (1 / (9792 * u)) :=
        mul_le_mul_of_nonneg_left hrLe (by norm_num)
      _ = 2 / (9792 * u) := by ring
      _ <= 1 / (12 * u) := by
        rw [div_le_div_iff₀ (by positivity : 0 < (9792 : Real) * u)
          (by positivity : 0 < (12 : Real) * u)]
        nlinarith
  unfold dimensionOneRosserArtificialFactor
  change Real.exp r <= _
  exact hexpLe.trans (by linarith)

/-- The epsilon-zero artificial factor is at least one for a nonnegative
coordinate. -/
theorem one_le_dimensionOneRosserArtificialFactor_zero
    {L t : Real} (hL : 0 < L) (ht : 0 <= t) :
    1 <= dimensionOneRosserArtificialFactor L 0 t := by
  unfold dimensionOneRosserArtificialFactor
  rw [Real.one_le_exp_iff]
  exact mul_nonneg ht (Real.log_nonneg (by
    unfold dimensionOneRosserArtificialBase
    have hratio : 0 <= t ^ 50 / L := by positivity
    simpa only [add_zero] using (show 1 <= 1 + t ^ 50 / L by linarith)))

/-- Linear upper bound for the endpoint factor on its strict domain. -/
theorem dimensionOneRosserSecondEndpointFactor_le_linear
    {t : Real} (ht : 1 < t) :
    dimensionOneRosserSecondEndpointFactor t <= 1 - 2 / (3 * t) := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  let y : Real := 1 / t
  let x : Real := 1 - y
  let z : Real := 1 - 2 * y / 3
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hyOne : y < 1 := by
    dsimp [y]
    exact (div_lt_one ht0).2 ht
  have hx0 : 0 <= x := by dsimp [x]; linarith
  have hcube : (x ^ (2 / 3 : Real)) ^ 3 = x ^ 2 := by
    rw [<- Real.rpow_mul_natCast hx0 (2 / 3 : Real) 3]
    norm_num [Real.rpow_natCast]
  have hpoly : x ^ 2 <= z ^ 3 := by
    dsimp [x, z]
    nlinarith [mul_nonneg (sq_nonneg y) (by linarith : 0 <= 9 - 8 * y)]
  rw [dimensionOneRosserSecondEndpointFactor_eq_rpow ht]
  have hroot : x ^ (2 / 3 : Real) <= z := by
    apply ((show Odd 3 by decide).pow_le_pow).mp
    rw [hcube]
    exact hpoly
  convert hroot using 1
  dsimp [x, z, y]
  field_simp

/-- Linear lower bound for the endpoint factor on its strict domain. -/
theorem linear_le_dimensionOneRosserSecondEndpointFactor
    {t : Real} (ht : 1 < t) :
    1 - 1 / t <= dimensionOneRosserSecondEndpointFactor t := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hbase0 : 0 <= 1 - 1 / t := by
    rw [sub_nonneg, div_le_one ht0]
    exact ht.le
  have hbaseOne : 1 - 1 / t <= 1 := by
    linarith [one_div_pos.mpr ht0]
  rw [dimensionOneRosserSecondEndpointFactor_eq_rpow ht]
  exact Real.self_le_rpow_of_le_one hbase0 hbaseOne (by norm_num)

end PrimesRestrictedDigits
