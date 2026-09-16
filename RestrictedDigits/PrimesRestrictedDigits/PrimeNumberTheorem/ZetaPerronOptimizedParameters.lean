import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaZeroFree

/-!
# Optimized parameters for the zeta Perron contour

This makes the contour-height choice in `MONTGOMERY-VAUGHAN-MNT-I`,
Chapter 6, Theorem 6.9, p. 181 explicit for the project's quarter-width
zero-free contour.
-/

namespace PrimesRestrictedDigits

/-- The logarithmic threshold needed by the optimized contour height. -/
noncomputable def zetaPerronLogThreshold (c : Real) : Real :=
  max 1 (8 * Real.log 4 ^ 2 / c)

/-- The height balancing the Perron and shifted-contour errors. -/
noncomputable def zetaPerronHeight (c x : Real) : Real :=
  Real.exp (Real.sqrt ((c / 8) * Real.log x))

/-- Half of the optimized height exponent, retained after log-square
absorption. -/
noncomputable def zetaPerronDecay (c : Real) : Real :=
  Real.sqrt (c / 8) / 2

/-- The optimized logarithmic threshold is at least one. -/
theorem one_le_zetaPerronLogThreshold (c : Real) :
    1 <= zetaPerronLogThreshold c := by
  exact le_max_left _ _

/-- A positive zero-free constant gives a positive optimized decay rate. -/
theorem zetaPerronDecay_pos
    {c : Real} (hc : 0 < c) :
    0 < zetaPerronDecay c := by
  rw [zetaPerronDecay]
  exact div_pos (Real.sqrt_pos.2 (div_pos hc (by norm_num))) (by norm_num)

/-- Above the logarithmic threshold, the optimized height lies in the range
accepted by the Perron and contour estimates. -/
theorem zetaPerronHeight_bounds
    {c x : Real} (hc : IsRiemannZetaZeroFreeConstant c)
    (hx : 0 < x)
    (hLarge : zetaPerronLogThreshold c <= Real.log x) :
    4 <= zetaPerronHeight c x ∧ zetaPerronHeight c x <= x := by
  let L : Real := Real.log x
  let u : Real := Real.sqrt ((c / 8) * L)
  have hLOne : 1 <= L :=
    (one_le_zetaPerronLogThreshold c).trans hLarge
  have hLNonneg : 0 <= L := zero_le_one.trans hLOne
  have hThreshold : 8 * Real.log 4 ^ 2 / c <= L :=
    (le_max_right 1 (8 * Real.log 4 ^ 2 / c)).trans hLarge
  have hcDivNonneg : 0 <= c / 8 := div_nonneg hc.1.le (by norm_num)
  have hArgNonneg : 0 <= (c / 8) * L :=
    mul_nonneg hcDivNonneg hLNonneg
  have huNonneg : 0 <= u := Real.sqrt_nonneg _
  have huSq : u ^ 2 = (c / 8) * L := by
    dsimp [u]
    rw [Real.sq_sqrt hArgNonneg]
  have hLogFourNonneg : 0 <= Real.log 4 :=
    Real.log_nonneg (by norm_num)
  have hLogFourSqLe : Real.log 4 ^ 2 <= (c / 8) * L := by
    calc
      Real.log 4 ^ 2 = (c / 8) * (8 * Real.log 4 ^ 2 / c) := by
        field_simp [hc.1.ne']
      _ <= (c / 8) * L :=
        mul_le_mul_of_nonneg_left hThreshold hcDivNonneg
  have hLogFourLe : Real.log 4 <= u := by
    nlinarith
  have hcDivLeL : c / 8 <= L := by
    nlinarith [hc.2.1]
  have hArgLe : (c / 8) * L <= L ^ 2 := by
    calc
      (c / 8) * L <= L * L :=
        mul_le_mul_of_nonneg_right hcDivLeL hLNonneg
      _ = L ^ 2 := by ring
  have huLe : u <= L := by
    nlinarith
  constructor
  · calc
      4 = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      _ <= Real.exp u := Real.exp_le_exp.mpr hLogFourLe
      _ = zetaPerronHeight c x := by rfl
  · calc
      zetaPerronHeight c x = Real.exp u := by rfl
      _ <= Real.exp L := Real.exp_le_exp.mpr huLe
      _ = x := by
        dsimp [L]
        exact Real.exp_log hx

/-- The logarithm on the shifted contour is at most twice the optimized
height exponent. -/
theorem log_zetaPerronHeight_add_four_le
    {c x : Real} (hc : IsRiemannZetaZeroFreeConstant c)
    (hx : 0 < x)
    (hLarge : zetaPerronLogThreshold c <= Real.log x) :
    Real.log (zetaPerronHeight c x + 4) <=
      2 * Real.sqrt ((c / 8) * Real.log x) := by
  let T : Real := zetaPerronHeight c x
  let u : Real := Real.sqrt ((c / 8) * Real.log x)
  have hT : 4 <= T := (zetaPerronHeight_bounds hc hx hLarge).1
  have hTPos : 0 < T := by linarith
  have hProduct : T + 4 <= T * T := by nlinarith
  calc
    Real.log (zetaPerronHeight c x + 4) = Real.log (T + 4) := by rfl
    _ <= Real.log (T * T) := Real.log_le_log (by linarith) hProduct
    _ = 2 * u := by
      rw [Real.log_mul hTPos.ne' hTPos.ne']
      simp only [T, zetaPerronHeight, Real.log_exp]
      dsimp [u]
      ring
    _ = 2 * Real.sqrt ((c / 8) * Real.log x) := by rfl

/-- The optimized height has twice the retained exponential decay rate. -/
theorem zetaPerronHeight_eq_exp_two_mul_decay_sqrt_log
    {c x : Real} (hx : 1 <= x) :
    zetaPerronHeight c x =
      Real.exp
        (2 * zetaPerronDecay c * Real.sqrt (Real.log x)) := by
  have hLogNonneg : 0 <= Real.log x := Real.log_nonneg hx
  rw [zetaPerronHeight, Real.sqrt_mul' (c / 8) hLogNonneg]
  dsimp [zetaPerronDecay]
  congr 1
  ring

end PrimesRestrictedDigits
