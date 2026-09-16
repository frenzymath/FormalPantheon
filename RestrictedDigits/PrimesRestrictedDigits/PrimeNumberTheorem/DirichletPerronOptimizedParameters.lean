import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaZeroFree

/-!
# Optimized parameters for the Dirichlet Perron contour

This records the square-root-logarithmic height chosen in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Theorem 11.16, pp. 378--379, with an
explicit threshold for the height range suppressed in the source.
-/

namespace PrimesRestrictedDigits

/-- Half of the source's optimized height exponent, retained after absorbing
two logarithmic powers. -/
noncomputable def dirichletPerronDecay (c : Real) : Real :=
  c / 20

/-- The height selected in the proof of Theorem 11.16. -/
noncomputable def dirichletPerronHeight (c x : Real) : Real :=
  Real.exp ((c / 10) * Real.sqrt (Real.log x))

/-- A logarithmic threshold ensuring that the optimized height is admissible. -/
noncomputable def dirichletPerronLogThreshold (c : Real) : Real :=
  max 1 (((10 * Real.log 4) / c) ^ 2)

/-- The optimized logarithmic threshold is at least one. -/
theorem one_le_dirichletPerronLogThreshold (c : Real) :
    1 <= dirichletPerronLogThreshold c := by
  exact le_max_left _ _

/-- A positive zero-free constant gives a positive retained decay rate. -/
theorem dirichletPerronDecay_pos
    {c : Real} (hc : 0 < c) :
    0 < dirichletPerronDecay c := by
  exact div_pos hc (by norm_num)

/-- Above the explicit threshold, the source's height lies between four and
the cutoff. -/
theorem dirichletPerronHeight_bounds
    {c x : Real} (hc : IsRiemannZetaZeroFreeConstant c)
    (hx : 0 < x)
    (hLarge : dirichletPerronLogThreshold c <= Real.log x) :
    4 <= dirichletPerronHeight c x ∧
      dirichletPerronHeight c x <= x := by
  let ell : Real := Real.log x
  let s : Real := Real.sqrt ell
  have hEllOne : 1 <= ell :=
    (one_le_dirichletPerronLogThreshold c).trans hLarge
  have hEllNonneg : 0 <= ell := zero_le_one.trans hEllOne
  have hsNonneg : 0 <= s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hsSq : s ^ 2 = ell := by
    dsimp [s]
    exact Real.sq_sqrt hEllNonneg
  have hThreshold : ((10 * Real.log 4) / c) ^ 2 <= ell :=
    (le_max_right 1 (((10 * Real.log 4) / c) ^ 2)).trans hLarge
  have hRatioLe : (10 * Real.log 4) / c <= s := by
    dsimp [s]
    exact Real.le_sqrt_of_sq_le hThreshold
  have hLogFourLe : Real.log 4 <= (c / 10) * s := by
    have hcTenNonneg : 0 <= c / 10 := (div_pos hc.1 (by norm_num)).le
    calc
      Real.log 4 = (c / 10) * ((10 * Real.log 4) / c) := by
        field_simp [hc.1.ne']
      _ <= (c / 10) * s :=
        mul_le_mul_of_nonneg_left hRatioLe hcTenNonneg
  have hsLeEll : s <= ell := by
    apply (Real.sqrt_le_iff).2
    constructor
    · exact hEllNonneg
    · nlinarith
  have hcTenthLeOne : c / 10 <= 1 := by
    nlinarith [hc.2.1]
  have hExponentLe : (c / 10) * s <= ell := by
    calc
      (c / 10) * s <= 1 * s :=
        mul_le_mul_of_nonneg_right hcTenthLeOne hsNonneg
      _ <= ell := by simpa using hsLeEll
  constructor
  · calc
      4 = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      _ <= Real.exp ((c / 10) * s) := Real.exp_le_exp.mpr hLogFourLe
      _ = dirichletPerronHeight c x := by rfl
  · calc
      dirichletPerronHeight c x =
          Real.exp ((c / 10) * s) := by rfl
      _ <= Real.exp ell := Real.exp_le_exp.mpr hExponentLe
      _ = x := by
        dsimp [ell]
        exact Real.exp_log hx

/-- The height exponent is twice the retained decay exponent. -/
theorem dirichletPerronHeight_eq_exp_two_mul_decay_sqrt_log
    {c x : Real} :
    dirichletPerronHeight c x =
      Real.exp
        (2 * dirichletPerronDecay c * Real.sqrt (Real.log x)) := by
  rw [dirichletPerronHeight, dirichletPerronDecay]
  congr 1
  ring

end PrimesRestrictedDigits
