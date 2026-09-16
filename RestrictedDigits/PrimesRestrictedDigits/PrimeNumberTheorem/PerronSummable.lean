import PrimesRestrictedDigits.PrimeNumberTheorem.PerronSummableIntegral

/-!
# The summable truncated Perron estimate

This file proves the countable L-series form of
`MONTGOMERY-VAUGHAN-MNT-I`, Corollary 5.3, p. 140, with an explicit absolute
constant and the exact starred endpoint convention.
-/

namespace PrimesRestrictedDigits

private theorem norm_perronStarredTerm_sub_kernelTerm_le
    {a : Nat -> Complex} {x sigma T : Real} (hx : 0 < x)
    (hsigma : 0 < sigma) (hsigma2 : sigma <= 2) (hT : 0 < T)
    (n : Nat) :
    ‖perronStarredTerm a x n - perronKernelTerm a x sigma T n‖ <=
      2 * perronNearErrorTerm a x T n +
        (16 * x ^ sigma / T) * perronCoefficientMassTerm a sigma n := by
  by_cases hn : n = 0
  · subst n
    simp [perronStarredTerm, perronKernelTerm, perronNearErrorTerm,
      perronCoefficientMassTerm]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnR : (0 : Real) < n := by exact_mod_cast hnpos
    have hone :=
      norm_perronKernel_div_natCast_sub_perronWeight_le_uniform
        (x := x) (sigma := sigma) (T := T) (n := n)
        hx hnpos hsigma hsigma2 hT
    have heq :
        ‖perronStarredTerm a x n - perronKernelTerm a x sigma T n‖ =
          ‖a n‖ * ‖perronKernel (x / (n : Real)) sigma T -
            (perronWeight x n : Complex)‖ := by
      rw [perronStarredTerm, perronKernelTerm, if_neg hn, if_neg hn]
      rw [show (perronWeight x n : Complex) * a n -
          a n * perronKernel (x / (n : Real)) sigma T =
          -(a n * (perronKernel (x / (n : Real)) sigma T -
            (perronWeight x n : Complex))) by ring,
        norm_neg, norm_mul]
    rw [heq]
    calc
      ‖a n‖ * ‖perronKernel (x / (n : Real)) sigma T -
          (perronWeight x n : Complex)‖ <=
          ‖a n‖ * (2 * perronNearError x T n +
            16 * (x / (n : Real)) ^ sigma / T) :=
        mul_le_mul_of_nonneg_left hone (norm_nonneg _)
      _ = 2 * perronNearErrorTerm a x T n +
          (16 * x ^ sigma / T) * perronCoefficientMassTerm a sigma n := by
        rw [perronNearErrorTerm, perronCoefficientMassTerm, if_neg hn,
          if_neg hn, Real.div_rpow hx.le hnR.le]
        ring

/-- The countable starred sum differs from its vertical integral by the
separated near-diagonal and coefficient-mass errors. -/
theorem norm_starredPerronSum_sub_truncatedPerronIntegral_le_raw
    {a : Nat -> Complex} {x sigma T : Real}
    (hsum : LSeriesSummable a (sigma : Complex))
    (hx : 0 < x) (hsigma : 0 < sigma) (hsigma2 : sigma <= 2)
    (hT : 0 < T) :
    ‖starredPerronSum a x - truncatedPerronIntegral a x sigma T‖ <=
      2 * perronNearErrorSum a x T +
        (16 * x ^ sigma / T) * perronCoefficientMass a sigma := by
  rw [starredPerronSum, perronNearErrorSum, perronCoefficientMass,
    truncatedPerronIntegral_eq_tsum_perronKernel hsum hx hsigma]
  have hstar : Summable (perronStarredTerm a x) :=
    summable_perronStarredTerm a x
  have hkernel : Summable (perronKernelTerm a x sigma T) :=
    (hasSum_perronKernelTerm_truncatedPerronIntegral hsum hx hsigma).summable
  have hnear : Summable (perronNearErrorTerm a x T) :=
    summable_perronNearErrorTerm a x T
  have hmass : Summable (perronCoefficientMassTerm a sigma) :=
    LSeriesSummable.summable_perronCoefficientMassTerm hsum
  have hbound : Summable (fun n =>
      2 * perronNearErrorTerm a x T n +
        (16 * x ^ sigma / T) * perronCoefficientMassTerm a sigma n) :=
    (hnear.mul_left 2).add (hmass.mul_left (16 * x ^ sigma / T))
  have hnorm : Summable (fun n =>
      ‖perronStarredTerm a x n - perronKernelTerm a x sigma T n‖) :=
    hbound.of_norm_bounded fun n => by
      simpa only [norm_norm] using
        norm_perronStarredTerm_sub_kernelTerm_le hx hsigma hsigma2 hT n
  rw [← hstar.tsum_sub hkernel]
  calc
    ‖∑' n, (perronStarredTerm a x n -
        perronKernelTerm a x sigma T n)‖ <=
        ∑' n, ‖perronStarredTerm a x n -
          perronKernelTerm a x sigma T n‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ <= ∑' n, (2 * perronNearErrorTerm a x T n +
        (16 * x ^ sigma / T) *
          perronCoefficientMassTerm a sigma n) :=
      hnorm.tsum_le_tsum
        (norm_perronStarredTerm_sub_kernelTerm_le hx hsigma hsigma2 hT)
        hbound
    _ = 2 * (∑' n, perronNearErrorTerm a x T n) +
        (16 * x ^ sigma / T) *
          ∑' n, perronCoefficientMassTerm a sigma n := by
      rw [(hnear.mul_left 2).tsum_add
        (hmass.mul_left (16 * x ^ sigma / T)),
        tsum_mul_left, tsum_mul_left]

/-- The countable Corollary 5.3 estimate with the explicit absolute constant
used by the finite theorem. -/
theorem norm_starredPerronSum_sub_truncatedPerronIntegral_le
    {a : Nat -> Complex} {x sigma T : Real}
    (hsum : LSeriesSummable a (sigma : Complex))
    (hx : 0 < x) (hsigma : 0 < sigma) (hsigma2 : sigma <= 2)
    (hT : 0 < T) :
    ‖starredPerronSum a x - truncatedPerronIntegral a x sigma T‖ <=
      16 * (perronNearErrorSum a x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          perronCoefficientMass a sigma) := by
  have hmain := norm_starredPerronSum_sub_truncatedPerronIntegral_le_raw
    hsum hx hsigma hsigma2 hT
  have hnear : 0 <= perronNearErrorSum a x T := by
    rw [perronNearErrorSum]
    exact tsum_nonneg (perronNearErrorTerm_nonneg hx hT)
  have hmass : 0 <= perronCoefficientMass a sigma := by
    rw [perronCoefficientMass]
    exact tsum_nonneg perronCoefficientMassTerm_nonneg
  have hnearScale : 2 * perronNearErrorSum a x T <=
      16 * perronNearErrorSum a x T :=
    mul_le_mul_of_nonneg_right (by norm_num) hnear
  have hglobalCoeff : 16 * x ^ sigma / T <=
      16 * (((4 : Real) ^ sigma + x ^ sigma) / T) := by
    have hp : x ^ sigma <= (4 : Real) ^ sigma + x ^ sigma :=
      le_add_of_nonneg_left (Real.rpow_nonneg (by norm_num) _)
    calc
      16 * x ^ sigma / T = 16 * (x ^ sigma / T) := by ring
      _ <= 16 * (((4 : Real) ^ sigma + x ^ sigma) / T) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hp hT.le) (by norm_num)
  have hglobalScale :
      (16 * x ^ sigma / T) * perronCoefficientMass a sigma <=
        16 * (((4 : Real) ^ sigma + x ^ sigma) / T) *
          perronCoefficientMass a sigma :=
    mul_le_mul_of_nonneg_right hglobalCoeff hmass
  exact hmain.trans <| calc
    2 * perronNearErrorSum a x T +
        (16 * x ^ sigma / T) * perronCoefficientMass a sigma <=
      16 * perronNearErrorSum a x T +
        16 * (((4 : Real) ^ sigma + x ^ sigma) / T) *
          perronCoefficientMass a sigma :=
      add_le_add hnearScale hglobalScale
    _ = 16 * (perronNearErrorSum a x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          perronCoefficientMass a sigma) := by ring

/-- The summable truncated Perron theorem, with its absolute constant chosen
before the coefficient function, cutoff, line, and height parameters. -/
theorem truncatedPerron_bound :
    exists C : Real, 0 < C ∧
      forall (a : Nat -> Complex) (x sigma T : Real),
        LSeriesSummable a (sigma : Complex) ->
        0 < x -> 0 < sigma -> sigma <= 2 -> 0 < T ->
        ‖starredPerronSum a x - truncatedPerronIntegral a x sigma T‖ <=
          C * (perronNearErrorSum a x T +
            ((4 : Real) ^ sigma + x ^ sigma) / T *
              perronCoefficientMass a sigma) := by
  refine ⟨16, by norm_num, ?_⟩
  intro a x sigma T hsum hx hsigma hsigma2 hT
  exact norm_starredPerronSum_sub_truncatedPerronIntegral_le
    hsum hx hsigma hsigma2 hT

end PrimesRestrictedDigits
