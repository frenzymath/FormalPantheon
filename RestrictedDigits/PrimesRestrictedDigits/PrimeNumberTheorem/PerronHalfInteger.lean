import PrimesRestrictedDigits.PrimeNumberTheorem.PerronFinite

/-!
# Half-integer finite Perron cutoff

This specializes the finite Perron theorem to the strict cutoff used in the proof of published
Proposition 9.3: `x = X - 1/2`, `sigma = 1/log X`, and `T = X^4`. It repairs the false squared
normalization in the source by reusing the project's correctly normalized one-variable
integral.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The half-integer cutoff has no starred endpoint: its Perron weight is the
strict natural cutoff. -/
theorem perronWeight_nat_sub_half
    {X n : Nat} (_hX : 1 <= X) :
    perronWeight ((X : Real) - 1 / 2) n =
      if n < X then 1 else 0 := by
  by_cases hn : n < X
  · rw [if_pos hn]
    apply perronWeight_eq_one_of_lt
    have hcast : (n : Real) + 1 <= X := by
      exact_mod_cast (Nat.succ_le_iff.mpr hn)
    linarith
  · rw [if_neg hn]
    apply perronWeight_eq_zero_of_lt
    have hcast : (X : Real) <= n := by
      exact_mod_cast (Nat.le_of_not_gt hn)
    linarith

/-- Every integer is at distance at least one half from `X-1/2`. -/
theorem one_half_le_abs_nat_sub_half_sub_nat
    (X n : Nat) :
    (1 / 2 : Real) <= abs ((X : Real) - 1 / 2 - (n : Real)) := by
  by_cases hn : n < X
  · have hcast : (n : Real) + 1 <= X := by
      exact_mod_cast (Nat.succ_le_iff.mpr hn)
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hcast : (X : Real) <= n := by
      exact_mod_cast (Nat.le_of_not_gt hn)
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- The half-integer specialization removes the near-diagonal singularity
and gains three powers of the ambient scale. -/
theorem perronNearError_nat_sub_half_le
    {X n : Nat} (hX : 4 <= X) (_hn : 0 < n) :
    perronNearError ((X : Real) - 1 / 2) ((X : Real) ^ 4) n <=
      2 / ((X : Real) ^ 3) := by
  have hXPos : (0 : Real) < X := by positivity
  have hdistance := one_half_le_abs_nat_sub_half_sub_nat X n
  rw [perronNearError]
  split_ifs with hrange
  · calc
      min 1 (((X : Real) - 1 / 2) /
          ((X : Real) ^ 4 *
            abs ((X : Real) - 1 / 2 - (n : Real)))) <=
          ((X : Real) - 1 / 2) /
            ((X : Real) ^ 4 *
              abs ((X : Real) - 1 / 2 - (n : Real))) :=
        min_le_right _ _
      _ <= (X : Real) /
          ((X : Real) ^ 4 *
            abs ((X : Real) - 1 / 2 - (n : Real))) := by
        exact div_le_div_of_nonneg_right (by linarith)
          (mul_nonneg (by positivity) (abs_nonneg _))
      _ <= (X : Real) / ((X : Real) ^ 4 * (1 / 2 : Real)) := by
        exact div_le_div_of_nonneg_left hXPos.le (by positivity)
          (mul_le_mul_of_nonneg_left hdistance (by positivity))
      _ = 2 / ((X : Real) ^ 3) := by
        field_simp
  · positivity

/-- The finite half-integer near error is controlled by the unweighted
coefficient norm mass. -/
theorem finitePerronNearError_nat_sub_half_le
    {X : Nat} (hX : 4 <= X)
    {S : Finset Nat} {c : Nat -> Complex}
    (hS : forall n, n ∈ S -> 0 < n) :
    finitePerronNearError S c ((X : Real) - 1 / 2)
        ((X : Real) ^ 4) <=
      (2 / ((X : Real) ^ 3)) * (∑ n ∈ S, ‖c n‖) := by
  rw [finitePerronNearError]
  calc
    (∑ n ∈ S, ‖c n‖ *
        perronNearError ((X : Real) - 1 / 2) ((X : Real) ^ 4) n) <=
        ∑ n ∈ S, ‖c n‖ * (2 / ((X : Real) ^ 3)) := by
      apply Finset.sum_le_sum
      intro n hnS
      exact mul_le_mul_of_nonneg_left
        (perronNearError_nat_sub_half_le hX (hS n hnS)) (norm_nonneg _)
    _ = (2 / ((X : Real) ^ 3)) * (∑ n ∈ S, ‖c n‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hnS
      ring

/-- On positive support and a nonnegative vertical line, the weighted
Dirichlet coefficient mass is at most the raw norm mass. -/
theorem finitePerronCoefficientMass_le_normSum
    {S : Finset Nat} {c : Nat -> Complex} {sigma : Real}
    (hsigma : 0 <= sigma) (hS : forall n, n ∈ S -> 0 < n) :
    finitePerronCoefficientMass S c sigma <=
      ∑ n ∈ S, ‖c n‖ := by
  rw [finitePerronCoefficientMass]
  apply Finset.sum_le_sum
  intro n hnS
  have hnOne : (1 : Real) <= n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (hS n hnS).ne')
  exact div_le_self (norm_nonneg _) (Real.one_le_rpow hnOne hsigma)

/-- The repaired finite Perron estimate at the half-integer strict cutoff.
The coefficient `20` is `2*2` from the near term plus `16` from the
ratio-power term. -/
theorem norm_sum_lt_sub_halfIntegerPerronIntegral_le
    {X : Nat} (hX : 4 <= X)
    {S : Finset Nat} {c : Nat -> Complex}
    (hS : forall n, n ∈ S -> 0 < n) :
    ‖(∑ n ∈ S,
        ((if n < X then 1 else 0 : Real) : Complex) * c n) -
      finitePerronIntegral S c ((X : Real) - 1 / 2)
        (Real.log (X : Real))⁻¹ ((X : Real) ^ 4)‖ <=
      20 * (∑ n ∈ S, ‖c n‖) / ((X : Real) ^ 3) := by
  let mass : Real := ∑ n ∈ S, ‖c n‖
  have hXpos : (0 : Real) < X := by positivity
  have hcutoffPos : (0 : Real) < (X : Real) - 1 / 2 := by
    have hXR : (4 : Real) <= (X : Real) := by exact_mod_cast hX
    linarith
  have hTPos : (0 : Real) < (X : Real) ^ 4 := by positivity
  have hlogOne : (1 : Real) <= Real.log (X : Real) := by
    apply (Real.le_log_iff_exp_le hXpos).2
    exact Real.exp_one_lt_three.le.trans <|
      (show (3 : Real) <= (X : Real) by
        exact_mod_cast (show 3 <= X by omega))
  have hlogPos : 0 < Real.log (X : Real) :=
    lt_of_lt_of_le zero_lt_one hlogOne
  have hsigmaPos : 0 < (Real.log (X : Real))⁻¹ := inv_pos.mpr hlogPos
  have hsigmaOne : (Real.log (X : Real))⁻¹ <= 1 := by
    simpa only [one_div] using
      (one_div_le hlogPos zero_lt_one).2 (by simpa using hlogOne)
  have hsigmaTwo : (Real.log (X : Real))⁻¹ <= 2 :=
    hsigmaOne.trans (by norm_num)
  have hmain := norm_sum_sub_finitePerronIntegral_le
    (S := S) (a := c) (x := (X : Real) - 1 / 2)
    (sigma := (Real.log (X : Real))⁻¹) (T := (X : Real) ^ 4)
    hS hcutoffPos hsigmaPos hsigmaTwo hTPos
  simp_rw [perronWeight_nat_sub_half (X := X) (by omega)] at hmain
  have hnear : finitePerronNearError S c ((X : Real) - 1 / 2)
      ((X : Real) ^ 4) <= (2 / ((X : Real) ^ 3)) * mass := by
    simpa only [mass] using finitePerronNearError_nat_sub_half_le hX hS
  have hcoeff : finitePerronCoefficientMass S c
      (Real.log (X : Real))⁻¹ <= mass := by
    simpa only [mass] using
      finitePerronCoefficientMass_le_normSum hsigmaPos.le hS
  have hmassNonneg : 0 <= mass := by
    dsimp only [mass]
    positivity
  have hcoeffNonneg : 0 <= finitePerronCoefficientMass S c
      (Real.log (X : Real))⁻¹ := by
    rw [finitePerronCoefficientMass]
    positivity
  have hcutoffPower :
      ((X : Real) - 1 / 2) ^ (Real.log (X : Real))⁻¹ <=
        (X : Real) := by
    calc
      ((X : Real) - 1 / 2) ^ (Real.log (X : Real))⁻¹ <=
          (X : Real) ^ (Real.log (X : Real))⁻¹ :=
        Real.rpow_le_rpow hcutoffPos.le (by norm_num) hsigmaPos.le
      _ <= Real.exp 1 := Real.rpow_inv_log_le_exp_one
      _ <= (X : Real) := Real.exp_one_lt_three.le.trans <|
        (show (3 : Real) <= (X : Real) by
          exact_mod_cast (show 3 <= X by omega))
  have hratio : 16 *
      (((X : Real) - 1 / 2) ^ (Real.log (X : Real))⁻¹) /
        ((X : Real) ^ 4) <= 16 / ((X : Real) ^ 3) := by
    calc
      16 * (((X : Real) - 1 / 2) ^
            (Real.log (X : Real))⁻¹) / ((X : Real) ^ 4) <=
          16 * (X : Real) / ((X : Real) ^ 4) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcutoffPower (by norm_num))
          (by positivity)
      _ = 16 / ((X : Real) ^ 3) := by
        field_simp [hXpos.ne']
  have hratioMass :
      (16 * (((X : Real) - 1 / 2) ^
          (Real.log (X : Real))⁻¹) / ((X : Real) ^ 4)) *
          finitePerronCoefficientMass S c
            (Real.log (X : Real))⁻¹ <=
        (16 / ((X : Real) ^ 3)) * mass := by
    calc
      (16 * (((X : Real) - 1 / 2) ^
          (Real.log (X : Real))⁻¹) / ((X : Real) ^ 4)) *
          finitePerronCoefficientMass S c
            (Real.log (X : Real))⁻¹ <=
        (16 / ((X : Real) ^ 3)) *
          finitePerronCoefficientMass S c
            (Real.log (X : Real))⁻¹ :=
        mul_le_mul_of_nonneg_right hratio hcoeffNonneg
      _ <= (16 / ((X : Real) ^ 3)) * mass :=
        mul_le_mul_of_nonneg_left hcoeff (by positivity)
  exact hmain.trans <| calc
    2 * finitePerronNearError S c ((X : Real) - 1 / 2)
          ((X : Real) ^ 4) +
        (16 * (((X : Real) - 1 / 2) ^
          (Real.log (X : Real))⁻¹) / ((X : Real) ^ 4)) *
          finitePerronCoefficientMass S c
            (Real.log (X : Real))⁻¹ <=
      2 * ((2 / ((X : Real) ^ 3)) * mass) +
        (16 / ((X : Real) ^ 3)) * mass :=
      add_le_add (mul_le_mul_of_nonneg_left hnear (by norm_num)) hratioMass
    _ = 20 * (∑ n ∈ S, ‖c n‖) / ((X : Real) ^ 3) := by
      dsimp only [mass]
      field_simp [hXpos.ne']
      ring

end

end PrimesRestrictedDigits
