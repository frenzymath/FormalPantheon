import PrimesRestrictedDigits.PrimeNumberTheorem.PerronFiniteIntegral
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronOneTerm

/-!
# The finite truncated Perron estimate

This file sums the uniform one-term estimate and obtains an explicit form of
`MONTGOMERY-VAUGHAN-MNT-I`, Corollary 5.3, p. 140, for finite complex
coefficients.
-/

namespace PrimesRestrictedDigits

/-- The finite strict near-diagonal error, before multiplication by its
absolute comparison constant. -/
noncomputable def finitePerronNearError
    (S : Finset Nat) (a : Nat -> Complex) (x T : Real) : Real :=
  ∑ n ∈ S, ‖a n‖ * perronNearError x T n

/-- The finite absolute Dirichlet coefficient mass on a real vertical line. -/
noncomputable def finitePerronCoefficientMass
    (S : Finset Nat) (a : Nat -> Complex) (sigma : Real) : Real :=
  ∑ n ∈ S, ‖a n‖ / (n : Real) ^ sigma

/-- The finite starred sum differs from its vertical integral by an explicit
near error and ratio-power coefficient mass. -/
theorem norm_sum_sub_finitePerronIntegral_le
    {S : Finset Nat} {a : Nat -> Complex} {x sigma T : Real}
    (hS : forall n, n ∈ S -> 0 < n) (hx : 0 < x)
    (hsigma : 0 < sigma) (hsigma2 : sigma <= 2) (hT : 0 < T) :
    ‖(∑ n ∈ S, (perronWeight x n : Complex) * a n) -
        finitePerronIntegral S a x sigma T‖ <=
      2 * finitePerronNearError S a x T +
        16 * x ^ sigma / T * finitePerronCoefficientMass S a sigma := by
  rw [finitePerronIntegral_eq_sum_perronKernel hS hx hsigma]
  have hdiff :
      (∑ n ∈ S, (perronWeight x n : Complex) * a n) -
          (∑ n ∈ S, a n * perronKernel (x / (n : Real)) sigma T) =
        ∑ n ∈ S, -(a n *
          (perronKernel (x / (n : Real)) sigma T -
            (perronWeight x n : Complex))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hnS
    ring
  rw [hdiff]
  calc
    ‖∑ n ∈ S, -(a n *
        (perronKernel (x / (n : Real)) sigma T -
          (perronWeight x n : Complex)))‖ <=
        ∑ n ∈ S, ‖-(a n *
          (perronKernel (x / (n : Real)) sigma T -
            (perronWeight x n : Complex)))‖ := norm_sum_le _ _
    _ = ∑ n ∈ S, ‖a n‖ *
        ‖perronKernel (x / (n : Real)) sigma T -
          (perronWeight x n : Complex)‖ := by
      apply Finset.sum_congr rfl
      intro n hnS
      rw [norm_neg, norm_mul]
    _ <= ∑ n ∈ S, ‖a n‖ *
        (2 * perronNearError x T n +
          16 * (x / (n : Real)) ^ sigma / T) := by
      apply Finset.sum_le_sum
      intro n hnS
      exact mul_le_mul_of_nonneg_left
        (norm_perronKernel_div_natCast_sub_perronWeight_le_uniform
          hx (hS n hnS) hsigma hsigma2 hT) (norm_nonneg _)
    _ = 2 * finitePerronNearError S a x T +
        16 * x ^ sigma / T * finitePerronCoefficientMass S a sigma := by
      rw [finitePerronNearError, finitePerronCoefficientMass]
      calc
        (∑ n ∈ S, ‖a n‖ *
          (2 * perronNearError x T n +
            16 * (x / (n : Real)) ^ sigma / T)) =
            ∑ n ∈ S, (2 * (‖a n‖ * perronNearError x T n) +
              (16 * x ^ sigma / T) *
                (‖a n‖ / (n : Real) ^ sigma)) := by
          apply Finset.sum_congr rfl
          intro n hnS
          have hn' : (0 : Real) < n := by exact_mod_cast hS n hnS
          rw [Real.div_rpow hx.le hn'.le]
          ring
        _ = 2 * (∑ n ∈ S, ‖a n‖ * perronNearError x T n) +
            (16 * x ^ sigma / T) *
              (∑ n ∈ S, ‖a n‖ / (n : Real) ^ sigma) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- The finite Corollary 5.3 estimate with one explicit absolute constant. -/
theorem norm_sum_sub_finitePerronIntegral_le_source
    {S : Finset Nat} {a : Nat -> Complex} {x sigma T : Real}
    (hS : forall n, n ∈ S -> 0 < n) (hx : 0 < x)
    (hsigma : 0 < sigma) (hsigma2 : sigma <= 2) (hT : 0 < T) :
    ‖(∑ n ∈ S, (perronWeight x n : Complex) * a n) -
        finitePerronIntegral S a x sigma T‖ <=
      16 * (finitePerronNearError S a x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          finitePerronCoefficientMass S a sigma) := by
  have hmain := norm_sum_sub_finitePerronIntegral_le
    (S := S) (a := a) (x := x) (sigma := sigma) (T := T)
    hS hx hsigma hsigma2 hT
  have hnear : 0 <= finitePerronNearError S a x T := by
    rw [finitePerronNearError]
    apply Finset.sum_nonneg
    intro n hnS
    apply mul_nonneg (norm_nonneg _)
    rw [perronNearError]
    split_ifs with h
    · apply le_min
      · norm_num
      · have hdiff : 0 < |x - (n : Real)| :=
          abs_pos.mpr (sub_ne_zero.mpr h.2.2)
        positivity
    · exact le_rfl
  have hmass : 0 <= finitePerronCoefficientMass S a sigma := by
    rw [finitePerronCoefficientMass]
    apply Finset.sum_nonneg
    intro n hnS
    exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hnearScale : 2 * finitePerronNearError S a x T <=
      16 * finitePerronNearError S a x T :=
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
      16 * x ^ sigma / T * finitePerronCoefficientMass S a sigma <=
        16 * (((4 : Real) ^ sigma + x ^ sigma) / T) *
          finitePerronCoefficientMass S a sigma :=
    mul_le_mul_of_nonneg_right hglobalCoeff hmass
  exact hmain.trans <| calc
    2 * finitePerronNearError S a x T +
        16 * x ^ sigma / T * finitePerronCoefficientMass S a sigma <=
      16 * finitePerronNearError S a x T +
        16 * (((4 : Real) ^ sigma + x ^ sigma) / T) *
          finitePerronCoefficientMass S a sigma :=
      add_le_add hnearScale hglobalScale
    _ = 16 * (finitePerronNearError S a x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          finitePerronCoefficientMass S a sigma) := by ring

/-- The finite truncated Perron theorem with its absolute constant quantified
before all support, coefficient, cutoff, line, and height parameters. -/
theorem finite_truncatedPerron_bound :
    exists C : Real, 0 < C ∧
      forall (S : Finset Nat) (a : Nat -> Complex) (x sigma T : Real),
        (forall n, n ∈ S -> 0 < n) ->
        0 < x -> 0 < sigma -> sigma <= 2 -> 0 < T ->
        ‖(∑ n ∈ S, (perronWeight x n : Complex) * a n) -
            finitePerronIntegral S a x sigma T‖ <=
          C * (finitePerronNearError S a x T +
            ((4 : Real) ^ sigma + x ^ sigma) / T *
              finitePerronCoefficientMass S a sigma) := by
  refine ⟨16, by norm_num, ?_⟩
  intro S a x sigma T hS hx hsigma hsigma2 hT
  exact norm_sum_sub_finitePerronIntegral_le_source
    hS hx hsigma hsigma2 hT

end PrimesRestrictedDigits
