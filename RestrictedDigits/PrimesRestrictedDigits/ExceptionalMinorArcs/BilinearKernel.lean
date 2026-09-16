import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearIntervals
import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearPhase
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Geometric phase sums and the zero-safe bilinear kernel

This proves the finite geometric-progression estimate used after Cauchy in repaired Lemma
13.1.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

theorem majorArcPhase_add_int_eq
    (x : Real) (z : Int) :
    majorArcPhase (x + z) = majorArcPhase x := by
  rw [majorArcPhase, majorArcPhase]
  have harg : (((2 * Real.pi * (x + z) : Real) : Complex) * Complex.I) =
      (((2 * Real.pi * x : Real) : Complex) * Complex.I) +
        (z : Complex) * (2 * (Real.pi : Complex) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The denominator in a geometric phase sum is bounded below by four times
the distance to the nearest integer. -/
theorem four_mul_nearestIntegerDistance_le_norm_phase_sub_one
    (theta : Real) :
    4 * nearestIntegerDistance theta <= ‖majorArcPhase theta - 1‖ := by
  let r : Real := theta - (round theta : Int)
  have hr : |r| <= 1 / 2 := by
    simpa [r] using abs_sub_round theta
  have hphase : majorArcPhase theta = majorArcPhase r := by
    have hdecomp : theta = r + (round theta : Int) := by
      dsimp only [r]
      ring
    rw [hdecomp, majorArcPhase_add_int_eq]
  have harg : |Real.pi * r| <= Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin harg
  have hnorm : ‖majorArcPhase r - 1‖ =
      2 * |Real.sin (Real.pi * r)| := by
    rw [majorArcPhase]
    have hexp :
        Complex.exp
            (((2 * Real.pi * r : Real) : Complex) * Complex.I) =
          Complex.exp (Complex.I * (2 * Real.pi * r : Real)) := by
      congr 1
      push_cast
      ring
    rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
    congr 1
    ring_nf
  rw [hphase, hnorm, nearestIntegerDistance]
  change 4 * |r| <= 2 * |Real.sin (Real.pi * r)|
  have hscaled : 2 * |r| <= |Real.sin (Real.pi * r)| := by
    calc
      2 * |r| = 2 / Real.pi * |Real.pi * r| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        field_simp [Real.pi_ne_zero]
      _ <= |Real.sin (Real.pi * r)| := hsin
  linarith

/-- Trivial cardinality bound for a phase sum over the source interval. -/
theorem norm_phase_sum_sourceFactorTenNaturalInterval_le_card
    (M theta : Real) :
    ‖∑ m ∈ sourceFactorTenNaturalInterval M,
        majorArcPhase ((m : Real) * theta)‖ <=
      (sourceFactorTenNaturalInterval M).card := by
  calc
    ‖∑ m ∈ sourceFactorTenNaturalInterval M,
        majorArcPhase ((m : Real) * theta)‖ <=
        ∑ m ∈ sourceFactorTenNaturalInterval M,
          ‖majorArcPhase ((m : Real) * theta)‖ := norm_sum_le _ _
    _ = (sourceFactorTenNaturalInterval M).card := by simp

/-- Away from an integral phase, the shifted geometric sum is bounded by the
inverse nearest-integer distance. -/
theorem norm_phase_sum_sourceFactorTenNaturalInterval_le_inv
    {M theta : Real} (hM : 0 <= M)
    (hdist : 0 < nearestIntegerDistance theta) :
    ‖∑ m ∈ sourceFactorTenNaturalInterval M,
        majorArcPhase ((m : Real) * theta)‖ <=
      (nearestIntegerDistance theta)⁻¹ := by
  let lo : Nat := Nat.floor (M / 10) + 1
  let hi : Nat := Nat.floor M + 1
  have hlohi : lo <= hi := by
    dsimp only [lo, hi]
    apply Nat.add_le_add_right
    apply Nat.floor_mono
    linarith
  let z : Complex := majorArcPhase theta
  have hsum :
      (∑ m ∈ sourceFactorTenNaturalInterval M,
          majorArcPhase ((m : Real) * theta)) =
        ∑ m ∈ Finset.Ico lo hi, z ^ m := by
    rw [sourceFactorTenNaturalInterval,
      ← Finset.Ico_add_one_add_one_eq_Ioc]
    apply Finset.sum_congr rfl
    intro m _
    exact majorArcPhase_nat_mul theta m
  have hgeom := geom_sum_Ico_mul z hlohi
  have hnumpow : ‖z ^ hi - z ^ lo‖ <= 2 := by
    calc
      ‖z ^ hi - z ^ lo‖ <= ‖z ^ hi‖ + ‖z ^ lo‖ := norm_sub_le _ _
      _ = 2 := by simp [z]; norm_num
  have hproduct :
      ‖∑ m ∈ Finset.Ico lo hi, z ^ m‖ * ‖z - 1‖ <= 2 := by
    rw [← norm_mul, hgeom]
    exact hnumpow
  have hdenom :
      4 * nearestIntegerDistance theta <= ‖z - 1‖ := by
    simpa only [z] using
      four_mul_nearestIntegerDistance_le_norm_phase_sub_one theta
  have hsumNonneg : 0 <= ‖∑ m ∈ Finset.Ico lo hi, z ^ m‖ := norm_nonneg _
  have hmul :
      ‖∑ m ∈ Finset.Ico lo hi, z ^ m‖ *
          (4 * nearestIntegerDistance theta) <= 2 := by
    calc
      ‖∑ m ∈ Finset.Ico lo hi, z ^ m‖ *
          (4 * nearestIntegerDistance theta) <=
          ‖∑ m ∈ Finset.Ico lo hi, z ^ m‖ * ‖z - 1‖ := by
        exact mul_le_mul_of_nonneg_left hdenom hsumNonneg
      _ <= 2 := hproduct
  rw [hsum]
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hdist).2
  nlinarith

/-- A source interval of length at most `1000*L` is bounded by a fixed
multiple of the zero-safe capped kernel. -/
theorem norm_phase_sum_sourceFactorTenNaturalInterval_le_kernel
    {L M theta : Real} (hL : 0 < L) (hM : 0 <= M)
    (hML : M <= 1000 * L) :
    ‖∑ m ∈ sourceFactorTenNaturalInterval M,
        majorArcPhase ((m : Real) * theta)‖ <=
      1000 * cappedNearestIntegerKernel L theta := by
  let d := nearestIntegerDistance theta
  by_cases hsmall : L * d <= 1
  · rw [cappedNearestIntegerKernel_eq_cap hsmall]
    calc
      ‖∑ m ∈ sourceFactorTenNaturalInterval M,
          majorArcPhase ((m : Real) * theta)‖ <=
          (sourceFactorTenNaturalInterval M).card :=
        norm_phase_sum_sourceFactorTenNaturalInterval_le_card M theta
      _ <= M := card_sourceFactorTenNaturalInterval_le hM
      _ <= 1000 * L := hML
  · have hlarge : 1 <= L * d := (lt_of_not_ge hsmall).le
    have hd : 0 < d := by
      by_contra hdnot
      have hd0 : d = 0 := le_antisymm (le_of_not_gt hdnot)
        (nearestIntegerDistance_nonneg theta)
      rw [hd0, mul_zero] at hlarge
      norm_num at hlarge
    rw [cappedNearestIntegerKernel_eq_inv hL hlarge]
    calc
      ‖∑ m ∈ sourceFactorTenNaturalInterval M,
          majorArcPhase ((m : Real) * theta)‖ <= d⁻¹ :=
        norm_phase_sum_sourceFactorTenNaturalInterval_le_inv hM hd
      _ <= 1000 * d⁻¹ := by
        exact le_mul_of_one_le_left (inv_nonneg.mpr hd.le) (by norm_num)

end PrimesRestrictedDigits
