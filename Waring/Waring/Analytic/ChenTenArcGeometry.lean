import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rational major-arc geometry in Chen's Lemma 10

This file proves the elementary separation and interval-disjointness facts
used for Chen's basic intervals [CHEN1964-EN, p. 1561;
CHEN1964-ZH, p. 728].
-/

namespace Waring.Analytic

noncomputable section

/-- The real number represented by a natural numerator and denominator. -/
def rationalCenter (a q : Nat) : Real :=
  (a : Real) / q

/-- The closed real interval with the given center and radius. -/
def centeredClosedInterval (center radius : Real) : Set Real :=
  Set.Icc (center - radius) (center + radius)

/-- A closed interval of radius `radius` around the rational center `a / q`. -/
def rationalArc (a q : Nat) (radius : Real) : Set Real :=
  centeredClosedInterval (rationalCenter a q) radius

/-- Distinct rational cross-products give the standard reciprocal-product
lower bound for the distance between the two real fractions. -/
theorem one_div_mul_le_abs_nat_div_sub_nat_div
    (a b q r : Nat) (hq : 0 < q) (hr : 0 < r)
    (hcross : a * r ≠ b * q) :
    1 / ((q : Real) * r) ≤
      |(a : Real) / q - (b : Real) / r| := by
  let numerator : Int := (a * r : Nat) - (b * q : Nat)
  have hnumerator : numerator ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hcross
  have honeInt : (1 : Int) ≤ |numerator| := Int.one_le_abs hnumerator
  have honeReal : (1 : Real) ≤ |(numerator : Real)| := by
    rw [← Int.cast_abs]
    exact_mod_cast honeInt
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hrReal : (0 : Real) < r := by exact_mod_cast hr
  have hden : (0 : Real) < (q : Real) * r := mul_pos hqReal hrReal
  have hfraction :
      (a : Real) / q - (b : Real) / r =
        (numerator : Real) / ((q : Real) * r) := by
    dsimp [numerator]
    push_cast
    field_simp
  rw [hfraction, abs_div, abs_of_pos hden]
  exact (div_le_div_iff_of_pos_right hden).2 honeReal

/-- Closed center-radius intervals are disjoint when the sum of the radii is
strictly smaller than the distance between their centers.  No sign assumption
is needed: a negative radius makes the corresponding `Set.Icc` empty. -/
theorem disjoint_centeredClosedInterval_of_add_lt_abs_sub
    (x y rho sigma : Real) (hseparation : rho + sigma < |x - y|) :
    Disjoint (centeredClosedInterval x rho)
      (centeredClosedInterval y sigma) := by
  refine Set.disjoint_left.mpr ?_
  intro t htX htY
  have hxt : |x - t| ≤ rho := by
    apply abs_le.mpr
    constructor <;> dsimp [centeredClosedInterval] at htX <;>
      linarith [htX.1, htX.2]
  have hty : |t - y| ≤ sigma := by
    apply abs_le.mpr
    constructor <;> dsimp [centeredClosedInterval] at htY <;>
      linarith [htY.1, htY.2]
  have htriangle : |x - y| ≤ |x - t| + |t - y| := by
    calc
      |x - y| = |(x - t) + (t - y)| := by ring_nf
      _ ≤ |x - t| + |t - y| := abs_add_le _ _
  have : |x - y| ≤ rho + sigma :=
    htriangle.trans (add_le_add hxt hty)
  exact (not_lt_of_ge this) hseparation

/-- Rational arcs are disjoint if their radii sum to less than the standard
reciprocal-product separation. -/
theorem disjoint_rationalArc_of_add_lt_one_div_mul
    (a b q r : Nat) (rho sigma : Real)
    (hq : 0 < q) (hr : 0 < r) (hcross : a * r ≠ b * q)
    (hwidth : rho + sigma < 1 / ((q : Real) * r)) :
    Disjoint (rationalArc a q rho) (rationalArc b r sigma) := by
  apply disjoint_centeredClosedInterval_of_add_lt_abs_sub
    (rationalCenter a q) (rationalCenter b r) rho sigma
  exact hwidth.trans_le
    (one_div_mul_le_abs_nat_div_sub_nat_div a b q r hq hr hcross)

/-- For radii `1/(q*tau)` and `1/(r*tau)`, the natural condition
`q+r<tau` makes their sum smaller than the rational separation `1/(q*r)`. -/
theorem reciprocal_arc_radii_add_lt_one_div_mul
    (q r : Nat) (tau : Real) (hq : 0 < q) (hr : 0 < r)
    (htau : 0 < tau) (hwidth : (q : Real) + r < tau) :
    1 / ((q : Real) * tau) + 1 / ((r : Real) * tau) <
      1 / ((q : Real) * r) := by
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hrReal : (0 : Real) < r := by exact_mod_cast hr
  have hden : (0 : Real) < (q : Real) * r * tau := by positivity
  calc
    1 / ((q : Real) * tau) + 1 / ((r : Real) * tau) =
        ((q : Real) + r) / ((q : Real) * r * tau) := by
      field_simp
      ring
    _ < tau / ((q : Real) * r * tau) :=
      (div_lt_div_iff_of_pos_right hden).2 hwidth
    _ = 1 / ((q : Real) * r) := by
      field_simp

/-- Closed rational arcs of Chen's reciprocal-radius form are disjoint once
the denominator sum is strictly smaller than the common scale `tau`. -/
theorem disjoint_reciprocalRadiusRationalArcs
    (a b q r : Nat) (tau : Real)
    (hq : 0 < q) (hr : 0 < r) (htau : 0 < tau)
    (hcross : a * r ≠ b * q) (hwidth : (q : Real) + r < tau) :
    Disjoint
      (rationalArc a q (1 / ((q : Real) * tau)))
      (rationalArc b r (1 / ((r : Real) * tau))) := by
  apply disjoint_rationalArc_of_add_lt_one_div_mul
    a b q r _ _ hq hr hcross
  exact reciprocal_arc_radii_add_lt_one_div_mul
    q r tau hq hr htau hwidth

/-- Positive denominator bounds `q^2,r^2 <= P` imply the width inequality
`q+r < 10*P^4` used by Chen's major arcs. -/
theorem denominator_sum_lt_ten_mul_fourth_of_sq_le
    (P q r : Nat) (hP : 0 < P) (hq : 0 < q) (hr : 0 < r)
    (hqSq : (q : Real) ^ 2 ≤ P) (hrSq : (r : Real) ^ 2 ≤ P) :
    (q : Real) + r < 10 * (P : Real) ^ 4 := by
  have hPReal : (0 : Real) < P := by exact_mod_cast hP
  have hPOne : (1 : Real) ≤ P := by exact_mod_cast hP
  have hqOne : (1 : Real) ≤ q := by exact_mod_cast hq
  have hrOne : (1 : Real) ≤ r := by exact_mod_cast hr
  have hqP : (q : Real) ≤ P := by
    calc
      (q : Real) = (q : Real) ^ 1 := by ring
      _ ≤ (q : Real) ^ 2 := pow_le_pow_right₀ hqOne (by decide)
      _ ≤ P := hqSq
  have hrP : (r : Real) ≤ P := by
    calc
      (r : Real) = (r : Real) ^ 1 := by ring
      _ ≤ (r : Real) ^ 2 := pow_le_pow_right₀ hrOne (by decide)
      _ ≤ P := hrSq
  have hPpow : (P : Real) ≤ (P : Real) ^ 4 := by
    calc
      (P : Real) = (P : Real) ^ 1 := by ring
      _ ≤ (P : Real) ^ 4 := pow_le_pow_right₀ hPOne (by decide)
  have hPfourthPos : (0 : Real) < (P : Real) ^ 4 := pow_pos hPReal 4
  calc
    (q : Real) + r ≤ (P : Real) + P := add_le_add hqP hrP
    _ = 2 * (P : Real) := by ring
    _ ≤ 2 * (P : Real) ^ 4 :=
      mul_le_mul_of_nonneg_left hPpow (by positivity)
    _ < 10 * (P : Real) ^ 4 := by linarith

/-- Chen's closed basic arcs are disjoint under squared versions of the
source denominator cutoff. -/
theorem disjoint_chenTenRationalArcs_of_sq_le
    (P a b q r : Nat) (hP : 0 < P) (hq : 0 < q) (hr : 0 < r)
    (hqSq : (q : Real) ^ 2 ≤ P) (hrSq : (r : Real) ^ 2 ≤ P)
    (hcross : a * r ≠ b * q) :
    Disjoint
      (rationalArc a q
        (1 / ((q : Real) * (10 * (P : Real) ^ 4))))
      (rationalArc b r
        (1 / ((r : Real) * (10 * (P : Real) ^ 4)))) := by
  have hPReal : (0 : Real) < P := by exact_mod_cast hP
  apply disjoint_reciprocalRadiusRationalArcs
    a b q r (10 * (P : Real) ^ 4) hq hr (by positivity) hcross
  exact denominator_sum_lt_ten_mul_fourth_of_sq_le
    P q r hP hq hr hqSq hrSq

end

end Waring.Analytic
