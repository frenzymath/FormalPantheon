import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Interval.Finset.Nat

/-!
# Canonical rational major-arc approximations

This implements the repair of the rational witnesses in `MAYNARD-PRD-PUBLISHED`, pp. 186--189,
and records the finite carrier and signed-offset identities needed by the divisor-denominator
branches.
-/

namespace PrimesRestrictedDigits

/-- A major-arc approximation with the source's real cutoff and closed error. -/
def majorArcRationalApproximation
    (X a : Nat) (Q : Real) (r : Rat) : Prop :=
  abs ((a : Real) / (X : Real) - (r : Real)) <= Q / (X : Real) ∧
    (r.den : Real) <= Q

/-- Existence of a canonically reduced rational major-arc witness. -/
def majorArcRawApproximation (X a : Nat) (Q : Real) : Prop :=
  ∃ r : Rat, majorArcRationalApproximation X a Q r

/-- The equivalent positive-denominator integer formulation. -/
def majorArcRawIntegerApproximation (X a : Nat) (Q : Real) : Prop :=
  ∃ b : Int, ∃ q : Nat, 0 < q ∧ (q : Real) <= Q ∧
    abs ((a : Real) / (X : Real) - (b : Real) / (q : Real)) <=
      Q / (X : Real)

/-- A finite rational carrier for approximations with a bounded real cutoff. -/
noncomputable def majorArcRationalCarrier (N : Nat) : Finset Rat :=
  ((Finset.Icc (-(N : Int)) (2 * (N : Int))).product
      (Finset.Icc 1 N)).image fun bq =>
    (bq.1 : Rat) / (bq.2 : Rat)

/-- The integral displacement from a divisor-denominator approximation. -/
def majorArcSignedOffset (X a : Nat) (r : Rat) : Int :=
  (a : Int) - r.num * (X / r.den : Nat)

private theorem normalizedRational_den_le
    {b : Int} {q : Nat} (hq : 0 < q) :
    ((b : Rat) / (q : Rat)).den <= q := by
  have hden : ((b : Rat) / (q : Rat)).den ∣ q := by
    have hdenInt := Rat.den_dvd b (q : Int)
    exact_mod_cast hdenInt
  exact Nat.le_of_dvd hq hden

theorem majorArcRawApproximation_iff_integer
    {X a : Nat} {Q : Real} :
    majorArcRawApproximation X a Q ↔
      majorArcRawIntegerApproximation X a Q := by
  constructor
  · rintro ⟨r, happrox, hden⟩
    refine ⟨r.num, r.den, r.den_pos, hden, ?_⟩
    have hcast : (r : Real) = (r.num : Real) / (r.den : Real) := by
      rw [Rat.cast_def]
    rw [hcast] at happrox
    exact happrox
  · rintro ⟨b, q, hq, hqQ, happrox⟩
    let r : Rat := (b : Rat) / (q : Rat)
    have hden : r.den <= q := normalizedRational_den_le hq
    have hcast : (r : Real) = (b : Real) / (q : Real) := by
      dsimp [r]
      rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    refine ⟨r, ?_, ?_⟩
    · rw [hcast]
      exact happrox
    · have hdenReal : (r.den : Real) <= (q : Real) := by
        exact_mod_cast hden
      exact hdenReal.trans hqQ

theorem majorArcRationalCarrier_complete
    {X a : Nat} {Q : Real} {r : Rat}
    (hX : 0 < X) (hQX : Q <= X)
    (ha : a < X) (hr : majorArcRationalApproximation X a Q r) :
    r ∈ majorArcRationalCarrier (Nat.ceil Q) := by
  let N := Nat.ceil Q
  change r ∈ ((Finset.Icc (-(N : Int)) (2 * (N : Int))).product
      (Finset.Icc 1 N)).image _
  have hXReal : (0 : Real) < X := by
    exact_mod_cast hX
  have haReal : (a : Real) < X := by
    exact_mod_cast ha
  have hfrequencyNonneg : (0 : Real) <= (a : Real) / X := by
    positivity
  have hfrequencyLtOne : (a : Real) / X < 1 :=
    (div_lt_iff₀ hXReal).2 (by linarith)
  have htolerance : Q / X <= 1 :=
    (div_le_iff₀ hXReal).2 (by simpa using hQX)
  have happrox := hr.1
  change abs ((a : Real) / (X : Real) - (r : Real)) <=
    Q / (X : Real) at happrox
  have hrLower : (-1 : Real) <= (r : Real) := by
    rcases abs_le.mp happrox with ⟨hlower, _⟩
    linarith
  have hrUpper : (r : Real) <= 2 := by
    rcases abs_le.mp happrox with ⟨_, hupper⟩
    linarith
  have hdenPos : 0 < r.den := r.den_pos
  have hdenCeil : (r.den : Real) <= (N : Real) :=
    hr.2.trans (Nat.le_ceil Q)
  have hnumDivDen : (r.num : Real) / (r.den : Real) = (r : Real) := by
    exact_mod_cast r.num_div_den
  have hnumLowerReal : -(r.den : Real) <= (r.num : Real) := by
    have hdivision : (-1 : Real) <= (r.num : Real) / (r.den : Real) := by
      rw [hnumDivDen]
      exact hrLower
    have hdenReal : (0 : Real) < r.den := by
      exact_mod_cast hdenPos
    have hscaled := (le_div_iff₀ hdenReal).mp hdivision
    nlinarith
  have hnumUpperReal : (r.num : Real) <= 2 * (r.den : Real) := by
    have hdivision : (r.num : Real) / (r.den : Real) <= (2 : Real) := by
      rw [hnumDivDen]
      exact hrUpper
    have hdenReal : (0 : Real) < r.den := by
      exact_mod_cast hdenPos
    have hscaled := (div_le_iff₀ hdenReal).mp hdivision
    nlinarith
  have hnumLower : -(N : Int) <= r.num := by
    have hnumLowerDen : -(r.den : Int) <= r.num := by
      exact_mod_cast hnumLowerReal
    have hdenCeilInt : (r.den : Int) <= N := by
      exact_mod_cast hdenCeil
    omega
  have hnumUpper : r.num <= 2 * (N : Int) := by
    have hnumUpperDen : r.num <= 2 * (r.den : Int) := by
      exact_mod_cast hnumUpperReal
    have hdenCeilInt : (r.den : Int) <= N := by
      exact_mod_cast hdenCeil
    omega
  have hdenMem : r.den ∈ Finset.Icc 1 N := by
    rw [Finset.mem_Icc]
    refine ⟨Nat.one_le_iff_ne_zero.mpr hdenPos.ne', ?_⟩
    exact_mod_cast hdenCeil
  have hnumMem : r.num ∈ Finset.Icc (-(N : Int)) (2 * (N : Int)) := by
    exact Finset.mem_Icc.mpr ⟨hnumLower, hnumUpper⟩
  apply Finset.mem_image.mpr
  refine ⟨(r.num, r.den), Finset.mem_product.mpr ⟨hnumMem, hdenMem⟩, ?_⟩
  exact r.num_div_den

theorem majorArcSignedOffset_identity
    {X a : Nat} {r : Rat} (hX : 0 < X) (hden : r.den ∣ X) :
    (a : Rat) / (X : Rat) =
      r + (majorArcSignedOffset X a r : Rat) / (X : Rat) := by
  have hquotient : ((X / r.den : Nat) : Rat) =
      (X : Rat) / (r.den : Rat) :=
    Rat.natCast_div X r.den hden
  have hoffset : ((majorArcSignedOffset X a r : Int) : Rat) =
      (a : Rat) - (r.num : Rat) * ((X / r.den : Nat) : Rat) := by
    change (((a : Int) - r.num * (X / r.den : Nat) : Int) : Rat) = _
    rw [Int.cast_sub, Int.cast_mul]
    rfl
  calc
    (a : Rat) / (X : Rat) =
        (r.num : Rat) / (r.den : Rat) +
          ((a : Rat) - (r.num : Rat) *
            ((X / r.den : Nat) : Rat)) / (X : Rat) := by
      rw [hquotient]
      field_simp
      ring
    _ = (r.num : Rat) / (r.den : Rat) +
        (majorArcSignedOffset X a r : Rat) / (X : Rat) := by
      rw [hoffset]
    _ = r + (majorArcSignedOffset X a r : Rat) / (X : Rat) := by
      rw [Rat.num_div_den]

theorem majorArcSignedOffset_eq_zero_iff
    {X a : Nat} {r : Rat} (hX : 0 < X) (hden : r.den ∣ X) :
    majorArcSignedOffset X a r = 0 ↔
      (a : Rat) / (X : Rat) = r := by
  have hXNonzero : (X : Rat) ≠ 0 := by
    exact_mod_cast hX.ne'
  constructor
  · intro hoffset
    calc
      (a : Rat) / (X : Rat) = r +
          (majorArcSignedOffset X a r : Rat) / (X : Rat) :=
        majorArcSignedOffset_identity hX hden
      _ = r := by simp [hoffset]
  · intro hequal
    have hidentity := majorArcSignedOffset_identity (a := a) hX hden
    rw [hequal] at hidentity
    have hquotient : (majorArcSignedOffset X a r : Rat) / (X : Rat) = 0 := by
      linarith
    have hoffset : (majorArcSignedOffset X a r : Rat) = 0 :=
      (div_eq_zero_iff.mp hquotient).resolve_right hXNonzero
    exact_mod_cast hoffset

theorem majorArcSignedOffset_ne_zero_iff
    {X a : Nat} {r : Rat} (hX : 0 < X) (hden : r.den ∣ X) :
    majorArcSignedOffset X a r ≠ 0 ↔
      (a : Rat) / (X : Rat) ≠ r := by
  exact not_congr (majorArcSignedOffset_eq_zero_iff (a := a) hX hden)

theorem majorArcRatExact_iff_realExact
    {X a : Nat} {r : Rat} :
    (a : Rat) / (X : Rat) = r ↔
      (a : Real) / (X : Real) = (r : Real) := by
  constructor
  · intro hequal
    have hcast := congrArg (fun z : Rat => (z : Real)) hequal
    simpa only [Rat.cast_div, Rat.cast_natCast] using hcast
  · intro hequal
    apply Rat.cast_injective (α := Real)
    simpa only [Rat.cast_div, Rat.cast_natCast] using hequal

theorem abs_majorArcSignedOffset_le
    {X a : Nat} {Q : Real} {r : Rat}
    (hX : 0 < X) (hden : r.den ∣ X)
    (hr : majorArcRationalApproximation X a Q r) :
    abs (majorArcSignedOffset X a r : Real) <= Q := by
  have hidentityRat := majorArcSignedOffset_identity (a := a) hX hden
  have hidentityCast := congrArg (fun z : Rat => (z : Real)) hidentityRat
  have hidentity : (a : Real) / (X : Real) =
      (r : Real) + (majorArcSignedOffset X a r : Real) / (X : Real) := by
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_add,
      Rat.cast_intCast] using hidentityCast
  have hdifference : (a : Real) / (X : Real) - (r : Real) =
      (majorArcSignedOffset X a r : Real) / (X : Real) := by
    linarith
  have hquotient : abs ((majorArcSignedOffset X a r : Real) / (X : Real)) <=
      Q / (X : Real) := by
    rw [← hdifference]
    exact hr.1
  have hXReal : (0 : Real) < X := by
    exact_mod_cast hX
  rw [abs_div, abs_of_pos hXReal] at hquotient
  exact (div_le_div_iff_of_pos_right hXReal).mp hquotient

end PrimesRestrictedDigits
