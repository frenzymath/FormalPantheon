import PrimesRestrictedDigits.LatticeEstimates.DecompositionScales
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Canonical Dirichlet bands for exceptional minor arcs

Disjoint bands for the signed approximation error, including the zero-error
band and the terminal square-root denominator scale.

Source: `MAYNARD-PRD-PUBLISHED`, proof of Proposition 9.3, pp. 191--193.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem one_div_den_mul_den_le_abs_sub_rat
    {r s : Rat} (hrs : r ≠ s) :
    1 / ((r.den : Real) * (s.den : Real)) <=
      abs ((r : Real) - (s : Real)) := by
  have hcross :
      r.num * (s.den : Int) - s.num * (r.den : Int) ≠ 0 := by
    rw [sub_ne_zero]
    exact mt Rat.eq_iff_mul_eq_mul.mpr hrs
  have honeInt : (1 : Int) <=
      |r.num * (s.den : Int) - s.num * (r.den : Int)| :=
    Int.one_le_abs hcross
  have hone : (1 : Real) <=
      abs ((r.num : Real) * (s.den : Real) -
        (s.num : Real) * (r.den : Real)) := by
    exact_mod_cast honeInt
  have hrden : (0 : Real) < r.den := by positivity
  have hsden : (0 : Real) < s.den := by positivity
  rw [Rat.cast_def, Rat.cast_def]
  rw [show (r.num : Real) / (r.den : Real) -
      (s.num : Real) / (s.den : Real) =
      ((r.num : Real) * (s.den : Real) -
        (s.num : Real) * (r.den : Real)) /
          ((r.den : Real) * (s.den : Real)) by field_simp]
  rw [abs_div, abs_of_pos (mul_pos hrden hsden)]
  exact (div_le_div_iff_of_pos_right (mul_pos hrden hsden)).2
    (by simpa using hone)

/-- A nonzero difference between `a / X` and a reduced rational is at least
the reciprocal of the product of their displayed denominators. -/
theorem one_div_nat_mul_den_le_abs_sub_rat
    {X a : Nat} (hX : 0 < X) (r : Rat)
    (hne : (a : Real) / (X : Real) ≠ (r : Real)) :
    1 / ((X : Real) * (r.den : Real)) <=
      abs ((a : Real) / (X : Real) - (r : Real)) := by
  let s : Rat := (a : Rat) / (X : Rat)
  have hcast : (s : Real) = (a : Real) / (X : Real) := by
    simp [s, Rat.cast_div]
  have hsr : s ≠ r := by
    intro h
    apply hne
    rw [← hcast, h]
  have hsdenDvdInt : (s.den : Int) ∣ (X : Int) := by
    dsimp only [s]
    change ((((a : Int) : Rat) / ((X : Int) : Rat)).den : Int) ∣
      (X : Int)
    rw [Rat.intCast_div_eq_divInt]
    exact Rat.den_dvd _ _
  have hsdenDvd : s.den ∣ X := by
    exact_mod_cast hsdenDvdInt
  have hsdenLe : s.den <= X := Nat.le_of_dvd hX hsdenDvd
  have hsdenLeReal : (s.den : Real) <= (X : Real) := by
    exact_mod_cast hsdenLe
  have hrdenPos : (0 : Real) < r.den := by positivity
  have hproduct : (s.den : Real) * (r.den : Real) <=
      (X : Real) * (r.den : Real) :=
    mul_le_mul_of_nonneg_right hsdenLeReal hrdenPos.le
  calc
    1 / ((X : Real) * (r.den : Real)) <=
        1 / ((s.den : Real) * (r.den : Real)) :=
      one_div_le_one_div_of_le (by positivity) hproduct
    _ <= abs ((s : Real) - (r : Real)) :=
      one_div_den_mul_den_le_abs_sub_rat hsr
    _ = abs ((a : Real) / (X : Real) - (r : Real)) := by rw [hcast]

/-- One canonically chosen reduced Dirichlet approximation at denominator
bound `Nat.sqrt X`. The fallback branch is unreachable in the source range. -/
noncomputable def exceptionalDirichletApproximation
    (X : Nat) (a : Fin X) : Rat :=
  if h : 0 < Nat.sqrt X then
    Classical.choose
      (Real.exists_rat_abs_sub_le_and_den_le
        ((a.val : Real) / (X : Real)) h)
  else 0

/-- The signed error of the canonical approximation. -/
noncomputable def exceptionalDirichletError
    (X : Nat) (a : Fin X) : Real :=
  (a.val : Real) / (X : Real) -
    (exceptionalDirichletApproximation X a : Real)

/-- The denominator's factor-ten upper scale, capped at the terminal
Dirichlet scale `sqrt X`. -/
noncomputable def exceptionalDirichletDenominatorScale
    (X : Nat) (a : Fin X) : Real :=
  min
    (factorTenScale (exceptionalDirichletApproximation X a).den : Real)
    (Real.sqrt (X : Real))

/-- The positive error target after shifting all relevant decimal exponents
into the natural range. -/
noncomputable def exceptionalDirichletErrorTarget
    (X : Nat) (a : Fin X) : Real :=
  (X : Real) ^ 2 * abs (exceptionalDirichletError X a)

/-- The repaired error scale: zero for an exact approximation, and otherwise
the canonical upper scale of `X^2 * |nu|`, divided by `X`. -/
noncomputable def exceptionalDirichletErrorScale
    (X : Nat) (a : Fin X) : Real :=
  if exceptionalDirichletError X a = 0 then 0
  else
    (latticePositiveRealFactorTenScale
      (exceptionalDirichletErrorTarget X a) : Real) / (X : Real)

/-- Exact output of the pinned reduced-rational Dirichlet theorem. -/
theorem exceptionalDirichletApproximation_spec
    {X : Nat} (hX : 1 <= X) (a : Fin X) :
    abs (exceptionalDirichletError X a) <=
        1 / (((Nat.sqrt X + 1 : Nat) : Real) *
          (exceptionalDirichletApproximation X a).den) ∧
      (exceptionalDirichletApproximation X a).den <= Nat.sqrt X := by
  have hsqrt : 0 < Nat.sqrt X := Nat.sqrt_pos.2 (by omega)
  rw [exceptionalDirichletError, exceptionalDirichletApproximation,
    dif_pos hsqrt]
  simpa only [Nat.cast_add, Nat.cast_one] using
    Classical.choose_spec
      (Real.exists_rat_abs_sub_le_and_den_le
        ((a.val : Real) / (X : Real)) hsqrt)

/-- The source form of the Dirichlet error, with a real square-root bound. -/
theorem exceptionalDirichletApproximation_error_le
    {X : Nat} (hX : 1 <= X) (a : Fin X) :
    abs (exceptionalDirichletError X a) <=
      1 / (Real.sqrt (X : Real) *
        (exceptionalDirichletApproximation X a).den) := by
  let r := exceptionalDirichletApproximation X a
  have hspec := exceptionalDirichletApproximation_spec hX a
  have hsqrtUpper : Real.sqrt (X : Real) <
      (Nat.sqrt X : Real) + 1 :=
    Real.real_sqrt_lt_nat_sqrt_succ
  have hrden : (0 : Real) < r.den := by positivity
  have hden : Real.sqrt (X : Real) * (r.den : Real) <=
      (((Nat.sqrt X + 1 : Nat) : Real) * (r.den : Real)) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    exact mul_le_mul_of_nonneg_right hsqrtUpper.le hrden.le
  exact hspec.1.trans (one_div_le_one_div_of_le (by positivity) hden)

/-- The capped denominator scale retains every literal source endpoint. -/
theorem exceptionalDirichletDenominatorScale_bounds
    {X : Nat} (hX : 1 <= X) (a : Fin X) :
    ((exceptionalDirichletApproximation X a).den : Real) <=
        exceptionalDirichletDenominatorScale X a ∧
      exceptionalDirichletDenominatorScale X a <
        10 * (exceptionalDirichletApproximation X a).den ∧
      exceptionalDirichletDenominatorScale X a <=
        Real.sqrt (X : Real) := by
  let r := exceptionalDirichletApproximation X a
  have hspec := exceptionalDirichletApproximation_spec hX a
  have hqPos : 0 < r.den := r.den_pos
  have hband := factorTenScale_band r.den hqPos
  have hqNatCast : (r.den : Real) <= (Nat.sqrt X : Real) := by
    exact_mod_cast hspec.2
  have hqSqrt : (r.den : Real) <= Real.sqrt (X : Real) :=
    hqNatCast.trans Real.nat_sqrt_le_real_sqrt
  have hqFactor : (r.den : Real) <=
      (factorTenScale r.den : Real) := hband.2
  have hfactorLt : (factorTenScale r.den : Real) <
      10 * (r.den : Real) := by
    nlinarith [hband.1]
  unfold exceptionalDirichletDenominatorScale
  change _ <= min (factorTenScale r.den : Real)
      (Real.sqrt (X : Real)) ∧
    min (factorTenScale r.den : Real) (Real.sqrt (X : Real)) < _ ∧ _
  exact ⟨le_min hqFactor hqSqrt,
    (min_le_left _ _).trans_lt hfactorLt, min_le_right _ _⟩

/-- A nonzero grid error makes the shifted target strictly larger than one. -/
theorem exceptionalDirichletErrorTarget_gt_one
    {X : Nat} (hX : 4 <= X) (a : Fin X)
    (hne : exceptionalDirichletError X a ≠ 0) :
    1 < exceptionalDirichletErrorTarget X a := by
  let x : Real := X
  let q : Real := (exceptionalDirichletApproximation X a).den
  have hx : 0 < x := by dsimp [x]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hsqrtOne : 1 < Real.sqrt x := by
    have hxOne : (1 : Real) < x := by
      dsimp [x]
      exact_mod_cast (show 1 < X by omega)
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hxOne
  have hqSqrt : q <= Real.sqrt x := by
    have hspec :=
      (exceptionalDirichletApproximation_spec (show 1 <= X by omega) a).2
    have hcast : q <= (Nat.sqrt X : Real) := by
      dsimp [q]
      exact_mod_cast hspec
    exact hcast.trans Real.nat_sqrt_le_real_sqrt
  have hspacing : 1 / (x * q) <=
      abs (exceptionalDirichletError X a) := by
    have hne' : (a.val : Real) / (X : Real) ≠
        (exceptionalDirichletApproximation X a : Real) :=
      sub_ne_zero.mp
        (by simpa only [exceptionalDirichletError] using hne)
    simpa only [x, q, exceptionalDirichletError] using
      one_div_nat_mul_den_le_abs_sub_rat (a := a.val) (by omega)
        (exceptionalDirichletApproximation X a) hne'
  have hsqrtLeDiv : Real.sqrt x <= x / q := by
    rw [le_div_iff₀ hq]
    calc
      Real.sqrt x * q <= Real.sqrt x * Real.sqrt x := by gcongr
      _ = x := Real.mul_self_sqrt hx.le
  have hdivIdentity : x / q = x ^ 2 * (1 / (x * q)) := by
    field_simp
  calc
    1 < Real.sqrt x := hsqrtOne
    _ <= x / q := hsqrtLeDiv
    _ = x ^ 2 * (1 / (x * q)) := hdivIdentity
    _ <= x ^ 2 * abs (exceptionalDirichletError X a) := by gcongr
    _ = exceptionalDirichletErrorTarget X a := by rfl

/-- The shifted target is at most `X^2`, which bounds its natural decimal
index by twice the decimal length. -/
theorem exceptionalDirichletErrorTarget_le_sq
    {X : Nat} (hX : 1 <= X) (a : Fin X) :
    exceptionalDirichletErrorTarget X a <= (X : Real) ^ 2 := by
  have hsqrtOne : (1 : Real) <= Real.sqrt (X : Real) := by simp [hX]
  have hdenOne : (1 : Real) <=
      (exceptionalDirichletApproximation X a).den := by
    exact_mod_cast (exceptionalDirichletApproximation X a).den_pos
  have hproductOne : (1 : Real) <= Real.sqrt (X : Real) *
      (exceptionalDirichletApproximation X a).den := by
    nlinarith
  have hinv : 1 / (Real.sqrt (X : Real) *
      (exceptionalDirichletApproximation X a).den) <= (1 : Real) := by
    simpa only [one_div] using inv_le_one_of_one_le₀ hproductOne
  have herrOne : abs (exceptionalDirichletError X a) <= 1 :=
    (exceptionalDirichletApproximation_error_le hX a).trans hinv
  unfold exceptionalDirichletErrorTarget
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left herrOne (sq_nonneg (X : Real))

end

end PrimesRestrictedDigits
