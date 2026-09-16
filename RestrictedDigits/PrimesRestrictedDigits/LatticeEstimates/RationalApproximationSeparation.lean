import PrimesRestrictedDigits.LatticeEstimates.RationalApproximationBands

/-!
# Cross separation of rational approximations

The integer cross difference replaces the invalid best-approximation step in the printed proof
of Lemma 14.2.
-/

namespace PrimesRestrictedDigits

/-- Cross difference between `b/q` and `c/r`. -/
def rationalApproximationCrossDifference
    (b c : Int) (q r : Nat) : Int :=
  b * (r : Int) - c * (q : Int)

theorem cast_rationalApproximationCrossDifference
    (b c : Int) (q r : Nat) (hq : 0 < q) (hr : 0 < r) :
    (rationalApproximationCrossDifference b c q r : Real) =
      (q : Real) * (r : Real) *
        ((b : Real) / (q : Real) - (c : Real) / (r : Real)) := by
  unfold rationalApproximationCrossDifference
  norm_num only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  field_simp [hq.ne', hr.ne']


theorem abs_rationalApproximationCrossDifference_le
    (x : Real) (b c : Int) (q r : Nat) (hq : 0 < q) (hr : 0 < r) :
    |(rationalApproximationCrossDifference b c q r : Real)| <=
      (q : Real) * (r : Real) *
        (|x - (b : Real) / (q : Real)| +
          |x - (c : Real) / (r : Real)|) := by
  rw [cast_rationalApproximationCrossDifference b c q r hq hr, abs_mul]
  rw [abs_of_nonneg (by positivity :
    (0 : Real) <= (q : Real) * (r : Real))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    |(b : Real) / (q : Real) - (c : Real) / (r : Real)| =
        |(x - (c : Real) / (r : Real)) -
          (x - (b : Real) / (q : Real))| := by
          congr 1
          ring
    _ <= |x - (c : Real) / (r : Real)| +
        |x - (b : Real) / (q : Real)| := abs_sub _ _
    _ = |x - (b : Real) / (q : Real)| +
        |x - (c : Real) / (r : Real)| := add_comm _ _

theorem sourceDenominator_dvd_of_crossDifference_eq_zero
    {b c : Int} {q r : Nat} (hcoprime : c.natAbs.Coprime r)
    (hzero : rationalApproximationCrossDifference b c q r = 0) :
    r ∣ q := by
  have hcross : b * (r : Int) = c * (q : Int) := by
    exact sub_eq_zero.mp hzero
  have habs := congrArg Int.natAbs hcross
  have hnat : b.natAbs * r = c.natAbs * q := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using habs
  have hdvd : r ∣ q * c.natAbs := by
    refine ⟨b.natAbs, ?_⟩
    calc
      q * c.natAbs = c.natAbs * q := Nat.mul_comm _ _
      _ = b.natAbs * r := hnat.symm
      _ = r * b.natAbs := Nat.mul_comm _ _
  exact hcoprime.symm.dvd_of_dvd_mul_right hdvd

theorem div_eq_div_of_crossDifference_eq_zero
    {b c : Int} {q r : Nat} (hq : 0 < q) (hr : 0 < r)
    (hzero : rationalApproximationCrossDifference b c q r = 0) :
    (b : Real) / (q : Real) = (c : Real) / (r : Real) := by
  have hcross : b * (r : Int) = c * (q : Int) :=
    sub_eq_zero.mp hzero
  field_simp [hq.ne', hr.ne']
  have hcross' : b * (r : Int) = (q : Int) * c := by
    simpa only [mul_comm] using hcross
  exact_mod_cast hcross'

theorem one_le_abs_crossDifference_cast
    {b c : Int} {q r : Nat}
    (hne : rationalApproximationCrossDifference b c q r ≠ 0) :
    (1 : Real) <=
      |(rationalApproximationCrossDifference b c q r : Real)| := by
  have hone := Int.one_le_abs hne
  exact_mod_cast hone

end PrimesRestrictedDigits
