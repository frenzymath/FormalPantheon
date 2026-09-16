import Waring.LargeNumber.FirstScale

/-!
# Main-scale bounds for the circle-method residual targets
-/

set_option autoImplicit false

namespace Waring.LargeNumber

/-- The final source threshold forces the main fifth-root scale above the
analytic threshold used by the corrected Lemmas 7 and 9. -/
theorem ten_pow_oneFiftySeven_le_mainScale
    {N : Nat} (hN : 10 ^ 785 ≤ N) :
    10 ^ 157 ≤ mainScale N := by
  rw [mainScale, Nat.le_nthRoot_iff (by norm_num)]
  calc
    (10 ^ 157) ^ 5 = 10 ^ (157 * 5) := by rw [pow_mul]
    _ = 10 ^ 785 := by norm_num
    _ ≤ N := hN

/-- The input lies strictly below the next fifth power after its natural
fifth root. -/
theorem lt_mainScale_add_one_pow_five (N : Nat) :
    N < (mainScale N + 1) ^ 5 := by
  exact Nat.lt_pow_nthRoot_add_one (by norm_num) N

/-- Removing two terms of size at most `N/4` leaves at least half of the main
scale's fifth power. -/
theorem mainScale_fifth_half_le_sub_sub
    {N u v : Nat} (hu : u ≤ N / 4) (hv : v ≤ N / 4) :
    (mainScale N : Real) ^ 5 / 2 ≤ (N - u - v : Nat) := by
  have huv : u + v ≤ N / 2 := by omega
  have hdouble : N ≤ 2 * (N - u - v) := by omega
  have hp : mainScale N ^ 5 ≤ N := mainScale_pow_five_le N
  have hnat : mainScale N ^ 5 ≤ 2 * (N - u - v) := hp.trans hdouble
  have hreal : (mainScale N : Real) ^ 5 ≤
      2 * ((N - u - v : Nat) : Real) := by
    exact_mod_cast hnat
  linarith

/-- Every residual target remains below the next fifth power. -/
theorem sub_sub_le_mainScale_add_one_pow_five
    (N u v : Nat) :
    N - u - v ≤ (mainScale N + 1) ^ 5 := by
  exact ((Nat.sub_le (N - u) v).trans (Nat.sub_le N u)).trans
    (lt_mainScale_add_one_pow_five N).le

end Waring.LargeNumber
