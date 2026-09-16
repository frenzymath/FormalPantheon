import PrimesRestrictedDigits.BasicEstimates.BuchstabFunction

/-!
# Elementary bounds for Buchstab's function

This file proves the weak bounds following Eq. (7.39) in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 7, p. 216.
-/

open MeasureTheory

namespace PrimesRestrictedDigits

/-- A finite approximant lies between one half and one on its covering interval. -/
theorem buchstabApprox_mem_Icc (n : Nat) {u : Real}
    (h1 : 1 <= u) (hu : u <= (n : Real) + 2) :
    buchstabApprox n u ∈ Set.Icc (1 / 2 : Real) 1 := by
  induction n generalizing u with
  | zero =>
      norm_num at hu
      rw [buchstabApprox_zero]
      constructor
      · simpa only [one_div] using
          (one_div_le_one_div_of_le (by linarith : 0 < u) hu)
      · simpa only [one_div, inv_one] using
          (one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) h1)
  | succ n ih =>
      by_cases h2 : u <= 2
      · rw [buchstabApprox_of_le_two (n + 1) h2]
        constructor
        · simpa only [one_div] using
            (one_div_le_one_div_of_le (by linarith : 0 < u) h2)
        · simpa only [one_div, inv_one] using
            (one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) h1)
      · have hgt : 2 < u := lt_of_not_ge h2
        rw [buchstabApprox_succ, if_neg h2]
        push_cast at hu
        have hInt : IntervalIntegrable (buchstabApprox n) volume 1 (u - 1) := by
          apply ContinuousOn.intervalIntegrable
          apply (continuousOn_buchstabApprox n).mono
          intro v hv
          rw [Set.uIcc_of_le (by linarith : (1 : Real) <= u - 1)] at hv
          exact zero_lt_one.trans_le hv.1
        have hLower : (u - 2) / 2 <=
            ∫ v in (1 : Real)..u - 1, buchstabApprox n v := by
          calc
            (u - 2) / 2 = ∫ _v in (1 : Real)..u - 1, (1 / 2 : Real) := by
              simp [intervalIntegral.integral_const]
              ring
            _ <= ∫ v in (1 : Real)..u - 1, buchstabApprox n v := by
              apply intervalIntegral.integral_mono_on (by linarith)
                intervalIntegrable_const hInt
              intro v hv
              exact (ih hv.1 (by linarith [hv.2])).1
        have hUpper : (∫ v in (1 : Real)..u - 1, buchstabApprox n v) <=
            u - 2 := by
          calc
            (∫ v in (1 : Real)..u - 1, buchstabApprox n v) <=
                ∫ _v in (1 : Real)..u - 1, (1 : Real) := by
              apply intervalIntegral.integral_mono_on (by linarith)
                hInt intervalIntegrable_const
              intro v hv
              exact (ih hv.1 (by linarith [hv.2])).2
            _ = u - 2 := by
              simp [intervalIntegral.integral_const]
              ring
        constructor
        · rw [le_div_iff₀ (by linarith)]
          linarith
        · rw [div_le_iff₀ (by linarith)]
          linarith

/-- The canonical Buchstab function lies between one half and one. -/
theorem buchstabFunction_mem_Icc {u : Real} (h1 : 1 <= u) :
    buchstabFunction u ∈ Set.Icc (1 / 2 : Real) 1 := by
  rw [buchstabFunction]
  exact buchstabApprox_mem_Icc (buchstabStage u) h1
    (le_buchstabStage_add_two u)

theorem buchstabFunction_pos {u : Real} (h1 : 1 <= u) :
    0 < buchstabFunction u :=
  (by norm_num : (0 : Real) < 1 / 2).trans_le
    (buchstabFunction_mem_Icc h1).1

end PrimesRestrictedDigits
