import PrimesRestrictedDigits.BasicEstimates.BuchstabRefinedTailBaseD900A
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Global refined Buchstab tail envelope

The refined length-one base interval is propagated to every real argument at
least `13 / 4` using the Buchstab integral recurrence.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

private theorem refinedTailIntervalIntegrable
    {a b : Real} (ha : 1 <= a) (hab : a <= b) :
    IntervalIntegrable buchstabFunction volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_buchstabFunction.mono
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact ha.trans hx.1

private theorem refinedTailSteps :
    forall n : Nat, forall {u : Real}, 13 / 4 <= u ->
      u <= (n : Real) + 17 / 4 ->
      buchstabFunction u <= 281 / 500 := by
  intro n
  induction n with
  | zero =>
      intro u hlo hhi
      apply buchstabFunction_le_refinedTailEnvelope_base hlo
      norm_num at hhi ⊢
      linarith
  | succ n ih =>
      intro u hlo hhi
      by_cases hprev : u <= (n : Real) + 17 / 4
      · exact ih hlo hprev
      · have hnNonneg : (0 : Real) <= n := by positivity
        have huLower : 17 / 4 <= u := by
          norm_num at hprev ⊢
          linarith
        have huUpperPrev : u - 1 <= (n : Real) + 17 / 4 := by
          norm_num at hhi ⊢
          linarith
        have hAUpper : (13 / 4 : Real) <= u - 1 := by
          linarith
        have hIntOneA := refinedTailIntervalIntegrable
          (a := (1 : Real)) (b := 13 / 4) (by norm_num) (by norm_num)
        have hIntAUpper := refinedTailIntervalIntegrable
          (a := (13 / 4 : Real)) (b := u - 1) (by norm_num) hAUpper
        have hsplit := intervalIntegral.integral_add_adjacent_intervals
          hIntOneA hIntAUpper
        have htailInt :
            (∫ v in (13 / 4 : Real)..u - 1, buchstabFunction v) <=
              (281 / 500 : Real) * (u - 17 / 4) := by
          calc
            (∫ v in (13 / 4 : Real)..u - 1, buchstabFunction v) <=
                ∫ _v in (13 / 4 : Real)..u - 1,
                  (281 / 500 : Real) := by
              apply intervalIntegral.integral_mono_on hAUpper
                hIntAUpper intervalIntegrable_const
              intro v hv
              apply ih
              · exact hv.1
              · exact hv.2.trans huUpperPrev
            _ = (281 / 500 : Real) * (u - 17 / 4) := by
              rw [intervalIntegral.integral_const]
              ring_nf
        have hrecU := mul_buchstabFunction_eq
          (by linarith : (2 : Real) <= u)
        have hrecA := mul_buchstabFunction_eq
          (by norm_num : (2 : Real) <= (17 / 4 : Real))
        have hanchor : buchstabFunction (17 / 4) <= 281 / 500 := by
          exact buchstabFunction_le_refinedTailEnvelope_base
            (by norm_num) (by norm_num)
        norm_num at hrecA
        rw [← hsplit] at hrecU
        norm_num at hrecU
        apply (mul_le_mul_iff_of_pos_left
          (by linarith : (0 : Real) < u)).mp
        rw [hrecU]
        have hanchorMul :
            (17 / 4 : Real) * buchstabFunction (17 / 4) <=
              (281 / 500 : Real) * (17 / 4) := by
          simpa [mul_comm] using
            ((mul_le_mul_iff_of_pos_left (by norm_num :
              (0 : Real) < (17 / 4 : Real))).mpr hanchor)
        linarith

theorem buchstabFunction_le_refinedTailEnvelope
    {u : Real} (hu : 13 / 4 <= u) :
    buchstabFunction u <= 281 / 500 := by
  obtain ⟨n, hn⟩ := exists_nat_ge (u - 17 / 4)
  have hnUpper : u <= (n : Real) + 17 / 4 := by
    have := hn
    norm_num at this ⊢
    linarith
  exact refinedTailSteps n hu hnUpper

end
end PrimesRestrictedDigits
