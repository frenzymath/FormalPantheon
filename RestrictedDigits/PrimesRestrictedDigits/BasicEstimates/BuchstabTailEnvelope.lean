import PrimesRestrictedDigits.BasicEstimates.BuchstabMiddleEnvelope
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Buchstab tail envelope

The 32-cell rational recurrence gives the literal tail constant used by Section 6.
Source: Montgomery--Vaughan Eq. (7.39), with the Section 6 branch bounds.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

private def sectionSixTailX (i : Nat) : Real :=
  (i + 1 : Real) / (i + 65)

private def sectionSixTailLogUpper (i : Nat) : Real :=
  2 * ((∑ k ∈ Finset.range 6,
      sectionSixTailX i ^ (2 * k + 1) / (2 * k + 1)) +
    sectionSixTailX i ^ 13 / (1 - sectionSixTailX i ^ 2))

private def sectionSixTailMajorant (i : Nat) : Real :=
  (1 + sectionSixTailLogUpper i) / (2 + (i : Real) / 32)

private def sectionSixTailCumulative (i : Nat) : Real :=
  ∑ j ∈ Finset.range i, sectionSixTailMajorant j / 32

private theorem sectionSixTailLogEndpoint_le (i : Nat) :
    Real.log (((i : Real) + 33) / 32) <=
      sectionSixTailLogUpper i := by
  have hxNonneg : 0 <= sectionSixTailX i := by
    dsimp [sectionSixTailX]
    positivity
  have hxOne : sectionSixTailX i < 1 := by
    dsimp [sectionSixTailX]
    rw [div_lt_one]
    · norm_num
    · positivity
  have h := Real.log_div_le_sum_range_add hxNonneg hxOne 6
  have hratio :
      (1 + sectionSixTailX i) / (1 - sectionSixTailX i) =
        ((i : Real) + 33) / 32 := by
    dsimp [sectionSixTailX]
    field_simp
    ring
  rw [hratio] at h
  dsimp [sectionSixTailLogUpper]
  linarith

private theorem sectionSixTailMajorant_nonneg (i : Nat) :
    0 <= sectionSixTailMajorant i := by
  have hx : (1 : Real) <= ((i : Real) + 33) / 32 := by
    rw [le_div_iff₀ (by norm_num : (0 : Real) < 32)]
    have hiNonneg : (0 : Real) <= i := by positivity
    linarith
  have hlog : 0 <= Real.log (((i : Real) + 33) / 32) :=
    Real.log_nonneg hx
  have := sectionSixTailLogEndpoint_le i
  dsimp [sectionSixTailMajorant]
  apply div_nonneg
  · linarith
  · positivity

private theorem sectionSixTailBuchstab_le_majorant
    (i : Nat) (hi : i < 32) {u : Real}
    (huLower : 2 + (i : Real) / 32 <= u)
    (huUpper : u <= 2 + ((i : Real) + 1) / 32) :
    buchstabFunction u <= sectionSixTailMajorant i := by
  have hiNonneg : (0 : Real) <= i := by positivity
  have huTwo : 2 <= u := by linarith
  have huThree : u <= 3 := by
    have hiReal : (i : Real) + 1 <= 32 := by exact_mod_cast hi
    linarith
  have huSubPos : 0 < u - 1 := by linarith
  have hendpoint : u - 1 <= ((i : Real) + 33) / 32 := by linarith
  have hlogMono : Real.log (u - 1) <=
      Real.log (((i : Real) + 33) / 32) :=
    Real.log_le_log huSubPos hendpoint
  have hlog := hlogMono.trans (sectionSixTailLogEndpoint_le i)
  have hnumNonneg : 0 <= 1 + Real.log (u - 1) := by
    have : 0 <= Real.log (u - 1) := Real.log_nonneg (by linarith)
    linarith
  have hupperNonneg : 0 <= 1 + sectionSixTailLogUpper i := by linarith
  have hleftPos : 0 < 2 + (i : Real) / 32 := by positivity
  have huPos : 0 < u := by linarith
  rw [buchstabFunction_eq_one_add_log_sub_one_div huTwo huThree]
  dsimp [sectionSixTailMajorant]
  rw [div_le_iff₀ huPos, div_mul_eq_mul_div,
    le_div_iff₀ hleftPos]
  calc
    (1 + Real.log (u - 1)) * (2 + (i : Real) / 32) <=
        (1 + sectionSixTailLogUpper i) * (2 + (i : Real) / 32) :=
      mul_le_mul_of_nonneg_right (by linarith) hleftPos.le
    _ <= (1 + sectionSixTailLogUpper i) * u :=
      mul_le_mul_of_nonneg_left huLower hupperNonneg

private theorem sectionSixTailBuchstab_intervalIntegrable
    {a b : Real} (ha : 1 <= a) (hab : a <= b) :
    IntervalIntegrable buchstabFunction volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_buchstabFunction.mono
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact ha.trans hx.1

private theorem sectionSixTailCellIntegral_le
    (i : Nat) (hi : i < 32) :
    (∫ u in 2 + (i : Real) / 32..2 + ((i : Real) + 1) / 32,
        buchstabFunction u) <= sectionSixTailMajorant i / 32 := by
  have hab : 2 + (i : Real) / 32 <= 2 + ((i : Real) + 1) / 32 := by
    have hiStep : (i : Real) <= (i : Real) + 1 := by linarith
    simpa [add_comm] using add_le_add_left
      ((div_le_div_iff_of_pos_right (by norm_num : (0 : Real) < 32)).2 hiStep) 2
  have hleftOne : (1 : Real) <= 2 + (i : Real) / 32 := by
    have hiNonneg : (0 : Real) <= i := by positivity
    linarith
  have hint := sectionSixTailBuchstab_intervalIntegrable
    (a := 2 + (i : Real) / 32)
    (b := 2 + ((i : Real) + 1) / 32) hleftOne hab
  calc
    (∫ u in 2 + (i : Real) / 32..2 + ((i : Real) + 1) / 32,
        buchstabFunction u) <=
        ∫ _u in 2 + (i : Real) / 32..2 + ((i : Real) + 1) / 32,
          sectionSixTailMajorant i := by
      apply intervalIntegral.integral_mono_on hab hint intervalIntegrable_const
      intro u hu
      exact sectionSixTailBuchstab_le_majorant i hi hu.1 hu.2
    _ = sectionSixTailMajorant i / 32 := by
      rw [intervalIntegral.integral_const]
      ring

private theorem sectionSixTailPrefixIntegral_le :
    forall i : Nat, i <= 32 ->
      (∫ u in (2 : Real)..2 + (i : Real) / 32, buchstabFunction u) <=
        sectionSixTailCumulative i := by
  intro i hi
  induction i with
  | zero => simp [sectionSixTailCumulative]
  | succ i ih =>
      have hiLt : i < 32 := Nat.lt_of_succ_le hi
      have hiNonneg : (0 : Real) <= i := by positivity
      have hleft : (2 : Real) <= 2 + (i : Real) / 32 := by linarith
      have hmid : 2 + (i : Real) / 32 <=
          2 + ((i : Real) + 1) / 32 := by
        have hiStep : (i : Real) <= (i : Real) + 1 := by linarith
        simpa [add_comm] using add_le_add_left
          ((div_le_div_iff_of_pos_right (by norm_num : (0 : Real) < 32)).2 hiStep) 2
      have hIntLeft := sectionSixTailBuchstab_intervalIntegrable
        (by norm_num : (1 : Real) <= 2) hleft
      have hIntCell := sectionSixTailBuchstab_intervalIntegrable
        (by linarith : (1 : Real) <= 2 + (i : Real) / 32) hmid
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        hIntLeft hIntCell
      rw [Nat.cast_succ]
      rw [← hsplit]
      dsimp [sectionSixTailCumulative]
      rw [Finset.sum_range_succ]
      exact add_le_add (ih (Nat.le_of_succ_le hi))
        (sectionSixTailCellIntegral_le i hiLt)

private theorem sectionSixTailNode_upper (i : Nat) (hi : i <= 32) :
    1 + (0.6931471808 : Real) + sectionSixTailCumulative i <=
      (564383 / 1000000 : Real) * (3 + (i : Real) / 32) := by
  interval_cases i <;>
    norm_num [sectionSixTailCumulative, sectionSixTailMajorant,
      sectionSixTailLogUpper, sectionSixTailX, Finset.sum_range_succ]

private theorem sectionSixTail_integral_buchstab_one_two :
    (∫ u in (1 : Real)..2, buchstabFunction u) = Real.log 2 := by
  calc
    (∫ u in (1 : Real)..2, buchstabFunction u) =
        ∫ u in (1 : Real)..2, u⁻¹ := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (by norm_num : (1 : Real) <= 2)] at hu
      exact buchstabFunction_eq_inv hu.1 hu.2
    _ = Real.log (2 / 1 : Real) :=
      integral_inv_of_pos (by norm_num) (by norm_num)
    _ = Real.log 2 := by norm_num

private theorem sectionSixTailBuchstab_le_base_cell
    (i : Nat) (hi : i < 32) {u : Real}
    (huLower : 3 + (i : Real) / 32 <= u)
    (huUpper : u <= 3 + ((i : Real) + 1) / 32) :
    buchstabFunction u <= 564383 / 1000000 := by
  have hiNonneg : (0 : Real) <= i := by positivity
  have huThree : 3 <= u := by linarith
  have hleft : (2 : Real) <= 2 + (i : Real) / 32 := by linarith
  have hright : 2 + (i : Real) / 32 <= u - 1 := by linarith
  have hpartialInt := sectionSixTailBuchstab_intervalIntegrable
    (by linarith : (1 : Real) <= 2 + (i : Real) / 32) hright
  have hpartial :
      (∫ v in 2 + (i : Real) / 32..u - 1, buchstabFunction v) <=
        sectionSixTailMajorant i *
          (u - (3 + (i : Real) / 32)) := by
    calc
      (∫ v in 2 + (i : Real) / 32..u - 1, buchstabFunction v) <=
          ∫ _v in 2 + (i : Real) / 32..u - 1,
            sectionSixTailMajorant i := by
        apply intervalIntegral.integral_mono_on hright hpartialInt
          intervalIntegrable_const
        intro v hv
        apply sectionSixTailBuchstab_le_majorant i hi hv.1
        linarith [hv.2]
      _ = sectionSixTailMajorant i *
          (u - (3 + (i : Real) / 32)) := by
        rw [intervalIntegral.integral_const]
        ring
  have hprefix := sectionSixTailPrefixIntegral_le i hi.le
  have hIntPrefix := sectionSixTailBuchstab_intervalIntegrable
    (by norm_num : (1 : Real) <= 2) hleft
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hIntPrefix hpartialInt
  have htwoToU :
      (∫ v in (2 : Real)..u - 1, buchstabFunction v) <=
        sectionSixTailCumulative i + sectionSixTailMajorant i *
          (u - (3 + (i : Real) / 32)) := by
    rw [← hsplit]
    exact add_le_add hprefix hpartial
  have hIntOneTwo := sectionSixTailBuchstab_intervalIntegrable
    (a := (1 : Real)) (b := 2) (by norm_num) (by norm_num)
  have hIntTwoU := sectionSixTailBuchstab_intervalIntegrable
    (a := (2 : Real)) (b := u - 1) (by norm_num) (by linarith)
  have hsplitOne := intervalIntegral.integral_add_adjacent_intervals
    hIntOneTwo hIntTwoU
  have hrec := mul_buchstabFunction_eq (by linarith : (2 : Real) <= u)
  rw [← hsplitOne, sectionSixTail_integral_buchstab_one_two] at hrec
  have hlogTwo : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hnodeLeft := sectionSixTailNode_upper i hi.le
  have hnodeRight := sectionSixTailNode_upper (i + 1) (Nat.succ_le_of_lt hi)
  have hqNonneg : 0 <= u - (3 + (i : Real) / 32) := by linarith
  have hqUpper : u - (3 + (i : Real) / 32) <= 1 / 32 := by
    linarith
  have haffine :
      1 + (0.6931471808 : Real) + sectionSixTailCumulative i +
          sectionSixTailMajorant i *
            (u - (3 + (i : Real) / 32)) <=
        (564383 / 1000000 : Real) * u := by
    by_cases hMD : sectionSixTailMajorant i <= 564383 / 1000000
    · have hmul := mul_le_mul_of_nonneg_right hMD hqNonneg
      linarith
    · have hDM : (564383 / 1000000 : Real) <=
          sectionSixTailMajorant i := le_of_not_ge hMD
      have hrem : 0 <= 1 / 32 -
          (u - (3 + (i : Real) / 32)) := by linarith
      have hmul := mul_le_mul_of_nonneg_right hDM hrem
      have hcumSucc : sectionSixTailCumulative (i + 1) =
          sectionSixTailCumulative i + sectionSixTailMajorant i / 32 := by
        simp only [sectionSixTailCumulative, Finset.sum_range_succ]
      rw [hcumSucc] at hnodeRight
      norm_num [Nat.cast_add, Nat.cast_one] at hnodeRight
      linarith
  have hproduct : u * buchstabFunction u <=
      (564383 / 1000000 : Real) * u := by
    rw [hrec]
    linarith
  exact (mul_le_mul_iff_of_pos_left (by linarith : 0 < u)).mp
    (by simpa [mul_comm] using hproduct)

private theorem sectionSixTailBuchstab_le_base
    {u : Real} (huThree : 3 <= u) (huFour : u <= 4) :
    buchstabFunction u <= 564383 / 1000000 := by
  by_cases huEq : u = 4
  · subst u
    apply sectionSixTailBuchstab_le_base_cell 31 (by norm_num)
    · norm_num
    · norm_num
  · have huLt : u < 4 := lt_of_le_of_ne huFour huEq
    let i : Nat := ⌊(32 * (u - 3))⌋₊
    have hyNonneg : 0 <= 32 * (u - 3) := by positivity
    have hi : i < 32 := by
      dsimp [i]
      rw [Nat.floor_lt hyNonneg]
      norm_num
      nlinarith
    have hfloor := Nat.floor_le hyNonneg
    have hceil := (Nat.lt_floor_add_one (32 * (u - 3))).le
    apply sectionSixTailBuchstab_le_base_cell i hi
    · dsimp [i] at hfloor ⊢
      nlinarith
    · dsimp [i] at hceil ⊢
      nlinarith

private theorem sectionSixTailBuchstab_le_steps :
    forall n : Nat, forall {u : Real}, 3 <= u -> u <= n + 4 ->
      buchstabFunction u <= 564383 / 1000000 := by
  intro n
  induction n with
  | zero =>
      intro u huThree huUpper
      exact sectionSixTailBuchstab_le_base huThree
        (by norm_num at huUpper ⊢; exact huUpper)
  | succ n ih =>
      intro u huThree huUpper
      by_cases hprev : u <= (n : Real) + 4
      · exact ih huThree hprev
      · have huFour : 4 <= u := by
          have hn : (0 : Real) <= n := by positivity
          linarith
        have huSubThree : 3 <= u - 1 := by linarith
        have huSubUpper : u - 1 <= (n : Real) + 4 := by
          norm_num at huUpper
          linarith
        have hIntOneThree := sectionSixTailBuchstab_intervalIntegrable
          (a := (1 : Real)) (b := 3) (by norm_num) (by norm_num)
        have hIntThreeUpper := sectionSixTailBuchstab_intervalIntegrable
          (a := (3 : Real)) (b := u - 1) (by norm_num) huSubThree
        have hIntegralUpper :
            (∫ v in (3 : Real)..u - 1, buchstabFunction v) <=
              (564383 / 1000000 : Real) * (u - 4) := by
          calc
            (∫ v in (3 : Real)..u - 1, buchstabFunction v) <=
                ∫ _v in (3 : Real)..u - 1,
                  (564383 / 1000000 : Real) := by
              apply intervalIntegral.integral_mono_on huSubThree
                hIntThreeUpper intervalIntegrable_const
              intro v hv
              exact ih hv.1 (hv.2.trans huSubUpper)
            _ = (564383 / 1000000 : Real) * (u - 4) := by
              rw [intervalIntegral.integral_const]
              ring
        have hSplit := intervalIntegral.integral_add_adjacent_intervals
          hIntOneThree hIntThreeUpper
        have hRec := mul_buchstabFunction_eq (by linarith : (2 : Real) <= u)
        have hFour := mul_buchstabFunction_eq (by norm_num : (2 : Real) <= 4)
        have hBase := sectionSixTailBuchstab_le_base
          (u := (4 : Real)) (by norm_num) (by norm_num)
        rw [← hSplit] at hRec
        norm_num at hFour
        have huPos : 0 < u := by linarith
        apply le_of_mul_le_mul_left ?_ huPos
        rw [hRec]
        nlinarith

theorem buchstabFunction_le_tailEnvelope
    {u : Real} (hu : 3 <= u) :
    buchstabFunction u <= 564383 / 1000000 := by
  obtain ⟨n, hn⟩ := exists_nat_ge u
  exact sectionSixTailBuchstab_le_steps n hu
    (hn.trans (by norm_num : (n : Real) <= n + 4))

end

end PrimesRestrictedDigits
