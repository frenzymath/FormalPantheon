import PrimesRestrictedDigits.Foundations.Intervals
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Weighted finite partial summation with a real endpoint

This is the second partial-summation step in Iwaniec's Lemma 21, Eq. (8.2),
`IWANIEC-ROSSER-SIEVE-1980`, printed p. 198; see also the dimension hypothesis on p. 171 and
the applications on pp. 199 and 201.
-/

open Finset MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem continuousOn_one_div_mul_log {a b : Real} (ha : 1 < a) :
    ContinuousOn (fun t : Real => 1 / (t * Real.log t)) (Icc a b) := by
  have hlog : ContinuousOn Real.log (Icc a b) := by
    apply Real.continuousOn_log.mono
    intro t ht
    exact ne_of_gt (by linarith [ha, ht.1])
  apply continuousOn_const.div (continuousOn_id.mul hlog)
  intro t ht
  apply mul_ne_zero
  · change t ≠ 0
    exact ne_of_gt (by linarith [ha, ht.1])
  · exact ne_of_gt (Real.log_pos (by linarith [ha, ht.1]))

private theorem sum_Ico_succ_sub_self (B : Nat -> Real) {m n : Nat}
    (hmn : m <= n) :
    (∑ i ∈ Ico m n, (B (i + 1) - B i)) = B n - B m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      rw [sum_Ico_succ_top hmn, ih]
      ring

private theorem sum_Ico_mul_eq_tailSum
    (a B : Nat -> Real) {m n : Nat} (hmn : m < n) :
    (∑ i ∈ Ico m n, a i * B i) =
      B m * (∑ k ∈ Ico m n, a k) +
        ∑ i ∈ Ico m (n - 1),
          (B (i + 1) - B i) * (∑ k ∈ Ico (i + 1) n, a k) := by
  have hparts := Finset.sum_Ico_by_parts B a hmn
  simp only [smul_eq_mul] at hparts
  rw [show (∑ i ∈ Ico m n, a i * B i) =
      ∑ i ∈ Ico m n, B i * a i by
    apply sum_congr rfl
    intro i hi
    ring]
  rw [hparts]
  have hmTop : m <= n - 1 := Nat.le_sub_one_of_lt hmn
  have htel := sum_Ico_succ_sub_self B hmTop
  have hprefix (i : Nat) (hi : i ∈ Finset.Ico m (n - 1)) :
      (∑ k ∈ range n, a k) - ∑ k ∈ range (i + 1), a k =
        ∑ k ∈ Ico (i + 1) n, a k := by
    rw [← sum_Ico_eq_sub]
    exact (Nat.succ_le_of_lt (Finset.mem_Ico.mp hi).2).trans
      (Nat.sub_le n 1)
  have htailSum :
      (∑ i ∈ Finset.Ico m (n - 1),
        (B (i + 1) - B i) * (∑ k ∈ Finset.Ico (i + 1) n, a k)) =
      ∑ i ∈ Finset.Ico m (n - 1),
        (B (i + 1) - B i) *
          ((∑ k ∈ range n, a k) - ∑ k ∈ range (i + 1), a k) := by
    apply sum_congr rfl
    intro i hi
    rw [hprefix i hi]
  have hfull : (∑ k ∈ Finset.Ico m n, a k) =
      (∑ k ∈ range n, a k) - ∑ k ∈ range m, a k :=
    sum_Ico_eq_sub _ hmn.le
  rw [htailSum, hfull]
  simp_rw [mul_sub]
  rw [sum_sub_distrib, ← sum_mul, htel]
  ring

private theorem sum_Ico_mul_le_of_tail_le
    (a B G E : Nat -> Real) {m n : Nat} (hmn : m < n)
    (hB0 : 0 <= B m)
    (hBstep : ∀ i ∈ Finset.Ico m (n - 1), B i <= B (i + 1))
    (hEle : ∀ i ∈ Finset.Ico m (n - 1), E (i + 1) <= E m)
    (htail : ∀ i ∈ Finset.Ico m n,
      (∑ k ∈ Finset.Ico i n, a k) <= G i + E i) :
    (∑ i ∈ Finset.Ico m n, a i * B i) <=
      B m * G m +
        (∑ i ∈ Finset.Ico m (n - 1),
          (B (i + 1) - B i) * G (i + 1)) +
        B (n - 1) * E m := by
  rw [sum_Ico_mul_eq_tailSum a B hmn]
  have hmMem : m ∈ Finset.Ico m n := Finset.mem_Ico.mpr ⟨le_rfl, hmn⟩
  have hmain :
      B m * (∑ k ∈ Finset.Ico m n, a k) <= B m * (G m + E m) :=
    mul_le_mul_of_nonneg_left (htail m hmMem) hB0
  have hdiff : ∀ i ∈ Finset.Ico m (n - 1),
      0 <= B (i + 1) - B i := by
    intro i hi
    exact sub_nonneg.mpr (hBstep i hi)
  have hrest :
      (∑ i ∈ Ico m (n - 1),
        (B (i + 1) - B i) * (∑ k ∈ Ico (i + 1) n, a k)) <=
      ∑ i ∈ Ico m (n - 1),
        (B (i + 1) - B i) * (G (i + 1) + E (i + 1)) := by
    apply sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left
    · apply htail (i + 1)
      rw [Finset.mem_Ico]
      have hiData := Finset.mem_Ico.mp hi
      have hnpos : 0 < n := (Nat.zero_le m).trans_lt hmn
      exact ⟨hiData.1.trans i.le_succ,
        (Nat.succ_le_of_lt hiData.2).trans_lt
          (Nat.sub_lt hnpos zero_lt_one)⟩
    · exact hdiff i hi
  calc
    B m * (∑ k ∈ Ico m n, a k) +
        ∑ i ∈ Ico m (n - 1),
          (B (i + 1) - B i) * (∑ k ∈ Ico (i + 1) n, a k) <=
        B m * (G m + E m) +
          ∑ i ∈ Ico m (n - 1),
            (B (i + 1) - B i) * (G (i + 1) + E (i + 1)) :=
      add_le_add hmain hrest
    _ = (B m * G m +
          ∑ i ∈ Ico m (n - 1),
            (B (i + 1) - B i) * G (i + 1)) +
        (B m * E m +
          ∑ i ∈ Ico m (n - 1),
            (B (i + 1) - B i) * E (i + 1)) := by
      simp_rw [mul_add, sum_add_distrib]
      ring
    _ <= (B m * G m +
          ∑ i ∈ Ico m (n - 1),
            (B (i + 1) - B i) * G (i + 1)) + B (n - 1) * E m := by
      have hmTop : m <= n - 1 := Nat.le_sub_one_of_lt hmn
      have htel := sum_Ico_succ_sub_self B hmTop
      have herr : B m * E m +
            ∑ i ∈ Ico m (n - 1),
              (B (i + 1) - B i) * E (i + 1) <= B (n - 1) * E m := by
        calc
          B m * E m + ∑ i ∈ Ico m (n - 1),
              (B (i + 1) - B i) * E (i + 1) <=
              B m * E m + ∑ i ∈ Ico m (n - 1),
                (B (i + 1) - B i) * E m := by
            apply add_le_add_right
            apply sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_left (hEle i hi) (hdiff i hi)
          _ = B (n - 1) * E m := by
            rw [← sum_mul, htel]
            ring
      nlinarith
    _ = _ := by ring

private theorem ceil_logIntegral_envelope
    (B : Real -> Real) {w z : Real} (hw : 2 <= w) (hwz : w < z)
    (hBcont : ContinuousOn B (Icc w z))
    (hBmono : MonotoneOn B (Icc w z))
    (hB0 : ∀ x ∈ Icc w z, 0 <= B x)
    (hmn : Nat.ceil w < Nat.ceil z) :
    B (Nat.ceil w : Real) *
          (∫ x in (Nat.ceil w : Real)..z, 1 / (x * Real.log x)) +
        ∑ i ∈ Ico (Nat.ceil w) (Nat.ceil z - 1),
          (B (i + 1 : Nat) - B i) *
            (∫ x in (i + 1 : Nat)..z, 1 / (x * Real.log x)) <=
      ∫ x in w..z, B x / (x * Real.log x) := by
  let m := Nat.ceil w
  let n := Nat.ceil z
  let ell := n - 1
  let g : Real -> Real := fun x => 1 / (x * Real.log x)
  let F : Real -> Real := fun x => B x * g x
  let G : Nat -> Real := fun i => ∫ x in (i : Real)..z, g x
  let q : Nat -> Real := fun i =>
    if i = ell then ∫ x in (i : Real)..z, g x
    else ∫ x in (i : Real)..(i + 1 : Nat), g x
  change m < n at hmn
  have hwm : w <= (m : Real) := Nat.le_ceil w
  have hmz : (m : Real) < z := Nat.lt_ceil.mp hmn
  have hnPos : 0 < n := (Nat.zero_le m).trans_lt hmn
  have hell : ell + 1 = n := by
    dsimp [ell]
    exact Nat.sub_add_cancel hnPos
  have hmell : m <= ell := by
    dsimp [ell]
    exact Nat.le_sub_one_of_lt hmn
  have hellz : (ell : Real) < z := by
    apply Nat.lt_ceil.mp
    change ell < n
    rw [← hell]
    exact Nat.lt_succ_self ell
  have hgCont : ContinuousOn g (Icc w z) := by
    dsimp [g]
    exact continuousOn_one_div_mul_log (by linarith [hw])
  have hFCont : ContinuousOn F (Icc w z) := hBcont.mul hgCont
  have hgInt : IntervalIntegrable g volume w z :=
    hgCont.intervalIntegrable_of_Icc hwz.le
  have hFInt : IntervalIntegrable F volume w z :=
    hFCont.intervalIntegrable_of_Icc hwz.le
  have hgNonneg : ∀ x ∈ Icc w z, 0 <= g x := by
    intro x hx
    dsimp [g]
    exact one_div_nonneg.mpr
      (mul_nonneg (by linarith [hw, hx.1])
        (Real.log_pos (by linarith [hw, hx.1])).le)
  have hFNonneg : ∀ x ∈ Icc w z, 0 <= F x := by
    intro x hx
    exact mul_nonneg (hB0 x hx) (hgNonneg x hx)
  have hgIntSub {a b : Real} (hwa : w <= a) (hab : a <= b)
      (hbz : b <= z) : IntervalIntegrable g volume a b := by
    apply hgInt.mono_set
    simpa [Set.uIcc_of_le hwz.le, Set.uIcc_of_le hab] using
      (Set.Icc_subset_Icc hwa hbz)
  have hFIntSub {a b : Real} (hwa : w <= a) (hab : a <= b)
      (hbz : b <= z) : IntervalIntegrable F volume a b := by
    apply hFInt.mono_set
    simpa [Set.uIcc_of_le hwz.le, Set.uIcc_of_le hab] using
      (Set.Icc_subset_Icc hwa hbz)
  have hqTail (i : Nat) (hi : i ∈ Finset.Ico m n) :
      (∑ k ∈ Ico i n, q k) = G i := by
    have hiData := Finset.mem_Ico.mp hi
    have hiell : i <= ell := by
      rw [← Nat.lt_add_one_iff, hell]
      exact hiData.2
    have hiCastW : w <= (i : Real) :=
      hwm.trans (by exact_mod_cast hiData.1)
    have hsumOrdinary : (∑ k ∈ Ico i ell, q k) =
        ∑ k ∈ Ico i ell,
          ∫ x in (k : Real)..(k + 1 : Nat), g x := by
      apply sum_congr rfl
      intro k hk
      have hkNe : k ≠ ell := ne_of_lt (Finset.mem_Ico.mp hk).2
      simp [q, hkNe]
    have hcollapse : (∑ k ∈ Ico i ell,
          ∫ x in (k : Real)..(k + 1 : Nat), g x) =
            ∫ x in (i : Real)..ell, g x := by
      apply intervalIntegral.sum_integral_adjacent_intervals_Ico hiell
      intro k hk
      have hkData := Set.mem_Ico.mp hk
      have hkW : w <= (k : Real) :=
        hiCastW.trans (by exact_mod_cast hkData.1)
      have hkSuccEll : k + 1 <= ell := Nat.succ_le_of_lt hkData.2
      have hkSuccEllReal : ((k + 1 : Nat) : Real) <= (ell : Real) := by
        exact_mod_cast hkSuccEll
      exact hgIntSub hkW (by exact_mod_cast Nat.le_succ k)
        (hkSuccEllReal.trans hellz.le)
    have hiEllInt : IntervalIntegrable g volume (i : Real) ell :=
      hgIntSub hiCastW (by exact_mod_cast hiell) hellz.le
    have hEllZInt : IntervalIntegrable g volume (ell : Real) z :=
      hgIntSub (hwm.trans (by exact_mod_cast hmell)) hellz.le le_rfl
    rw [← hell, sum_Ico_succ_top hiell, hsumOrdinary, hcollapse]
    simp only [q, if_pos]
    rw [intervalIntegral.integral_add_adjacent_intervals hiEllInt hEllZInt]
  have hmainEq : B (m : Real) * G m +
          ∑ i ∈ Ico m (n - 1),
            (B (i + 1 : Nat) - B i) * G (i + 1) =
        ∑ k ∈ Ico m n, q k * B k := by
    rw [sum_Ico_mul_eq_tailSum q (fun k => B k) hmn]
    rw [hqTail m (Finset.mem_Ico.mpr ⟨le_rfl, hmn⟩)]
    apply congrArg (fun y => B (m : Real) * G m + y)
    apply sum_congr rfl
    intro i hi
    rw [hqTail (i + 1) (by
      apply Finset.mem_Ico.mpr
      have hiData := Finset.mem_Ico.mp hi
      exact ⟨hiData.1.trans i.le_succ, by omega⟩)]
  have hcell (k : Nat) (hk : k ∈ Finset.Ico m ell) :
      q k * B k <= ∫ x in (k : Real)..(k + 1 : Nat), F x := by
    have hkData := Finset.mem_Ico.mp hk
    have hkNe : k ≠ ell := ne_of_lt hkData.2
    have hkW : w <= (k : Real) := hwm.trans (by exact_mod_cast hkData.1)
    have hkSuccEll : k + 1 <= ell := Nat.succ_le_of_lt hkData.2
    have hkSuccEllReal : ((k + 1 : Nat) : Real) <= (ell : Real) := by
      exact_mod_cast hkSuccEll
    have hkSuccZ : (k + 1 : Nat) <= z := hkSuccEllReal.trans hellz.le
    have hgCell := hgIntSub hkW (by exact_mod_cast Nat.le_succ k) hkSuccZ
    have hFCell := hFIntSub hkW (by exact_mod_cast Nat.le_succ k) hkSuccZ
    calc
      q k * B k = ∫ x in (k : Real)..(k + 1 : Nat), B k * g x := by
        rw [intervalIntegral.integral_const_mul]
        simp [q, hkNe]
        ring
      _ <= ∫ x in (k : Real)..(k + 1 : Nat), F x := by
        apply intervalIntegral.integral_mono_on
          (by exact_mod_cast Nat.le_succ k) (hgCell.const_mul (B k)) hFCell
        intro x hx
        have hxGlobal : x ∈ Icc w z := ⟨hkW.trans hx.1, hx.2.trans hkSuccZ⟩
        have hkGlobal : (k : Real) ∈ Icc w z :=
          ⟨hkW, (le_trans (by exact_mod_cast Nat.le_succ k) hkSuccZ)⟩
        exact mul_le_mul_of_nonneg_right
          (hBmono hkGlobal hxGlobal hx.1) (hgNonneg x hxGlobal)
  have hlast : q ell * B ell <= ∫ x in (ell : Real)..z, F x := by
    have hellW : w <= (ell : Real) := hwm.trans (by exact_mod_cast hmell)
    have hgLast := hgIntSub hellW hellz.le le_rfl
    have hFLast := hFIntSub hellW hellz.le le_rfl
    calc
      q ell * B ell = ∫ x in (ell : Real)..z, B ell * g x := by
        rw [intervalIntegral.integral_const_mul]
        simp [q]
        ring
      _ <= ∫ x in (ell : Real)..z, F x := by
        apply intervalIntegral.integral_mono_on hellz.le
          (hgLast.const_mul (B ell)) hFLast
        intro x hx
        have hxGlobal : x ∈ Icc w z := ⟨hellW.trans hx.1, hx.2⟩
        have hellGlobal : (ell : Real) ∈ Icc w z := ⟨hellW, hellz.le⟩
        exact mul_le_mul_of_nonneg_right
          (hBmono hellGlobal hxGlobal hx.1) (hgNonneg x hxGlobal)
  have hsumCells : (∑ k ∈ Ico m n, q k * B k) <=
      ∫ x in (m : Real)..z, F x := by
    rw [← hell, sum_Ico_succ_top hmell]
    calc
      (∑ k ∈ Ico m ell, q k * B k) + q ell * B ell <=
          (∑ k ∈ Ico m ell,
            ∫ x in (k : Real)..(k + 1 : Nat), F x) +
              ∫ x in (ell : Real)..z, F x :=
        add_le_add (sum_le_sum (fun k hk => hcell k hk)) hlast
      _ = (∫ x in (m : Real)..ell, F x) +
          ∫ x in (ell : Real)..z, F x := by
        rw [intervalIntegral.sum_integral_adjacent_intervals_Ico hmell]
        intro k hk
        have hkData := Set.mem_Ico.mp hk
        have hkW : w <= (k : Real) :=
          hwm.trans (by exact_mod_cast hkData.1)
        have hkSuccEll : k + 1 <= ell := Nat.succ_le_of_lt hkData.2
        have hkSuccEllReal : ((k + 1 : Nat) : Real) <= (ell : Real) := by
          exact_mod_cast hkSuccEll
        exact hFIntSub hkW (by exact_mod_cast Nat.le_succ k)
          (hkSuccEllReal.trans hellz.le)
      _ = ∫ x in (m : Real)..z, F x := by
        rw [intervalIntegral.integral_add_adjacent_intervals
          (hFIntSub hwm (by exact_mod_cast hmell) hellz.le)
          (hFIntSub (hwm.trans (by exact_mod_cast hmell)) hellz.le le_rfl)]
  have hextend : (∫ x in (m : Real)..z, F x) <= ∫ x in w..z, F x := by
    apply intervalIntegral.integral_mono_interval hwm hmz.le le_rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hFNonneg x ⟨hx.1.le, hx.2⟩
    · exact hFInt
  have htarget : (∫ x in w..z, F x) =
      ∫ x in w..z, B x / (x * Real.log x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [F, g]
    ring
  change B (m : Real) * G m +
        ∑ i ∈ Ico m (n - 1),
          (B (i + 1 : Nat) - B i) * G (i + 1) <=
      ∫ x in w..z, B x / (x * Real.log x)
  rw [hmainEq, ← htarget]
  exact hsumCells.trans hextend

/-- The finite tail-to-integral form of Iwaniec's second partial-summation
step, with the last weight evaluated at the actual real endpoint. -/
theorem weightedNaturalSum_le_integral_add_of_tail
    (a : Nat -> Real) (B : Real -> Real) {K w z : Real}
    (hK : 0 <= K) (hw : 2 <= w) (hwz : w < z)
    (hBcont : ContinuousOn B (Icc w z))
    (hBmono : MonotoneOn B (Icc w z))
    (hB0 : ∀ x ∈ Icc w z, 0 <= B x)
    (htail : ∀ i ∈ naturalLeftClosedRightOpenInterval w z,
      (∑ k ∈ naturalLeftClosedRightOpenInterval (i : Real) z, a k) <=
        (∫ x in (i : Real)..z, 1 / (x * Real.log x)) +
          2 * K / Real.log (i : Real)) :
    (∑ i ∈ naturalLeftClosedRightOpenInterval w z,
      a i * B (i : Real)) <=
      (∫ x in w..z, B x / (x * Real.log x)) +
        2 * K * B z / Real.log w := by
  let m := Nat.ceil w
  let n := Nat.ceil z
  let ell := n - 1
  let Bn : Nat -> Real := fun i => B (i : Real)
  let G : Nat -> Real := fun i =>
    ∫ x in (i : Real)..z, 1 / (x * Real.log x)
  let E : Nat -> Real := fun i => 2 * K / Real.log (i : Real)
  have hwm : w <= (m : Real) := Nat.le_ceil w
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith [hw])
  change (∑ i ∈ Finset.Ico m n, a i * Bn i) <=
    (∫ x in w..z, B x / (x * Real.log x)) +
      2 * K * B z / Real.log w
  by_cases heq : m = n
  · have hmain : 0 <= ∫ x in w..z, B x / (x * Real.log x) := by
      apply intervalIntegral.integral_nonneg hwz.le
      intro x hx
      exact div_nonneg (hB0 x hx)
        (mul_nonneg (by linarith [hw, hx.1])
          (Real.log_pos (by linarith [hw, hx.1])).le)
    have herr : 0 <= 2 * K * B z / Real.log w :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK)
        (hB0 z ⟨hwz.le, le_rfl⟩)) hlogw.le
    rw [heq]
    simpa using add_nonneg hmain herr
  · have hmn : m < n := lt_of_le_of_ne (Nat.ceil_mono hwz.le) heq
    have hmz : (m : Real) < z := Nat.lt_ceil.mp hmn
    have hnPos : 0 < n := (Nat.zero_le m).trans_lt hmn
    have hell : ell + 1 = n := by
      dsimp [ell]
      exact Nat.sub_add_cancel hnPos
    have hmell : m <= ell := by
      dsimp [ell]
      exact Nat.le_sub_one_of_lt hmn
    have hellz : (ell : Real) < z := by
      apply Nat.lt_ceil.mp
      change ell < n
      rw [← hell]
      exact Nat.lt_succ_self ell
    have hB0m : 0 <= Bn m := hB0 m ⟨hwm, hmz.le⟩
    have hBstep : ∀ i ∈ Finset.Ico m (n - 1), Bn i <= Bn (i + 1) := by
      intro i hi
      have hiData := Finset.mem_Ico.mp hi
      have hiW : w <= (i : Real) := hwm.trans (by exact_mod_cast hiData.1)
      have hiSuccEll : i + 1 <= ell := Nat.succ_le_of_lt hiData.2
      have hiSuccEllReal : ((i + 1 : Nat) : Real) <= (ell : Real) := by
        exact_mod_cast hiSuccEll
      have hiSuccZ : ((i + 1 : Nat) : Real) <= z :=
        hiSuccEllReal.trans hellz.le
      exact hBmono
        ⟨hiW, (le_trans (by exact_mod_cast Nat.le_succ i) hiSuccZ)⟩
        ⟨hiW.trans (by exact_mod_cast i.le_succ), hiSuccZ⟩
        (by exact_mod_cast i.le_succ)
    have hEle : ∀ i ∈ Finset.Ico m (n - 1), E (i + 1) <= E m := by
      intro i hi
      have hiData := Finset.mem_Ico.mp hi
      have hmSucc : m <= i + 1 := hiData.1.trans i.le_succ
      have hmPos : 0 < (m : Real) := by linarith [hw, hwm]
      have hiPos : 0 < ((i + 1 : Nat) : Real) :=
        hmPos.trans_le (by exact_mod_cast hmSucc)
      have hlogm : 0 < Real.log (m : Real) := Real.log_pos (by linarith [hw, hwm])
      have hlogLe : Real.log (m : Real) <= Real.log (i + 1 : Nat) :=
        Real.strictMonoOn_log.monotoneOn hmPos hiPos (by exact_mod_cast hmSucc)
      exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hK)
        hlogm hlogLe
    have htail' : ∀ i ∈ Finset.Ico m n,
        (∑ k ∈ Finset.Ico i n, a k) <= G i + E i := by
      intro i hi
      have hiNatural : i ∈ naturalLeftClosedRightOpenInterval w z := by
        simpa [naturalLeftClosedRightOpenInterval, m, n] using hi
      simpa [naturalLeftClosedRightOpenInterval, n, G, E] using
        (htail i hiNatural)
    have hlift := sum_Ico_mul_le_of_tail_le
      a Bn G E hmn hB0m hBstep hEle htail'
    have henvelope : Bn m * G m +
          ∑ i ∈ Finset.Ico m (n - 1),
            (Bn (i + 1) - Bn i) * G (i + 1) <=
        ∫ x in w..z, B x / (x * Real.log x) :=
      ceil_logIntegral_envelope B hw hwz hBcont hBmono hB0 hmn
    have hBlz : Bn ell <= B z := by
      exact hBmono ⟨hwm.trans (by exact_mod_cast hmell), hellz.le⟩
        ⟨hwz.le, le_rfl⟩ hellz.le
    have hlogm : 0 < Real.log (m : Real) := Real.log_pos (by linarith [hw, hwm])
    have hwPos : 0 < w := (by norm_num : (0 : Real) < 2).trans_le hw
    have hmPos : 0 < (m : Real) := hwPos.trans_le hwm
    have hlogwm : Real.log w <= Real.log (m : Real) :=
      Real.strictMonoOn_log.monotoneOn hwPos hmPos hwm
    have hEmNonneg : 0 <= E m :=
      div_nonneg (mul_nonneg (by norm_num) hK) hlogm.le
    have hEw : E m <= 2 * K / Real.log w :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hK) hlogw hlogwm
    have herror : Bn (n - 1) * E m <= 2 * K * B z / Real.log w := by
      change Bn ell * E m <= 2 * K * B z / Real.log w
      calc
        Bn ell * E m <= B z * E m :=
          mul_le_mul_of_nonneg_right hBlz hEmNonneg
        _ <= B z * (2 * K / Real.log w) :=
          mul_le_mul_of_nonneg_left hEw (hB0 z ⟨hwz.le, le_rfl⟩)
        _ = 2 * K * B z / Real.log w := by ring
    exact hlift.trans (add_le_add henvelope herror)

end PrimesRestrictedDigits
