import PrimesRestrictedDigits.BasicEstimates.PrimeDistribution
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletProgressionLogPower
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Short-interval errors for decimal-smooth progressions

This derives the project-repaired closed short-interval form of `MAYNARD-PRD-PUBLISHED`, Eq.
(5.1), p. 135. The added condition `0 < Delta <= 1` is assumed.
-/

open Filter Asymptotics
open scoped BigOperators

namespace PrimesRestrictedDigits

open ArithmeticFunction Finset

/-- The von Mangoldt sum in one residue class on a closed real interval. -/
noncomputable def vonMangoldtClosedProgressionSum
    (q a : Nat) (lower upper : Real) : Real :=
  ∑ n ∈ (naturalClosedInterval lower upper).filter
      (fun n => n ≡ a [MOD q]),
    vonMangoldt n

/-- Subtracting two weak global sums from the closed interval can leave only
the integral lower endpoint. -/
theorem vonMangoldtClosedProgressionSum_sub_difference_bounds
    {q a : Nat} {Y U : Real} (hY : 1 <= Y) (hYU : Y <= U) :
    0 <= vonMangoldtClosedProgressionSum q a Y U -
        (vonMangoldtProgressionSum q a U -
          vonMangoldtProgressionSum q a Y) ∧
      vonMangoldtClosedProgressionSum q a Y U -
        (vonMangoldtProgressionSum q a U -
          vonMangoldtProgressionSum q a Y) <= Real.log Y := by
  classical
  let P := fun n : Nat => n ≡ a [MOD q]
  let left := (Ioc 0 ⌊Y⌋₊).filter P
  let middle := (Ioc ⌊Y⌋₊ ⌊U⌋₊).filter P
  let whole := (Ioc 0 ⌊U⌋₊).filter P
  let endpoint := (naturalClosedInterval Y Y).filter P
  let closed := (naturalClosedInterval Y U).filter P
  have hFloor : ⌊Y⌋₊ <= ⌊U⌋₊ := Nat.floor_mono hYU
  have hWeakUnion : left ∪ middle = whole := by
    dsimp [left, middle, whole]
    rw [← Finset.filter_union,
      Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hFloor]
  have hWeakDisjoint : Disjoint left middle := by
    dsimp [left, middle]
    apply Finset.disjoint_filter_filter
    exact Finset.Ioc_disjoint_Ioc_of_le le_rfl
  have hWeakSum :
      vonMangoldtProgressionSum q a U -
          vonMangoldtProgressionSum q a Y =
        ∑ n ∈ middle, vonMangoldt n := by
    have hsum :
        (∑ n ∈ left, vonMangoldt n) +
            ∑ n ∈ middle, vonMangoldt n =
          ∑ n ∈ whole, vonMangoldt n := by
      rw [← Finset.sum_union hWeakDisjoint, hWeakUnion]
    dsimp [vonMangoldtProgressionSum, left, middle, whole, P]
    dsimp [left, middle, whole, P] at hsum
    linarith
  have hCeil : Nat.ceil Y <= Nat.floor Y + 1 :=
    Nat.ceil_le_floor_add_one Y
  have hClosedUnion : endpoint ∪ middle = closed := by
    ext n
    simp only [endpoint, middle, closed, P, naturalClosedInterval,
      Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro (⟨⟨hCeilN, hnFloor⟩, hnP⟩ | ⟨⟨hFloorN, hnU⟩, hnP⟩)
      · exact ⟨⟨hCeilN, hnFloor.trans hFloor⟩, hnP⟩
      · exact ⟨⟨hCeil.trans (Nat.succ_le_iff.mpr hFloorN), hnU⟩, hnP⟩
    · rintro ⟨⟨hCeilN, hnU⟩, hnP⟩
      by_cases hnFloor : n <= Nat.floor Y
      · exact Or.inl ⟨⟨hCeilN, hnFloor⟩, hnP⟩
      · exact Or.inr ⟨⟨lt_of_not_ge hnFloor, hnU⟩, hnP⟩
  have hClosedDisjoint : Disjoint endpoint middle := by
    rw [Finset.disjoint_left]
    intro n hnEndpoint hnMiddle
    have hnLe : n <= Nat.floor Y :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hnEndpoint).1).2
    have hnLt : Nat.floor Y < n :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hnMiddle).1).1
    omega
  have hClosedSum :
      vonMangoldtClosedProgressionSum q a Y U =
        (∑ n ∈ endpoint, vonMangoldt n) +
          ∑ n ∈ middle, vonMangoldt n := by
    rw [vonMangoldtClosedProgressionSum]
    change (∑ n ∈ closed, vonMangoldt n) = _
    rw [← hClosedUnion, Finset.sum_union hClosedDisjoint]
  have hEndpointNonneg :
      0 <= ∑ n ∈ endpoint, vonMangoldt n :=
    Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg
  have hEndpointLe :
      (∑ n ∈ endpoint, vonMangoldt n) <= Real.log Y := by
    have hbound :=
      abs_sum_vonMangoldt_naturalClosedInterval_sub_halfOpen_le_log
        P Y (upper := Y) hY
    rw [← abs_of_nonneg hEndpointNonneg]
    simpa [endpoint, P, naturalLeftClosedRightOpenInterval] using hbound
  have hDifference :
      vonMangoldtClosedProgressionSum q a Y U -
          (vonMangoldtProgressionSum q a U -
            vonMangoldtProgressionSum q a Y) =
        ∑ n ∈ endpoint, vonMangoldt n := by
    rw [hClosedSum, hWeakSum]
    ring
  rw [hDifference]
  exact ⟨hEndpointNonneg, hEndpointLe⟩

/-- For positive natural source exponent `A`, the repaired closed interval
sum has the required uniform logarithmic error. -/
theorem exists_abs_vonMangoldtClosedProgressionSum_sub_main_log_pow_le
    (A : Nat) (_hA : 0 < A) :
    ∃ C Y0 : Real,
      0 < C ∧ 4 <= Y0 ∧
      ∀ Y : Real, Y0 <= Y ->
        ∀ Delta : Real, 0 < Delta -> Delta <= 1 ->
          (Real.log Y ^ A)⁻¹ <= Delta ->
          ∀ q : Nat, 0 < q -> IsDecimalSmooth q ->
            ∀ a : Nat, Nat.Coprime a q ->
              (q : Real) <= Real.log Y ^ A ->
              abs (vonMangoldtClosedProgressionSum q a Y
                (Y + Delta * Y) -
                  Delta * Y / (q.totient : Real)) <=
                C * Y / Real.log Y ^ A := by
  obtain ⟨C0, x0, hC0, hx0, hGlobal⟩ :=
    exists_abs_vonMangoldtProgressionSum_sub_main_log_pow_le A A
  have hPowerEvent :
      ∀ᶠ x : Real in atTop, Real.log x ^ (A + 1) <= x := by
    have hbound :=
      (Real.isLittleO_pow_log_id_atTop (n := A + 1)).bound zero_lt_one
    filter_upwards [hbound, eventually_ge_atTop (1 : Real)] with x hx hx1
    have hleft : 0 <= Real.log x ^ (A + 1) :=
      pow_nonneg (Real.log_nonneg hx1) _
    have hright : 0 <= x := by linarith
    simpa only [id_eq,
      Real.norm_of_nonneg hleft, Real.norm_of_nonneg hright,
      one_mul] using hx
  obtain ⟨XE, hXE⟩ := eventually_atTop.mp hPowerEvent
  let Y0 : Real := max x0 XE
  have hx0Y0 : x0 <= Y0 := le_max_left _ _
  have hXEY0 : XE <= Y0 := le_max_right _ _
  have hY0Four : 4 <= Y0 := hx0.trans hx0Y0
  refine ⟨3 * C0 + 1, Y0, by positivity, hY0Four, ?_⟩
  intro Y hY Delta hDelta hDeltaOne _hDeltaLower q hq hSmooth a ha hqLog
  let U : Real := Y + Delta * Y
  have hYFour : 4 <= Y := hY0Four.trans hY
  have hYPos : 0 < Y := by linarith
  have hYU : Y <= U := by
    dsimp [U]
    nlinarith [mul_nonneg hDelta.le hYPos.le]
  have hU2Y : U <= 2 * Y := by
    have hDeltaY : Delta * Y <= 1 * Y :=
      mul_le_mul_of_nonneg_right hDeltaOne hYPos.le
    dsimp [U]
    linarith
  have hx0Y : x0 <= Y := hx0Y0.trans hY
  have hXEY : XE <= Y := hXEY0.trans hY
  have hLogYPos : 0 < Real.log Y := log_pos_of_four_le hYFour
  have hLogYU : Real.log Y <= Real.log U :=
    Real.log_le_log hYPos hYU
  have hLogPowMono : Real.log Y ^ A <= Real.log U ^ A :=
    pow_le_pow_left₀ hLogYPos.le hLogYU A
  have hLogYPowPos : 0 < Real.log Y ^ A := pow_pos hLogYPos A
  have hErrorY := hGlobal Y hx0Y q hq hSmooth a ha hqLog
  have hErrorU := hGlobal U (hx0Y.trans hYU) q hq hSmooth a ha
    (hqLog.trans hLogPowMono)
  have hErrorUScaled :
      abs (vonMangoldtProgressionSum q a U -
          U / (q.totient : Real)) <=
        2 * C0 * Y / Real.log Y ^ A := by
    apply hErrorU.trans
    calc
      C0 * U / Real.log U ^ A <=
          C0 * U / Real.log Y ^ A :=
        div_le_div_of_nonneg_left (by positivity) hLogYPowPos hLogPowMono
      _ <= C0 * (2 * Y) / Real.log Y ^ A :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hU2Y hC0.le) hLogYPowPos.le
      _ = 2 * C0 * Y / Real.log Y ^ A := by ring
  have hPower : Real.log Y ^ (A + 1) <= Y := hXE Y hXEY
  have hEndpointScale : Real.log Y <= Y / Real.log Y ^ A := by
    rw [le_div_iff₀ hLogYPowPos]
    calc
      Real.log Y * Real.log Y ^ A = Real.log Y ^ (A + 1) :=
        (pow_succ' (Real.log Y) A).symm
      _ <= Y := hPower
  have hEndpoint :=
    vonMangoldtClosedProgressionSum_sub_difference_bounds
      (q := q) (a := a) (Y := Y) (U := U) (by linarith) hYU
  let E0 : Real :=
    vonMangoldtClosedProgressionSum q a Y U -
      (vonMangoldtProgressionSum q a U -
        vonMangoldtProgressionSum q a Y)
  have hE0 : 0 <= E0 := by simpa [E0] using hEndpoint.1
  have hE0Scale : abs E0 <= Y / Real.log Y ^ A := by
    rw [abs_of_nonneg hE0]
    have hE0Le : E0 <= Real.log Y := by
      simpa [E0] using hEndpoint.2
    exact hE0Le.trans hEndpointScale
  have hIdentity :
      vonMangoldtClosedProgressionSum q a Y U -
          Delta * Y / (q.totient : Real) =
        E0 +
          (vonMangoldtProgressionSum q a U -
            U / (q.totient : Real)) -
          (vonMangoldtProgressionSum q a Y -
            Y / (q.totient : Real)) := by
    dsimp [E0, U]
    ring
  change abs (vonMangoldtClosedProgressionSum q a Y U -
    Delta * Y / (q.totient : Real)) <= _
  rw [hIdentity]
  calc
    abs (E0 +
          (vonMangoldtProgressionSum q a U -
            U / (q.totient : Real)) -
        (vonMangoldtProgressionSum q a Y -
          Y / (q.totient : Real))) <=
        abs (E0 +
          (vonMangoldtProgressionSum q a U -
            U / (q.totient : Real))) +
          abs (vonMangoldtProgressionSum q a Y -
            Y / (q.totient : Real)) := abs_sub _ _
    _ <= (abs E0 +
          abs (vonMangoldtProgressionSum q a U -
            U / (q.totient : Real))) +
          abs (vonMangoldtProgressionSum q a Y -
            Y / (q.totient : Real)) := by
      linarith [abs_add_le E0 (vonMangoldtProgressionSum q a U -
        U / (q.totient : Real))]
    _ <= (Y / Real.log Y ^ A +
          2 * C0 * Y / Real.log Y ^ A) +
          C0 * Y / Real.log Y ^ A := by
      gcongr
    _ = (3 * C0 + 1) * Y / Real.log Y ^ A := by ring

end PrimesRestrictedDigits
