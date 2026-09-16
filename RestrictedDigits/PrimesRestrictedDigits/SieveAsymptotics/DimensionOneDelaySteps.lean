import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-!
# Finite steps for the dimension-one delay system

This constructs the scaled delay functions `q+ = s^2 Q+` and `q- = s^2 Q-` by finite clamped
integral steps. The source equations are Iwaniec's dimension-one specializations of
(6.1)--(6.2); see `IWANIEC-ROSSER-SIEVE-1980`, printed p. 189.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable def dimensionOneDelayStepKernel
    (threshold : Real) (f : Real -> Real) (t : Real) : Real :=
  let u := max threshold t
  u * f (u - 1) / (u - 1) ^ 2

noncomputable def dimensionOneDelayStepUpdate
    (threshold initial : Real) (f : Real -> Real) (s : Real) : Real :=
  initial - ∫ t in threshold..max threshold s,
    dimensionOneDelayStepKernel threshold f t

theorem dimensionOneDelayStepKernel_continuous
    {threshold : Real} (hthreshold : 1 < threshold)
    {f : Real -> Real} (hf : Continuous f) :
    Continuous (dimensionOneDelayStepKernel threshold f) := by
  let u : Real -> Real := fun t => max threshold t
  have hu : Continuous u := continuous_const.max continuous_id
  have hshift : Continuous (fun t => u t - 1) := hu.sub continuous_const
  unfold dimensionOneDelayStepKernel
  dsimp only
  apply (hu.mul (hf.comp hshift)).div (hshift.pow 2)
  intro t
  have hu1 : 0 < u t - 1 := by
    dsimp [u]
    linarith [le_max_left threshold t]
  exact pow_ne_zero _ hu1.ne'

theorem dimensionOneDelayStepUpdate_continuous
    {threshold initial : Real} (hthreshold : 1 < threshold)
    {f : Real -> Real} (hf : Continuous f) :
    Continuous (dimensionOneDelayStepUpdate threshold initial f) := by
  have hkernel := dimensionOneDelayStepKernel_continuous hthreshold hf
  have hprimitive : Continuous (fun s =>
      ∫ t in threshold..s, dimensionOneDelayStepKernel threshold f t) :=
    intervalIntegral.continuous_primitive
      (fun a b => hkernel.intervalIntegrable a b) threshold
  exact continuous_const.sub
    (hprimitive.comp (continuous_const.max continuous_id))

@[simp] theorem dimensionOneDelayStepUpdate_eq_initial_of_le
    {threshold initial : Real} (f : Real -> Real) {s : Real}
    (hs : s <= threshold) :
    dimensionOneDelayStepUpdate threshold initial f s = initial := by
  rw [dimensionOneDelayStepUpdate, max_eq_left hs]
  simp

theorem dimensionOneDelayStepUpdate_eq_integral_of_le
    {threshold initial : Real} (f : Real -> Real) {s : Real}
    (hs : threshold <= s) :
    dimensionOneDelayStepUpdate threshold initial f s =
      initial - ∫ t in threshold..s,
        dimensionOneDelayStepKernel threshold f t := by
  rw [dimensionOneDelayStepUpdate, max_eq_right hs]

theorem dimensionOneDelayStepUpdate_congr_of_le
    {threshold initial bound s : Real}
    (f g : Real -> Real) (hfg : ∀ x, x <= bound -> f x = g x)
    (hs : s <= bound + 1) :
    dimensionOneDelayStepUpdate threshold initial f s =
      dimensionOneDelayStepUpdate threshold initial g s := by
  by_cases hst : s <= threshold
  · rw [dimensionOneDelayStepUpdate_eq_initial_of_le f hst,
      dimensionOneDelayStepUpdate_eq_initial_of_le g hst]
  · have hts : threshold <= s := le_of_not_ge hst
    rw [dimensionOneDelayStepUpdate_eq_integral_of_le f hts,
      dimensionOneDelayStepUpdate_eq_integral_of_le g hts]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hts] at ht
    unfold dimensionOneDelayStepKernel
    rw [max_eq_right ht.1]
    dsimp only
    rw [hfg (t - 1) (by linarith [ht.2, hs])]

private noncomputable def dimensionOneDelayScaledApproxPair :
    Nat -> (Real -> Real) × (Real -> Real)
  | 0 => (fun _ => 1 / 2, fun _ => 1)
  | r + 1 =>
      let previousPlus := (dimensionOneDelayScaledApproxPair r).1
      let currentMinus := dimensionOneDelayStepUpdate 2 1 previousPlus
      let currentPlus := dimensionOneDelayStepUpdate 3 (1 / 2) currentMinus
      (currentPlus, currentMinus)

noncomputable def dimensionOneDelayScaledPlusApprox (r : Nat) (s : Real) : Real :=
  (dimensionOneDelayScaledApproxPair r).1 s

noncomputable def dimensionOneDelayScaledMinusApprox (r : Nat) (s : Real) : Real :=
  (dimensionOneDelayScaledApproxPair r).2 s

@[simp] theorem dimensionOneDelayScaledPlusApprox_zero (s : Real) :
    dimensionOneDelayScaledPlusApprox 0 s = 1 / 2 := by
  simp [dimensionOneDelayScaledPlusApprox, dimensionOneDelayScaledApproxPair]

@[simp] theorem dimensionOneDelayScaledMinusApprox_zero (s : Real) :
    dimensionOneDelayScaledMinusApprox 0 s = 1 := by
  simp [dimensionOneDelayScaledMinusApprox, dimensionOneDelayScaledApproxPair]

theorem dimensionOneDelayScaledMinusApprox_succ (r : Nat) (s : Real) :
    dimensionOneDelayScaledMinusApprox (r + 1) s =
      dimensionOneDelayStepUpdate 2 1
        (dimensionOneDelayScaledPlusApprox r) s := by
  rfl

theorem dimensionOneDelayScaledPlusApprox_succ (r : Nat) (s : Real) :
    dimensionOneDelayScaledPlusApprox (r + 1) s =
      dimensionOneDelayStepUpdate 3 (1 / 2)
        (dimensionOneDelayScaledMinusApprox (r + 1)) s := by
  rfl

private structure DimensionOneDelayScaledApproxProperties (r : Nat) : Prop where
  plus_continuous : Continuous (dimensionOneDelayScaledPlusApprox r)
  minus_continuous : Continuous (dimensionOneDelayScaledMinusApprox r)

private theorem dimensionOneDelayScaledApproxProperties_all (r : Nat) :
    DimensionOneDelayScaledApproxProperties r := by
  induction r with
  | zero =>
      exact ⟨continuous_const, continuous_const⟩
  | succ r ih =>
      have hminus : Continuous (dimensionOneDelayScaledMinusApprox (r + 1)) := by
        rw [show dimensionOneDelayScaledMinusApprox (r + 1) =
          dimensionOneDelayStepUpdate 2 1
            (dimensionOneDelayScaledPlusApprox r) by
            funext s
            rw [dimensionOneDelayScaledMinusApprox_succ]]
        exact dimensionOneDelayStepUpdate_continuous
          (by norm_num) ih.plus_continuous
      have hplus : Continuous (dimensionOneDelayScaledPlusApprox (r + 1)) := by
        rw [show dimensionOneDelayScaledPlusApprox (r + 1) =
          dimensionOneDelayStepUpdate 3 (1 / 2)
            (dimensionOneDelayScaledMinusApprox (r + 1)) by
            funext s
            rw [dimensionOneDelayScaledPlusApprox_succ]]
        exact dimensionOneDelayStepUpdate_continuous (by norm_num) hminus
      exact ⟨hplus, hminus⟩

theorem dimensionOneDelayScaledPlusApprox_continuous (r : Nat) :
    Continuous (dimensionOneDelayScaledPlusApprox r) :=
  (dimensionOneDelayScaledApproxProperties_all r).plus_continuous

theorem dimensionOneDelayScaledMinusApprox_continuous (r : Nat) :
    Continuous (dimensionOneDelayScaledMinusApprox r) :=
  (dimensionOneDelayScaledApproxProperties_all r).minus_continuous

theorem dimensionOneDelayScaledApprox_stable (r : Nat) :
    (∀ s, s <= 3 + 2 * (r : Real) ->
      dimensionOneDelayScaledPlusApprox r s =
        dimensionOneDelayScaledPlusApprox (r + 1) s) ∧
    (∀ s, s <= 2 + 2 * (r : Real) ->
      dimensionOneDelayScaledMinusApprox r s =
        dimensionOneDelayScaledMinusApprox (r + 1) s) := by
  induction r with
  | zero =>
      constructor
      · intro s hs
        rw [dimensionOneDelayScaledPlusApprox_zero,
          dimensionOneDelayScaledPlusApprox_succ,
          dimensionOneDelayStepUpdate_eq_initial_of_le _
            (by norm_num at hs ⊢; exact hs)]
      · intro s hs
        rw [dimensionOneDelayScaledMinusApprox_zero,
          dimensionOneDelayScaledMinusApprox_succ,
          dimensionOneDelayStepUpdate_eq_initial_of_le _
            (by norm_num at hs ⊢; exact hs)]
  | succ r ih =>
      have hminus : ∀ s, s <= 2 + 2 * ((r + 1 : Nat) : Real) ->
          dimensionOneDelayScaledMinusApprox (r + 1) s =
            dimensionOneDelayScaledMinusApprox (r + 2) s := by
        intro s hs
        rw [dimensionOneDelayScaledMinusApprox_succ,
          show r + 2 = (r + 1) + 1 by omega,
          dimensionOneDelayScaledMinusApprox_succ]
        apply dimensionOneDelayStepUpdate_congr_of_le
          (dimensionOneDelayScaledPlusApprox r)
          (dimensionOneDelayScaledPlusApprox (r + 1)) ih.1
        push_cast at hs
        linarith
      constructor
      · intro s hs
        rw [dimensionOneDelayScaledPlusApprox_succ,
          show r + 2 = (r + 1) + 1 by omega,
          dimensionOneDelayScaledPlusApprox_succ]
        apply dimensionOneDelayStepUpdate_congr_of_le
          (dimensionOneDelayScaledMinusApprox (r + 1))
          (dimensionOneDelayScaledMinusApprox (r + 2)) hminus
        norm_num [Nat.cast_add, Nat.cast_one] at hs ⊢
        linarith
      · exact hminus

theorem dimensionOneDelayScaledPlusApprox_add_stable
    (r k : Nat) {s : Real} (hs : s <= 3 + 2 * (r : Real)) :
    dimensionOneDelayScaledPlusApprox r s =
      dimensionOneDelayScaledPlusApprox (r + k) s := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ]
      exact ih.trans ((dimensionOneDelayScaledApprox_stable (r + k)).1 s (by
        have hk : (0 : Real) <= (k : Real) := by norm_num
        norm_num [Nat.cast_add] at hs ⊢
        linarith))

theorem dimensionOneDelayScaledMinusApprox_add_stable
    (r k : Nat) {s : Real} (hs : s <= 2 + 2 * (r : Real)) :
    dimensionOneDelayScaledMinusApprox r s =
      dimensionOneDelayScaledMinusApprox (r + k) s := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ]
      exact ih.trans ((dimensionOneDelayScaledApprox_stable (r + k)).2 s (by
        have hk : (0 : Real) <= (k : Real) := by norm_num
        norm_num [Nat.cast_add] at hs ⊢
        linarith))

noncomputable def dimensionOneDelayRank (s : Real) : Nat :=
  ⌈max 0 s⌉₊

theorem le_dimensionOneDelayRank (s : Real) :
    s <= (dimensionOneDelayRank s : Real) := by
  exact (le_max_right 0 s).trans (Nat.le_ceil (max 0 s))

theorem dimensionOneDelayScaledPlusApprox_diagonal_bound (s : Real) :
    s <= 3 + 2 * (dimensionOneDelayRank s : Real) := by
  have hr : 0 <= (dimensionOneDelayRank s : Real) := by norm_num
  linarith [le_dimensionOneDelayRank s]

theorem dimensionOneDelayScaledMinusApprox_diagonal_bound (s : Real) :
    s <= 2 + 2 * (dimensionOneDelayRank s : Real) := by
  have hr : 0 <= (dimensionOneDelayRank s : Real) := by norm_num
  linarith [le_dimensionOneDelayRank s]

noncomputable def dimensionOneDelayScaledPlus (s : Real) : Real :=
  dimensionOneDelayScaledPlusApprox (dimensionOneDelayRank s) s

noncomputable def dimensionOneDelayScaledMinus (s : Real) : Real :=
  dimensionOneDelayScaledMinusApprox (dimensionOneDelayRank s) s

theorem dimensionOneDelayScaledPlus_eq_approx_of_le (R : Nat) {s : Real}
    (hs : s <= (R : Real)) :
    dimensionOneDelayScaledPlus s = dimensionOneDelayScaledPlusApprox R s := by
  have hr : dimensionOneDelayRank s <= R := by
    rw [dimensionOneDelayRank, Nat.ceil_le]
    exact max_le (Nat.cast_nonneg R) hs
  rw [dimensionOneDelayScaledPlus, <- Nat.add_sub_of_le hr]
  exact dimensionOneDelayScaledPlusApprox_add_stable
    (dimensionOneDelayRank s) (R - dimensionOneDelayRank s)
      (dimensionOneDelayScaledPlusApprox_diagonal_bound s)

theorem dimensionOneDelayScaledMinus_eq_approx_of_le (R : Nat) {s : Real}
    (hs : s <= (R : Real)) :
    dimensionOneDelayScaledMinus s = dimensionOneDelayScaledMinusApprox R s := by
  have hr : dimensionOneDelayRank s <= R := by
    rw [dimensionOneDelayRank, Nat.ceil_le]
    exact max_le (Nat.cast_nonneg R) hs
  rw [dimensionOneDelayScaledMinus, <- Nat.add_sub_of_le hr]
  exact dimensionOneDelayScaledMinusApprox_add_stable
    (dimensionOneDelayRank s) (R - dimensionOneDelayRank s)
      (dimensionOneDelayScaledMinusApprox_diagonal_bound s)

theorem dimensionOneDelayScaledPlus_continuous :
    Continuous dimensionOneDelayScaledPlus := by
  rw [continuous_iff_continuousAt]
  intro s
  let R := dimensionOneDelayRank s + 1
  have hsR : s < (R : Real) := by
    have hs := le_dimensionOneDelayRank s
    dsimp [R]
    norm_num [Nat.cast_add, Nat.cast_one]
    linarith
  apply (dimensionOneDelayScaledPlusApprox_continuous R).continuousAt.congr_of_eventuallyEq
  filter_upwards [Iic_mem_nhds hsR] with t ht
  exact dimensionOneDelayScaledPlus_eq_approx_of_le R ht

theorem dimensionOneDelayScaledMinus_continuous :
    Continuous dimensionOneDelayScaledMinus := by
  rw [continuous_iff_continuousAt]
  intro s
  let R := dimensionOneDelayRank s + 1
  have hsR : s < (R : Real) := by
    have hs := le_dimensionOneDelayRank s
    dsimp [R]
    norm_num [Nat.cast_add, Nat.cast_one]
    linarith
  apply (dimensionOneDelayScaledMinusApprox_continuous R).continuousAt.congr_of_eventuallyEq
  filter_upwards [Iic_mem_nhds hsR] with t ht
  exact dimensionOneDelayScaledMinus_eq_approx_of_le R ht

theorem dimensionOneDelayScaledMinus_eq_stepUpdate (s : Real) :
    dimensionOneDelayScaledMinus s =
      dimensionOneDelayStepUpdate 2 1 dimensionOneDelayScaledPlus s := by
  let r := dimensionOneDelayRank s
  calc
    dimensionOneDelayScaledMinus s =
        dimensionOneDelayScaledMinusApprox (r + 1) s :=
      dimensionOneDelayScaledMinus_eq_approx_of_le (r + 1) (by
        have hs := le_dimensionOneDelayRank s
        dsimp [r]
        norm_num [Nat.cast_add, Nat.cast_one]
        linarith)
    _ = dimensionOneDelayStepUpdate 2 1
        (dimensionOneDelayScaledPlusApprox r) s :=
      dimensionOneDelayScaledMinusApprox_succ r s
    _ = dimensionOneDelayStepUpdate 2 1 dimensionOneDelayScaledPlus s := by
      apply dimensionOneDelayStepUpdate_congr_of_le
      · intro x hx
        exact (dimensionOneDelayScaledPlus_eq_approx_of_le r hx).symm
      · have hs := le_dimensionOneDelayRank s
        dsimp [r]
        linarith

theorem dimensionOneDelayScaledPlus_eq_stepUpdate (s : Real) :
    dimensionOneDelayScaledPlus s =
      dimensionOneDelayStepUpdate 3 (1 / 2) dimensionOneDelayScaledMinus s := by
  let r := dimensionOneDelayRank s
  calc
    dimensionOneDelayScaledPlus s =
        dimensionOneDelayScaledPlusApprox (r + 1) s :=
      dimensionOneDelayScaledPlus_eq_approx_of_le (r + 1) (by
        have hs := le_dimensionOneDelayRank s
        dsimp [r]
        norm_num [Nat.cast_add, Nat.cast_one]
        linarith)
    _ = dimensionOneDelayStepUpdate 3 (1 / 2)
        (dimensionOneDelayScaledMinusApprox (r + 1)) s :=
      dimensionOneDelayScaledPlusApprox_succ r s
    _ = dimensionOneDelayStepUpdate 3 (1 / 2) dimensionOneDelayScaledMinus s := by
      apply dimensionOneDelayStepUpdate_congr_of_le
      · intro x hx
        exact (dimensionOneDelayScaledMinus_eq_approx_of_le (r + 1) hx).symm
      · have hs := le_dimensionOneDelayRank s
        dsimp [r]
        norm_num [Nat.cast_add, Nat.cast_one]
        linarith

theorem dimensionOneDelayScaledMinus_eq_one_of_le
    {s : Real} (hs : s <= 2) :
    dimensionOneDelayScaledMinus s = 1 := by
  rw [dimensionOneDelayScaledMinus_eq_stepUpdate,
    dimensionOneDelayStepUpdate_eq_initial_of_le _ hs]

theorem dimensionOneDelayScaledPlus_eq_half_of_le
    {s : Real} (hs : s <= 3) :
    dimensionOneDelayScaledPlus s = 1 / 2 := by
  rw [dimensionOneDelayScaledPlus_eq_stepUpdate,
    dimensionOneDelayStepUpdate_eq_initial_of_le _ hs]

end PrimesRestrictedDigits
