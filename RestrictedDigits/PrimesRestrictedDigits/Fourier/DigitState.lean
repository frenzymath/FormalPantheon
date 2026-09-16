import PrimesRestrictedDigits.Fourier.MatrixUpperBound

/-!
# Digit-window states and transitions

The source's Markov matrix has rows for shifted/future digit words and columns
for previous words. This file fixes that orientation without choosing a
numeric enumeration of the finite state type.
-/

open scoped BigOperators Matrix

namespace PrimesRestrictedDigits

abbrev DigitWindowState (length : ℕ) := Fin length → Fin 10

def digitWindowPrefix {length : ℕ}
    (window : Fin (length + 1) → Fin 10) : DigitWindowState length :=
  fun index => window index.castSucc

def digitWindowSuffix {length : ℕ}
    (window : Fin (length + 1) → Fin 10) : DigitWindowState length :=
  fun index => window index.succ

def appendDigitWindow {length : ℕ} (previous : DigitWindowState length)
    (last : Fin 10) : Fin (length + 1) → Fin 10 :=
  Fin.lastCases last previous

theorem card_digitWindowState (length : ℕ) :
    Fintype.card (DigitWindowState length) = 10 ^ length := by
  simp [DigitWindowState]

theorem digitWindowPrefix_appendDigitWindow {length : ℕ}
    (previous : DigitWindowState length) (last : Fin 10) :
    digitWindowPrefix (appendDigitWindow previous last) = previous := by
  funext index
  simp [digitWindowPrefix, appendDigitWindow]

theorem appendDigitWindow_prefix_last {length : ℕ}
    (window : Fin (length + 1) → Fin 10) :
    appendDigitWindow (digitWindowPrefix window) (window (Fin.last length)) = window := by
  funext index
  refine Fin.lastCases ?_ (fun i => ?_) index
  · simp [appendDigitWindow]
  · simp [appendDigitWindow, digitWindowPrefix]

noncomputable def digitWindowTransitionMatrix (length : ℕ)
    (weight : (Fin (length + 1) → Fin 10) → ℝ) :
    Matrix (DigitWindowState length) (DigitWindowState length) ℝ :=
  fun future previous =>
    ∑ last : Fin 10,
      if digitWindowSuffix (appendDigitWindow previous last) = future then
        weight (appendDigitWindow previous last)
      else 0

theorem digitWindowTransitionMatrix_nonneg (length : ℕ)
    (weight : (Fin (length + 1) → Fin 10) → ℝ)
    (hweight : ∀ window, 0 ≤ weight window) :
    ∀ future previous,
      0 ≤ digitWindowTransitionMatrix length weight future previous := by
  intro future previous
  unfold digitWindowTransitionMatrix
  apply Finset.sum_nonneg
  intro last hlast
  split_ifs
  · exact hweight _
  · exact le_rfl

theorem digitWindow_eq_of_prefix_eq_of_suffix_eq {length : ℕ} (hlength : 0 < length)
    {first second : Fin (length + 1) → Fin 10}
    (hprefix : digitWindowPrefix first = digitWindowPrefix second)
    (hsuffix : digitWindowSuffix first = digitWindowSuffix second) :
    first = second := by
  funext index
  by_cases hzero : (index : ℕ) = 0
  · let stateIndex : Fin length := ⟨0, hlength⟩
    have hvalue := congrFun hprefix stateIndex
    have hindex : stateIndex.castSucc = index := Fin.ext hzero.symm
    simpa [digitWindowPrefix, hindex] using hvalue
  · let stateIndex : Fin length := ⟨(index : ℕ) - 1, by omega⟩
    have hvalue := congrFun hsuffix stateIndex
    have hindex : stateIndex.succ = index := by
      apply Fin.ext
      dsimp [stateIndex]
      omega
    simpa [digitWindowSuffix, hindex] using hvalue

theorem digitWindowTransitionMatrix_apply_window {length : ℕ} (hlength : 0 < length)
    (weight : (Fin (length + 1) → Fin 10) → ℝ)
    (window : Fin (length + 1) → Fin 10) :
    digitWindowTransitionMatrix length weight
      (digitWindowSuffix window) (digitWindowPrefix window) = weight window := by
  unfold digitWindowTransitionMatrix
  have hsingle : ∀ last : Fin 10, last = window (Fin.last length) ↔
      digitWindowSuffix (appendDigitWindow (digitWindowPrefix window) last) =
        digitWindowSuffix window := by
    intro last
    constructor
    · intro h
      subst last
      rw [appendDigitWindow_prefix_last]
    · intro h
      have hwindow :
          appendDigitWindow (digitWindowPrefix window) last = window := by
        apply digitWindow_eq_of_prefix_eq_of_suffix_eq hlength
        · exact digitWindowPrefix_appendDigitWindow _ _
        · exact h
      have hlast := congrFun hwindow (Fin.last length)
      simpa [appendDigitWindow] using hlast
  have hsum :
      (∑ last : Fin 10,
        if digitWindowSuffix (appendDigitWindow (digitWindowPrefix window) last) =
            digitWindowSuffix window then
          weight (appendDigitWindow (digitWindowPrefix window) last) else 0) =
        weight (appendDigitWindow (digitWindowPrefix window)
          (window (Fin.last length))) := by
    have hsum' := Finset.sum_eq_single
      (s := Finset.univ)
      (f := fun last : Fin 10 =>
        if digitWindowSuffix (appendDigitWindow (digitWindowPrefix window) last) =
            digitWindowSuffix window then
          weight (appendDigitWindow (digitWindowPrefix window) last) else 0)
      (a := window (Fin.last length))
      (by
        intro other hother hne
        rw [if_neg]
        intro hcondition
        exact hne ((hsingle other).mpr hcondition))
      (by simp)
    simpa [appendDigitWindow_prefix_last] using hsum'
  rw [hsum, appendDigitWindow_prefix_last]

theorem digitWindowTransitionMatrix_eq_zero_of_no_transition
    {length : ℕ} (weight : (Fin (length + 1) → Fin 10) → ℝ)
    {future previous : DigitWindowState length}
    (hno : ¬ ∃ last : Fin 10,
      digitWindowSuffix (appendDigitWindow previous last) = future) :
    digitWindowTransitionMatrix length weight future previous = 0 := by
  unfold digitWindowTransitionMatrix
  apply Finset.sum_eq_zero
  intro last hlast
  rw [if_neg]
  intro hcondition
  exact hno ⟨last, hcondition⟩

theorem digitWindowTransitionMatrix_zero_apply
    (weight : (Fin 1 → Fin 10) → ℝ)
    (future previous : DigitWindowState 0) :
    digitWindowTransitionMatrix 0 weight future previous =
      ∑ last : Fin 10, weight (appendDigitWindow previous last) := by
  unfold digitWindowTransitionMatrix
  have hstate : ∀ last : Fin 10,
      digitWindowSuffix (appendDigitWindow previous last) = future := by
    intro last
    apply Subsingleton.elim
  simp [hstate]

end PrimesRestrictedDigits
