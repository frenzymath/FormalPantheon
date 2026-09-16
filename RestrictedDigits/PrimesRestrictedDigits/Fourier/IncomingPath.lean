import PrimesRestrictedDigits.Fourier.DigitState
import PrimesRestrictedDigits.Fourier.MatrixPathSum

/-!
# Incoming digit-window paths

The transition matrix is written with future windows as rows and previous
windows as columns. Reindexing its incoming edges by the first digit of a full
window gives the recurrence used by the source's expanded matrix paths.
-/

open scoped BigOperators Matrix

namespace PrimesRestrictedDigits

def prependDigitWindow {length : ℕ} (first : Fin 10)
    (future : DigitWindowState length) : Fin (length + 1) → Fin 10 :=
  Fin.cases first future

theorem digitWindowSuffix_prependDigitWindow {length : ℕ}
    (first : Fin 10) (future : DigitWindowState length) :
    digitWindowSuffix (prependDigitWindow first future) = future := by
  funext index
  simp [digitWindowSuffix, prependDigitWindow]

theorem prependDigitWindow_reconstruct {length : ℕ}
    (window : Fin (length + 1) → Fin 10) :
    prependDigitWindow (window 0) (digitWindowSuffix window) = window := by
  funext index
  refine Fin.cases ?_ (fun i => ?_) index
  · simp [prependDigitWindow]
  · simp [prependDigitWindow, digitWindowSuffix]

def appendDigitWindowEquiv (length : ℕ) :
    DigitWindowState length × Fin 10 ≃ (Fin (length + 1) → Fin 10) where
  toFun pair := appendDigitWindow pair.1 pair.2
  invFun window := (digitWindowPrefix window, window (Fin.last length))
  left_inv pair := by
    rcases pair with ⟨previous, last⟩
    simp [digitWindowPrefix_appendDigitWindow, appendDigitWindow]
  right_inv window := appendDigitWindow_prefix_last window

private theorem incoming_sum_filter {length : ℕ}
    (weight : (Fin (length + 1) → Fin 10) → ℝ)
    (vector : DigitWindowState length → ℝ)
    (future : DigitWindowState length) :
    (∑ previous : DigitWindowState length,
      digitWindowTransitionMatrix length weight future previous * vector previous) =
      ∑ window ∈ Finset.univ.filter
          (fun window => digitWindowSuffix window = future),
        weight window * vector (digitWindowPrefix window) := by
  unfold digitWindowTransitionMatrix
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_product']
  have hsum :
      (∑ pair : DigitWindowState length × Fin 10,
        (if digitWindowSuffix (appendDigitWindow pair.1 pair.2) = future then
          weight (appendDigitWindow pair.1 pair.2) else 0) * vector pair.1) =
      ∑ window : Fin (length + 1) → Fin 10,
        (if digitWindowSuffix window = future then weight window else 0) *
          vector (digitWindowPrefix window) := by
    apply Fintype.sum_equiv (appendDigitWindowEquiv length)
    intro pair
    change
      (if digitWindowSuffix (appendDigitWindow pair.1 pair.2) = future then
          weight (appendDigitWindow pair.1 pair.2) else 0) * vector pair.1 =
        (if digitWindowSuffix (appendDigitWindow pair.1 pair.2) = future then
          weight (appendDigitWindow pair.1 pair.2) else 0) *
          vector (digitWindowPrefix (appendDigitWindow pair.1 pair.2))
    rw [digitWindowPrefix_appendDigitWindow]
  calc
    (∑ x ∈ Finset.univ ×ˢ Finset.univ,
        (if digitWindowSuffix (appendDigitWindow x.1 x.2) = future then
          weight (appendDigitWindow x.1 x.2) else 0) * vector x.1) =
        ∑ x : DigitWindowState length × Fin 10,
          (if digitWindowSuffix (appendDigitWindow x.1 x.2) = future then
            weight (appendDigitWindow x.1 x.2) else 0) * vector x.1 := by
          simp only [Finset.univ_product_univ]
    _ = ∑ window : Fin (length + 1) → Fin 10,
          (if digitWindowSuffix window = future then weight window else 0) *
            vector (digitWindowPrefix window) := hsum
    _ = ∑ window ∈ Finset.univ.filter
          (fun window => digitWindowSuffix window = future),
          weight window * vector (digitWindowPrefix window) := by
            rw [Finset.sum_filter]
            simp only [ite_mul, zero_mul]

private theorem filter_sum_incoming {length : ℕ}
    (weight : (Fin (length + 1) → Fin 10) → ℝ)
    (vector : DigitWindowState length → ℝ)
    (future : DigitWindowState length) :
    (∑ first : Fin 10,
      weight (prependDigitWindow first future) *
        vector (digitWindowPrefix (prependDigitWindow first future))) =
      ∑ window ∈ Finset.univ.filter
          (fun window => digitWindowSuffix window = future),
        weight window * vector (digitWindowPrefix window) := by
  apply Finset.sum_bij
    (fun first _ => prependDigitWindow first future)
  · intro first hfirst
    simp [digitWindowSuffix_prependDigitWindow]
  · intro first hfirst second hsecond heq
    have hvalue := congrFun heq (0 : Fin (length + 1))
    simpa [prependDigitWindow] using hvalue
  · intro window hwindow
    have hsuffix : digitWindowSuffix window = future := by
      simpa using (Finset.mem_filter.mp hwindow).2
    refine ⟨window 0, Finset.mem_univ _, ?_⟩
    rw [← hsuffix]
    exact prependDigitWindow_reconstruct window
  · intro first hfirst
    rfl

theorem digitWindowTransitionMatrix_mulVec_eq_incoming {length : ℕ}
    (weight : (Fin (length + 1) → Fin 10) → ℝ)
    (vector : DigitWindowState length → ℝ)
    (future : DigitWindowState length) :
    (digitWindowTransitionMatrix length weight *ᵥ vector) future =
      ∑ first : Fin 10,
        weight (prependDigitWindow first future) *
          vector (digitWindowPrefix (prependDigitWindow first future)) := by
  rw [Matrix.mulVec]
  simp only [dotProduct]
  rw [incoming_sum_filter]
  exact (filter_sum_incoming (length := length) weight vector future).symm

def digitWordPathSum {length : ℕ}
    (weight : (Fin (length + 1) → Fin 10) → ℝ) :
    ℕ → DigitWindowState length → ℝ
  | 0, _ => 1
  | steps + 1, future =>
      ∑ first : Fin 10,
        weight (prependDigitWindow first future) *
          digitWordPathSum weight steps
            (digitWindowPrefix (prependDigitWindow first future))

theorem digitWordPathSum_succ_apply {length : ℕ}
    (weight : (Fin (length + 1) → Fin 10) → ℝ)
    (steps : ℕ) (future : DigitWindowState length) :
    digitWordPathSum weight (steps + 1) future =
      ∑ first : Fin 10,
        weight (prependDigitWindow first future) *
          digitWordPathSum weight steps
            (digitWindowPrefix (prependDigitWindow first future)) := by
  rfl

theorem digitWordPathSum_apply_eq_matrixRowPathSum {length : ℕ}
    (weight : (Fin (length + 1) → Fin 10) → ℝ)
    (steps : ℕ) (future : DigitWindowState length) :
    digitWordPathSum weight steps future =
      matrixRowPathSum (digitWindowTransitionMatrix length weight) steps future := by
  induction steps generalizing future with
  | zero => rfl
  | succ steps ih =>
      rw [digitWordPathSum, matrixRowPathSum,
        digitWindowTransitionMatrix_mulVec_eq_incoming]
      apply Finset.sum_congr rfl
      intro first hfirst
      rw [ih]

theorem digitWordPathSum_eq_matrixRowPathSum {length : ℕ}
    (weight : (Fin (length + 1) → Fin 10) → ℝ)
    (steps : ℕ) :
    digitWordPathSum weight steps =
      matrixRowPathSum (digitWindowTransitionMatrix length weight) steps := by
  funext future
  exact digitWordPathSum_apply_eq_matrixRowPathSum weight steps future

end PrimesRestrictedDigits
