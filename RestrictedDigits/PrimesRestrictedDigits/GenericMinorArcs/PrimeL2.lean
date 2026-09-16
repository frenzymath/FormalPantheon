import PrimesRestrictedDigits.Fourier.Parseval
import PrimesRestrictedDigits.MajorArcs.WeightedPhaseSum

/-!
# Finite-grid L2 bounds for weighted phase sums

This supplies the exact Parseval and large-value layer of Lemma 12.1 in
`MAYNARD-PRD-PUBLISHED`, pp. 189--190. The source-specific logarithmic bound
for the prime-tuple coefficients is a separate downstream result.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Frequencies on the complete natural grid where a weighted phase sum is at
least the given threshold. -/
noncomputable def weightedPhaseLargeFrequencies
    (X : Nat) (w : Nat -> Complex) (T : Real) : Finset Nat := by
  classical
  exact (Finset.range X).filter fun h =>
    T <= ‖majorArcWeightedPhaseSum (Finset.range X) w
      (-((h : Real) / (X : Real)))‖

@[simp] theorem mem_weightedPhaseLargeFrequencies
    {X h : Nat} {w : Nat -> Complex} {T : Real} :
    h ∈ weightedPhaseLargeFrequencies X w T <->
      h < X ∧ T <= ‖majorArcWeightedPhaseSum (Finset.range X) w
        (-((h : Real) / (X : Real)))‖ := by
  simp [weightedPhaseLargeFrequencies]

/-- The negative natural-grid weighted phase sum is the unnormalized DFT. -/
theorem weightedPhaseSum_eq_dft
    {X : Nat} [NeZero X] (w : Nat -> Complex) (h : Nat) :
    majorArcWeightedPhaseSum (Finset.range X) w
        (-((h : Real) / (X : Real))) =
      ZMod.dft (fun j : ZMod X => w j.val) (h : ZMod X) := by
  unfold majorArcWeightedPhaseSum
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  rw [← (ZMod.finEquiv X).toEquiv.sum_comp]
  have hrhs :
      (∑ i : Fin X,
        ZMod.stdAddChar (-((ZMod.finEquiv X).toEquiv i * (h : ZMod X))) *
          w ((ZMod.finEquiv X).toEquiv i).val) =
      ∑ i : Fin X,
        ZMod.stdAddChar (-((i.val : ZMod X) * (h : ZMod X))) * w i.val := by
    apply Finset.sum_congr rfl
    intro i _
    rw [finEquiv_apply_eq_natCast_val]
    rw [ZMod.val_natCast_of_lt i.isLt]
  rw [hrhs]
  rw [Fin.sum_univ_eq_sum_range
    (fun n => ZMod.stdAddChar
      (-((n : ZMod X) * (h : ZMod X))) * w n) X]
  apply Finset.sum_congr rfl
  intro n _
  rw [show -((n : ZMod X) * (h : ZMod X)) =
      ((-((n : Int) * (h : Int)) : Int) : ZMod X) by push_cast; ring]
  rw [ZMod.stdAddChar_coe]
  unfold majorArcPhase
  rw [mul_comm]
  congr 1
  push_cast
  have hX0 : (X : Real) ≠ 0 := by exact_mod_cast (NeZero.ne X)
  field_simp

/-- Parseval on the natural representatives of the complete frequency grid,
with the unnormalized factor `X`. -/
theorem sum_norm_sq_weightedPhase_grid
    (X : Nat) (hX : 0 < X) (w : Nat -> Complex) :
    (∑ h ∈ Finset.range X,
      ‖majorArcWeightedPhaseSum (Finset.range X) w
        (-((h : Real) / (X : Real)))‖ ^ 2) =
      (X : Real) * ∑ n ∈ Finset.range X, ‖w n‖ ^ 2 := by
  letI : NeZero X := ⟨hX.ne'⟩
  let Phi : ZMod X -> Complex := fun j => w j.val
  have hfreq :
      (∑ i : Fin X, ‖ZMod.dft Phi (i.val : ZMod X)‖ ^ 2) =
        ∑ k : ZMod X, ‖ZMod.dft Phi k‖ ^ 2 := by
    calc
      _ = ∑ i : Fin X,
          ‖ZMod.dft Phi ((ZMod.finEquiv X).toEquiv i)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [finEquiv_apply_eq_natCast_val]
      _ = _ := (ZMod.finEquiv X).toEquiv.sum_comp
        (fun k => ‖ZMod.dft Phi k‖ ^ 2)
  have hcoeff :
      (∑ j : ZMod X, ‖Phi j‖ ^ 2) =
        ∑ n ∈ Finset.range X, ‖w n‖ ^ 2 := by
    calc
      _ = ∑ i : Fin X,
          ‖Phi ((ZMod.finEquiv X).toEquiv i)‖ ^ 2 :=
        ((ZMod.finEquiv X).toEquiv.sum_comp
          (fun j => ‖Phi j‖ ^ 2)).symm
      _ = ∑ i : Fin X, ‖w i.val‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [finEquiv_apply_eq_natCast_val]
        simp [Phi, ZMod.val_natCast_of_lt i.isLt]
      _ = _ := Fin.sum_univ_eq_sum_range (fun n => ‖w n‖ ^ 2) X
  calc
    (∑ h ∈ Finset.range X,
        ‖majorArcWeightedPhaseSum (Finset.range X) w
          (-((h : Real) / (X : Real)))‖ ^ 2) =
        ∑ i : Fin X,
          ‖majorArcWeightedPhaseSum (Finset.range X) w
            (-((i.val : Real) / (X : Real)))‖ ^ 2 :=
      (Fin.sum_univ_eq_sum_range
        (fun h => ‖majorArcWeightedPhaseSum (Finset.range X) w
          (-((h : Real) / (X : Real)))‖ ^ 2) X).symm
    _ = ∑ i : Fin X, ‖ZMod.dft Phi (i.val : ZMod X)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [weightedPhaseSum_eq_dft]
    _ = ∑ k : ZMod X, ‖ZMod.dft Phi k‖ ^ 2 := hfreq
    _ = (X : Real) * ∑ j : ZMod X, ‖Phi j‖ ^ 2 := sum_norm_sq_dft Phi
    _ = (X : Real) * ∑ n ∈ Finset.range X, ‖w n‖ ^ 2 := by rw [hcoeff]

/-- A finite large-value bound obtained by summing the squared threshold over
the filtered frequency carrier. -/
theorem card_weightedPhaseLargeFrequencies_mul_sq_le
    (X : Nat) (hX : 0 < X) (w : Nat -> Complex)
    (T : Real) (hT : 0 <= T) :
    ((weightedPhaseLargeFrequencies X w T).card : Real) * T ^ 2 <=
      (X : Real) * ∑ n ∈ Finset.range X, ‖w n‖ ^ 2 := by
  let E := weightedPhaseLargeFrequencies X w T
  have hsubset : E ⊆ Finset.range X := by
    intro h hh
    exact Finset.mem_range.mpr
      (mem_weightedPhaseLargeFrequencies.mp hh).1
  have hpoint : ∀ h ∈ E, T ^ 2 <=
      ‖majorArcWeightedPhaseSum (Finset.range X) w
        (-((h : Real) / (X : Real)))‖ ^ 2 := by
    intro h hh
    exact (sq_le_sq₀ hT (norm_nonneg _)).2
      (mem_weightedPhaseLargeFrequencies.mp hh).2
  calc
    (E.card : Real) * T ^ 2 = ∑ _h ∈ E, T ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ <= ∑ h ∈ E,
        ‖majorArcWeightedPhaseSum (Finset.range X) w
          (-((h : Real) / (X : Real)))‖ ^ 2 :=
      Finset.sum_le_sum hpoint
    _ <= ∑ h ∈ Finset.range X,
        ‖majorArcWeightedPhaseSum (Finset.range X) w
          (-((h : Real) / (X : Real)))‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro h _ _
        positivity)
    _ = (X : Real) * ∑ n ∈ Finset.range X, ‖w n‖ ^ 2 :=
      sum_norm_sq_weightedPhase_grid X hX w

/-- The explicit `100 * C^2` large-level estimate under a pointwise
coefficient cap. -/
theorem card_weightedPhaseLargeFrequencies_le
    (X : Nat) (hX : 0 < X) (w : Nat -> Complex)
    (C L : Real) (hC : 0 < C) (hL : 0 <= L)
    (hw : ∀ n ∈ Finset.range X, ‖w n‖ <= L) :
    ((weightedPhaseLargeFrequencies X w
      ((X : Real) / (10 * C))).card : Real) <=
      100 * C ^ 2 * L ^ 2 := by
  have hXReal : (0 : Real) < X := by exact_mod_cast hX
  have hthreshold : 0 <= (X : Real) / (10 * C) := by positivity
  have hlarge := card_weightedPhaseLargeFrequencies_mul_sq_le
    X hX w ((X : Real) / (10 * C)) hthreshold
  have hcoeff : (∑ n ∈ Finset.range X, ‖w n‖ ^ 2) <=
      (X : Real) * L ^ 2 := by
    calc
      (∑ n ∈ Finset.range X, ‖w n‖ ^ 2) <=
          ∑ _n ∈ Finset.range X, L ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact (sq_le_sq₀ (norm_nonneg _) hL).2 (hw n hn)
      _ = (X : Real) * L ^ 2 := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have henergy :
      (X : Real) * (∑ n ∈ Finset.range X, ‖w n‖ ^ 2) <=
        (X : Real) ^ 2 * L ^ 2 := by
    calc
      (X : Real) * (∑ n ∈ Finset.range X, ‖w n‖ ^ 2) <=
          (X : Real) * ((X : Real) * L ^ 2) :=
        mul_le_mul_of_nonneg_left hcoeff hXReal.le
      _ = (X : Real) ^ 2 * L ^ 2 := by ring
  have hcombined := hlarge.trans henergy
  have hden : 0 < (10 * C) ^ 2 := by positivity
  have hXsq : 0 < (X : Real) ^ 2 := by positivity
  have hscaled :
      ((weightedPhaseLargeFrequencies X w
        ((X : Real) / (10 * C))).card : Real) * (X : Real) ^ 2 <=
        (100 * C ^ 2 * L ^ 2) * (X : Real) ^ 2 := by
    calc
      ((weightedPhaseLargeFrequencies X w
          ((X : Real) / (10 * C))).card : Real) * (X : Real) ^ 2 =
          (((weightedPhaseLargeFrequencies X w
            ((X : Real) / (10 * C))).card : Real) *
            ((X : Real) / (10 * C)) ^ 2) * (10 * C) ^ 2 := by
        field_simp
      _ <= ((X : Real) ^ 2 * L ^ 2) * (10 * C) ^ 2 :=
        mul_le_mul_of_nonneg_right hcombined hden.le
      _ = (100 * C ^ 2 * L ^ 2) * (X : Real) ^ 2 := by ring
  exact le_of_mul_le_mul_right hscaled hXsq

end PrimesRestrictedDigits
