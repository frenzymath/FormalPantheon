import PrimesRestrictedDigits.Fourier.Parseval
import PrimesRestrictedDigits.GenericMinorArcs.PrimeL2
import PrimesRestrictedDigits.MajorArcs.M1Contribution

/-!
# Exact decimal-grid Fourier inversion

The complete frequency grid is represented by `Fin (10 ^ K)`. The DFT is
unnormalized, so the finite inversion identity contributes one division by the
complex cast of `10 ^ K`.
-/

open scoped BigOperators ZMod

namespace PrimesRestrictedDigits

private theorem unitPhaseSum_eq_dft_indicator
    {X : Nat} [NeZero X] (A : Finset Nat)
    (hA : A ⊆ Finset.range X) (h : Fin X) :
    majorArcWeightedPhaseSum A (fun _ => 1)
        ((h.val : Real) / (X : Real)) =
      ZMod.dft (fun j : ZMod X =>
        if j.val ∈ A then (1 : Complex) else 0)
        (-(h.val : ZMod X)) := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  rw [← (ZMod.finEquiv X).toEquiv.sum_comp]
  have hsum :
      (∑ i : Fin X,
        ZMod.stdAddChar
            (-((ZMod.finEquiv X).toEquiv i *
              (-(h.val : ZMod X)))) *
          (if ((ZMod.finEquiv X).toEquiv i).val ∈ A then
            (1 : Complex) else 0)) =
      ∑ i : Fin X,
        ZMod.stdAddChar ((i.val : ZMod X) * (h.val : ZMod X)) *
          (if i.val ∈ A then (1 : Complex) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [finEquiv_apply_eq_natCast_val]
    rw [ZMod.val_natCast_of_lt i.isLt]
    simp only [mul_neg, neg_neg]
  rw [hsum]
  rw [Fin.sum_univ_eq_sum_range
    (fun n => ZMod.stdAddChar ((n : ZMod X) * (h.val : ZMod X)) *
      (if n ∈ A then (1 : Complex) else 0)) X]
  have hfilter :
      (Finset.range X).filter (fun n => n ∈ A) = A := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hn
      exact hn.2
    · intro hn
      exact ⟨Finset.mem_range.mp (hA hn), hn⟩
  rw [show (∑ n ∈ Finset.range X,
      ZMod.stdAddChar ((n : ZMod X) * (h.val : ZMod X)) *
        (if n ∈ A then (1 : Complex) else 0)) =
      ∑ n ∈ (Finset.range X).filter (fun n => n ∈ A),
        ZMod.stdAddChar ((n : ZMod X) * (h.val : ZMod X)) by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hnA : n ∈ A <;> simp [hnA]]
  rw [hfilter]
  unfold majorArcWeightedPhaseSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [one_mul]
  rw [show ((n : ZMod X) * (h.val : ZMod X)) =
      (((n : Int) * (h.val : Int) : Int) : ZMod X) by
        push_cast
        ring]
  rw [ZMod.stdAddChar_coe]
  unfold majorArcPhase
  congr 1
  push_cast
  have hX0 : (X : Real) ≠ 0 := by
    exact_mod_cast (NeZero.ne X)
  field_simp

/-- Exact finite Fourier inversion on the padded decimal grid. -/
theorem sum_paddedRestrictedNumbers_weight_eq_decimalGrid
    (digit : Fin 10) (K : Nat) (w : Nat -> Complex) :
    (∑ n ∈ paddedRestrictedNumbers digit K, w n) =
      (∑ h : Fin (10 ^ K),
        paddedDigitFourierSum digit K h.val *
          majorArcWeightedPhaseSum (Finset.range (10 ^ K)) w
            (-((h.val : Real) / ((10 ^ K : Nat) : Real)))) /
        ((10 ^ K : Nat) : Complex) := by
  let X : Nat := 10 ^ K
  let A : Finset Nat := paddedRestrictedNumbers digit K
  have hX : 0 < X := by
    dsimp only [X]
    positivity
  letI : NeZero X := ⟨hX.ne'⟩
  have hA : A ⊆ Finset.range X := by
    intro n hn
    dsimp only [A, X] at hn ⊢
    exact Finset.mem_range.mpr (mem_paddedRestrictedNumbers.mp hn).1
  let f : ZMod X → Complex := fun j =>
    if j.val ∈ A then (1 : Complex) else 0
  let g : ZMod X → Complex := fun j => w j.val
  have hgrid :
      (∑ h : Fin X,
        majorArcWeightedPhaseSum A (fun _ => 1)
            ((h.val : Real) / (X : Real)) *
          majorArcWeightedPhaseSum (Finset.range X) w
            (-((h.val : Real) / (X : Real)))) =
        (X : Complex) * ∑ n ∈ A, w n := by
    calc
      (∑ h : Fin X,
          majorArcWeightedPhaseSum A (fun _ => 1)
              ((h.val : Real) / (X : Real)) *
            majorArcWeightedPhaseSum (Finset.range X) w
              (-((h.val : Real) / (X : Real)))) =
          ∑ h : Fin X,
            ZMod.dft f (-(h.val : ZMod X)) *
              ZMod.dft g (h.val : ZMod X) := by
        apply Finset.sum_congr rfl
        intro h _
        rw [unitPhaseSum_eq_dft_indicator A hA h,
          weightedPhaseSum_eq_dft]
      _ = ∑ h : Fin X,
          ZMod.dft f (-((ZMod.finEquiv X).toEquiv h)) *
            ZMod.dft g ((ZMod.finEquiv X).toEquiv h) := by
        apply Finset.sum_congr rfl
        intro h _
        rw [finEquiv_apply_eq_natCast_val]
      _ = ∑ h : ZMod X, ZMod.dft f (-h) * ZMod.dft g h :=
        (ZMod.finEquiv X).toEquiv.sum_comp
          (fun h => ZMod.dft f (-h) * ZMod.dft g h)
      _ = (X : Complex) * ∑ j : ZMod X, f j * g j :=
        sum_dft_neg_mul_dft f g
      _ = (X : Complex) * ∑ n ∈ A, w n := by
        congr 1
        calc
          (∑ j : ZMod X, f j * g j) =
              ∑ i : Fin X,
                f ((ZMod.finEquiv X).toEquiv i) *
                  g ((ZMod.finEquiv X).toEquiv i) := by
            symm
            exact (ZMod.finEquiv X).toEquiv.sum_comp
              (fun j => f j * g j)
          _ = ∑ i : Fin X, (if i.val ∈ A then w i.val else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [finEquiv_apply_eq_natCast_val]
            simp [f, g, ZMod.val_natCast_of_lt i.isLt]
          _ = ∑ n ∈ Finset.range X,
                (if n ∈ A then w n else 0) :=
            Fin.sum_univ_eq_sum_range
              (fun n => if n ∈ A then w n else 0) X
          _ = ∑ n ∈ A, w n := by
            rw [← Finset.sum_filter]
            rw [show (Finset.range X).filter (fun n => n ∈ A) = A by
              ext n
              simp only [Finset.mem_filter, Finset.mem_range]
              constructor
              · intro hn'
                exact hn'.2
              · intro hn'
                exact ⟨Finset.mem_range.mp (hA hn'), hn'⟩]
  have hgrid' :
      (∑ h : Fin X,
        paddedDigitFourierSum digit K h.val *
          majorArcWeightedPhaseSum (Finset.range X) w
            (-((h.val : Real) / (X : Real)))) =
        (X : Complex) * ∑ n ∈ A, w n := by
    simpa only [A, X, majorArcWeightedPhaseSum_padded_eq] using hgrid
  have hXne : (X : Complex) ≠ 0 := by
    exact_mod_cast (NeZero.ne X)
  calc
    (∑ n ∈ paddedRestrictedNumbers digit K, w n) =
        ((X : Complex) * ∑ n ∈ A, w n) / (X : Complex) := by
      dsimp only [A]
      field_simp
    _ = (∑ h : Fin X,
        paddedDigitFourierSum digit K h.val *
          majorArcWeightedPhaseSum (Finset.range X) w
            (-((h.val : Real) / (X : Real)))) / (X : Complex) := by
      rw [hgrid']
    _ = (∑ h : Fin (10 ^ K),
        paddedDigitFourierSum digit K h.val *
          majorArcWeightedPhaseSum (Finset.range (10 ^ K)) w
            (-((h.val : Real) / ((10 ^ K : Nat) : Real)))) /
        ((10 ^ K : Nat) : Complex) := by
      rfl

end PrimesRestrictedDigits
