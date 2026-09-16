import PrimesRestrictedDigits.Fourier.CenteredPhase
import PrimesRestrictedDigits.Fourier.KernelNormSq
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Local contraction for the digit Fourier kernel

This file proves the single-factor estimate used in the repaired proof of
`MAYNARD-PRD-PUBLISHED`, Lemma 10.1, pp. 169--170.  The proof uses two
adjacent allowed digits and Mathlib's global cosine bound, avoiding the
source's informal convexity claim.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Distance from a real number to its nearest integer. -/
noncomputable def nearestIntegerDistance (x : Real) : Real :=
  |x - (round x : Int)|

theorem nearestIntegerDistance_eq_norm_unitAddCircle (x : Real) :
    nearestIntegerDistance x = ‖(x : UnitAddCircle)‖ := by
  rw [nearestIntegerDistance, UnitAddCircle.norm_eq]

theorem nearestIntegerDistance_nonneg (x : Real) :
    0 ≤ nearestIntegerDistance x := by
  exact abs_nonneg _

theorem nearestIntegerDistance_le_half (x : Real) :
    nearestIntegerDistance x ≤ 1 / 2 := by
  exact abs_sub_round x

theorem nearestIntegerDistance_le_abs_sub_int (x : Real) (z : Int) :
    nearestIntegerDistance x ≤ |x - z| := by
  exact round_le x z

theorem nearestIntegerDistance_neg (x : Real) :
    nearestIntegerDistance (-x) = nearestIntegerDistance x := by
  rw [nearestIntegerDistance_eq_norm_unitAddCircle,
    nearestIntegerDistance_eq_norm_unitAddCircle]
  change ‖-((x : Real) : UnitAddCircle)‖ = ‖((x : Real) : UnitAddCircle)‖
  exact norm_neg _

theorem nearestIntegerDistance_perturbation_lower (x y : Real) :
    nearestIntegerDistance x - |y| ≤ nearestIntegerDistance (x + y) := by
  have htriangle :
      nearestIntegerDistance x ≤
        nearestIntegerDistance (x + y) + nearestIntegerDistance (-y) := by
    simp_rw [nearestIntegerDistance_eq_norm_unitAddCircle]
    convert norm_add_le ((x + y : Real) : UnitAddCircle)
      ((-y : Real) : UnitAddCircle) using 1; simp
  have hy : nearestIntegerDistance (-y) ≤ |y| := by
    simpa [nearestIntegerDistance_neg] using
      nearestIntegerDistance_le_abs_sub_int y 0
  linarith

theorem nearestIntegerDistance_ten_mul_of_lt
    {x : Real} (hx : nearestIntegerDistance x < 1 / 20) :
    nearestIntegerDistance (10 * x) = 10 * nearestIntegerDistance x := by
  let r : Real := x - (round x : Int)
  have hrAbs : |r| < (1 / 20 : Real) := by
    simpa [r, nearestIntegerDistance] using hx
  have hrMem : 10 * r ∈ Set.Ico (-(1 / 2 : Real)) (1 / 2) := by
    rw [abs_lt] at hrAbs
    constructor <;> linarith
  have hround : round (10 * r) = 0 := round_eq_zero_iff.mpr hrMem
  have hxDecomp : 10 * x = 10 * r + (10 * round x : Int) := by
    dsimp [r]
    push_cast
    ring
  rw [nearestIntegerDistance, nearestIntegerDistance, hxDecomp,
    round_add_intCast, hround]
  push_cast
  rw [show 10 * r + 10 * (round x : Real) -
      (0 + 10 * (round x : Real)) = 10 * r by ring,
    show x - (round x : Real) = r by rfl]
  rw [abs_mul]
  norm_num

private theorem nearestIntegerDistance_eq_abs_centeredFract (x : Real) :
    nearestIntegerDistance x = |centeredFract x| := by
  rw [nearestIntegerDistance, round_eq]
  have h := centeredFract_decomp x
  congr 1
  linarith

private noncomputable def localDigitPhase (d : Nat) (x : Real) : Complex :=
  Complex.exp (((2 * Real.pi * (d : Real) * x : Real) : Complex) * Complex.I)

private theorem norm_localDigitPhase (d : Nat) (x : Real) :
    ‖localDigitPhase d x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

private theorem adjacentPair_normSq (d : Nat) (x : Real) :
    Complex.normSq (localDigitPhase d x + localDigitPhase (d + 1) x) =
      2 + 2 * Real.cos (2 * Real.pi * x) := by
  have h := expNormSq_sum_double (Finset.range 2)
    (fun j : Nat => 2 * Real.pi * ((d + j : Nat) : Real) * x)
  norm_num [Finset.sum_range_succ] at h
  have h' :
      Complex.normSq (localDigitPhase d x + localDigitPhase (d + 1) x) =
        1 + Real.cos (2 * Real.pi * ((d : Real) + 1) * x -
            2 * Real.pi * (d : Real) * x) +
          (Real.cos (2 * Real.pi * (d : Real) * x -
            2 * Real.pi * ((d : Real) + 1) * x) + 1) := by
    unfold localDigitPhase
    convert h using 1; push_cast; ring
  calc
    _ = 1 + Real.cos (2 * Real.pi * ((d : Real) + 1) * x -
          2 * Real.pi * (d : Real) * x) +
        (Real.cos (2 * Real.pi * (d : Real) * x -
          2 * Real.pi * ((d : Real) + 1) * x) + 1) := h'
    _ = 2 + 2 * Real.cos (2 * Real.pi * x) := by
      rw [show 2 * Real.pi * ((d : Real) + 1) * x -
          2 * Real.pi * (d : Real) * x = 2 * Real.pi * x by ring,
        show 2 * Real.pi * (d : Real) * x -
          2 * Real.pi * ((d : Real) + 1) * x = -(2 * Real.pi * x) by ring,
        Real.cos_neg]
      ring

private theorem cos_two_pi_le (x : Real) :
    Real.cos (2 * Real.pi * x) ≤
      1 - 8 * nearestIntegerDistance x ^ 2 := by
  let c := centeredFract x
  have hc : |2 * Real.pi * c| ≤ Real.pi := by
    have habs : |c| ≤ (1 / 2 : Real) := (abs_le).2 (centeredFract_mem x)
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    nlinarith [Real.pi_pos]
  have hcos := Real.cos_le_one_sub_mul_cos_sq hc
  rw [cos_two_pi_mul_eq_centeredFract]
  calc
    Real.cos (2 * Real.pi * centeredFract x) ≤
        1 - 2 / Real.pi ^ 2 * (2 * Real.pi * c) ^ 2 := hcos
    _ = 1 - 8 * nearestIntegerDistance x ^ 2 := by
      rw [nearestIntegerDistance_eq_abs_centeredFract, sq_abs]
      dsimp [c]
      field_simp [ne_of_gt Real.pi_pos]
      ring

private theorem adjacentPair_norm_le (d : Nat) (x : Real) :
    ‖localDigitPhase d x + localDigitPhase (d + 1) x‖ ≤
      2 - 4 * nearestIntegerDistance x ^ 2 := by
  have hdist := nearestIntegerDistance_le_half x
  have hdist0 := nearestIntegerDistance_nonneg x
  have hcos := cos_two_pi_le x
  have hsquare :
      ‖localDigitPhase d x + localDigitPhase (d + 1) x‖ ^ 2 ≤
        (2 - 4 * nearestIntegerDistance x ^ 2) ^ 2 := by
    rw [Complex.sq_norm, adjacentPair_normSq]
    nlinarith [sq_nonneg (nearestIntegerDistance x)]
  have hrhs : 0 ≤ 2 - 4 * nearestIntegerDistance x ^ 2 := by
    nlinarith [sq_nonneg (nearestIntegerDistance x)]
  exact (sq_le_sq₀ (norm_nonneg _) hrhs).mp hsquare

private def adjacentAllowedStart (a : Fin 10) : Nat :=
  if a.val ≤ 1 then 2 else 0

private theorem adjacentAllowedStart_mem (a : Fin 10) :
    adjacentAllowedStart a ∈ allowedDecimalDigits a ∧
      adjacentAllowedStart a + 1 ∈ allowedDecimalDigits a := by
  by_cases h : a.val ≤ 1
  · simp [adjacentAllowedStart, h, allowedDecimalDigits]
    omega
  · simp [adjacentAllowedStart, h, allowedDecimalDigits]
    omega

/-- Every normalized one-digit factor has Gaussian contraction in the
distance to the nearest integer, uniformly in the omitted digit. -/
theorem digitKernel_le_exp_nearestIntegerDistance_sq
    (digit : Fin 10) (x : Real) :
    digitKernel digit x ≤
      Real.exp (-(4 / 9 : Real) * nearestIntegerDistance x ^ 2) := by
  let d := adjacentAllowedStart digit
  let s := allowedDecimalDigits digit
  let r := (s.erase d).erase (d + 1)
  have hd : d ∈ s ∧ d + 1 ∈ s := by
    simpa [d, s] using adjacentAllowedStart_mem digit
  have hne : d + 1 ≠ d := by omega
  have hd' : d + 1 ∈ s.erase d := Finset.mem_erase.mpr ⟨hne, hd.2⟩
  have hcardS : s.card = 9 := by
    simpa [s] using allowedDecimalDigits_card digit
  have hcardErase : (s.erase d).card = 8 := by
    rw [Finset.card_erase_of_mem hd.1, hcardS]
  have hcardR : r.card = 7 := by
    dsimp [r]
    rw [Finset.card_erase_of_mem hd', hcardErase]
  have hsum :
      ∑ e ∈ s, localDigitPhase e x =
        (localDigitPhase d x + localDigitPhase (d + 1) x) +
          ∑ e ∈ r, localDigitPhase e x := by
    calc
      ∑ e ∈ s, localDigitPhase e x =
          (∑ e ∈ s.erase d, localDigitPhase e x) + localDigitPhase d x :=
        (Finset.sum_erase_add s (fun e => localDigitPhase e x) hd.1).symm
      _ = ((∑ e ∈ r, localDigitPhase e x) + localDigitPhase (d + 1) x) +
          localDigitPhase d x := by
        rw [Finset.sum_erase_add (s.erase d) (fun e => localDigitPhase e x) hd']
      _ = (localDigitPhase d x + localDigitPhase (d + 1) x) +
          ∑ e ∈ r, localDigitPhase e x := by abel
  have hrest : ‖∑ e ∈ r, localDigitPhase e x‖ ≤ 7 := by
    calc
      ‖∑ e ∈ r, localDigitPhase e x‖ ≤
          ∑ e ∈ r, ‖localDigitPhase e x‖ := norm_sum_le _ _
      _ = r.card := by simp [norm_localDigitPhase]
      _ = 7 := by exact_mod_cast hcardR
  have htotal :
      ‖∑ e ∈ s, localDigitPhase e x‖ ≤
        9 - 4 * nearestIntegerDistance x ^ 2 := by
    rw [hsum]
    calc
      _ ≤ ‖localDigitPhase d x + localDigitPhase (d + 1) x‖ +
          ‖∑ e ∈ r, localDigitPhase e x‖ := norm_add_le _ _
      _ ≤ (2 - 4 * nearestIntegerDistance x ^ 2) + 7 :=
        add_le_add (adjacentPair_norm_le d x) hrest
      _ = 9 - 4 * nearestIntegerDistance x ^ 2 := by ring
  have hkernel :
      digitKernel digit x ≤
        1 - (4 / 9 : Real) * nearestIntegerDistance x ^ 2 := by
    rw [digitKernel]
    change (1 / 9 : Real) *
        ‖∑ e ∈ allowedDecimalDigits digit,
          Complex.exp
            (((2 * Real.pi * (e : Real) * x : Real) : Complex) * Complex.I)‖ ≤ _
    change (1 / 9 : Real) *
        ‖∑ e ∈ s, localDigitPhase e x‖ ≤ _
    nlinarith
  calc
    digitKernel digit x ≤
        1 - (4 / 9 : Real) * nearestIntegerDistance x ^ 2 := hkernel
    _ ≤ Real.exp (-((4 / 9 : Real) * nearestIntegerDistance x ^ 2)) :=
      Real.one_sub_le_exp_neg _
    _ = Real.exp (-(4 / 9 : Real) * nearestIntegerDistance x ^ 2) := by
      congr 1
      ring

/-- The weaker coefficient used in the paper's product estimate. -/
theorem digitKernel_le_exp_sourceCoefficient
    (digit : Fin 10) (x : Real) :
    digitKernel digit x ≤
      Real.exp (-(1 / 20 : Real) * nearestIntegerDistance x ^ 2) := by
  refine (digitKernel_le_exp_nearestIntegerDistance_sq digit x).trans ?_
  apply Real.exp_le_exp.mpr
  have hsq : 0 ≤ nearestIntegerDistance x ^ 2 := sq_nonneg _
  nlinarith

end PrimesRestrictedDigits
