import BoundedGaps.Maynard.MaynardLambdaSharpBound

noncomputable section

/-!
# Maynard's finite Y-to-lambda transform

The concrete coefficient was introduced directly in the inverse-transform
form used in Maynard2013v3, equations `eq:YLambdaDef` and `eq:LambdaYDef`
(source lines 299--308). This file makes its supported `y` value explicit.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators
local instance yTransformDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def maynardYValue
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ)
    (r : H → ℕ) : ℝ :=
  if divisorTupleProduct H r < R ∧
      Nat.Coprime (divisorTupleProduct H r) W ∧
      Squarefree (divisorTupleProduct H r) then
    F (fun h => Real.log (r h) / Real.log R)
  else 0

def maynardCoefficientFromY
    (H : Finset ℕ) (R W : ℕ) (y : (H → ℕ) → ℝ)
    (d : H → ℕ) : ℝ :=
  if Nat.Coprime (divisorTupleProduct H d) W then
    (∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * d h) *
      ∑ r ∈ maynardDivisorTupleBox H R,
        if divisorTupleProduct H r < R ∧ (∀ h : H, d h ∣ r h) then
          y r / ∏ h : H, (Nat.totient (r h) : ℝ)
        else 0
  else 0

theorem maynardCoefficient_eq_fromYValue
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ)
    (d : H → ℕ) :
    maynardCoefficient H R W F d =
      maynardCoefficientFromY H R W (maynardYValue H R W F) d := by
  classical
  unfold maynardCoefficient maynardCoefficientFromY
  by_cases hdCop : Nat.Coprime (divisorTupleProduct H d) W
  · rw [if_pos hdCop, if_pos hdCop]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hbase : divisorTupleProduct H r < R ∧
        (∀ h : H, d h ∣ r h)
    · rw [if_pos hbase]
      by_cases hrCop : Nat.Coprime (divisorTupleProduct H r) W
      · rw [if_pos ⟨hbase.1, hbase.2, hrCop⟩]
        by_cases hrSq : Squarefree (divisorTupleProduct H r)
        · rw [maynardYValue, if_pos ⟨hbase.1, hrCop, hrSq⟩]
          have hmu :
              (ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 = 1 := by
            exact_mod_cast (squarefree_iff_moebius_sq_eq_one _).mp hrSq
          rw [hmu]
          ring
        · rw [maynardYValue, if_neg (fun h => hrSq h.2.2)]
          have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hrSq
          simp [hmu]
      · rw [if_neg (fun h => hrCop h.2.2)]
        rw [maynardYValue, if_neg (fun h => hrCop h.2.1)]
        simp
    · rw [if_neg hbase]
      rw [if_neg (fun h => hbase ⟨h.1, h.2.1⟩)]
  · simp [hdCop]

end BoundedGaps.Maynard
