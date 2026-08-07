import BoundedGaps.Maynard.MaynardLambdaTotientRegrouping

noncomputable section

/-!
# The concrete Maynard coefficient and its quotient majorant

Maynard2013v3, equation `eq:LambdaSize` (source lines 304--316), bounds the
finite coefficient by first restricting its auxiliary tuple to squarefree
total product, then writing that tuple as the fixed divisor tuple times a
quotient tuple. This file proves that exact comparison.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators
local instance coefficientMajorantDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem lambdaQuotientWeightSum_eq_auxiliary_sum
    (H : Finset ℕ) (R : ℕ) (d : H → ℕ) :
    lambdaQuotientWeightSum H R d =
      (divisorTupleProduct H d : ℝ) *
        ∑ r ∈ lambdaAuxiliaryTupleSupport H R d,
          (Nat.totient (divisorTupleProduct H r) : ℝ)⁻¹ := by
  classical
  unfold lambdaQuotientWeightSum lambdaQuotientTupleSupport
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hrData := mem_lambdaAuxiliaryTupleSupport_iff.mp hr
    rw [divisorTupleProduct_mul_quotient hrData.2.2.1]
    simp [div_eq_mul_inv]
  · exact divisorTupleQuotient_injOn.mono fun r hr =>
      (mem_lambdaAuxiliaryTupleSupport_iff.mp hr).2.2.1

theorem abs_maynardCoefficient_le_quotientWeightSum
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ)
    (d : H → ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ x, |F x| ≤ B)
    (hd : d ∈ maynardDivisorTupleSupport H R W) :
    |maynardCoefficient H R W F d| ≤
      B * lambdaQuotientWeightSum H R d := by
  classical
  let box := maynardDivisorTupleBox H R
  have hdData := isMaynardDivisorTuple_of_mem_support hd
  have hcop : Nat.Coprime (divisorTupleProduct H d) W := hdData.2.1
  have houter :
      |∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * d h| ≤
        (divisorTupleProduct H d : ℝ) := by
    rw [Finset.abs_prod]
    calc
      (∏ h : H, |(ArithmeticFunction.moebius (d h) : ℝ) * d h|) ≤
          ∏ h : H, (d h : ℝ) := by
        apply Finset.prod_le_prod
        · intro h _
          exact abs_nonneg _
        · intro h _
          have hdAbs : |(d h : ℝ)| = (d h : ℝ) :=
            abs_of_nonneg (Nat.cast_nonneg (d h))
          rw [abs_mul, hdAbs]
          have hmuAbs : |(ArithmeticFunction.moebius (d h) : ℝ)| ≤ 1 := by
            rcases ArithmeticFunction.moebius_eq_or (d h) with hmu | hmu | hmu <;>
              simp [hmu]
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hmuAbs (Nat.cast_nonneg (d h))
      _ = (divisorTupleProduct H d : ℝ) := by
        simp [divisorTupleProduct]
  have hterm : ∀ r ∈ box,
      |if divisorTupleProduct H r < R ∧
          (∀ h : H, d h ∣ r h) ∧
          Nat.Coprime (divisorTupleProduct H r) W then
        ((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
          ∏ h : H, (Nat.totient (r h) : ℝ)) *
          F (fun h => Real.log (r h) / Real.log R)
        else 0| ≤
      if divisorTupleProduct H r < R ∧
          (∀ h : H, d h ∣ r h) ∧
          Squarefree (divisorTupleProduct H r) then
        B * (Nat.totient (divisorTupleProduct H r) : ℝ)⁻¹
      else 0 := by
    intro r hr
    by_cases hsq : Squarefree (divisorTupleProduct H r)
    · by_cases hcond : divisorTupleProduct H r < R ∧
          (∀ h : H, d h ∣ r h) ∧
          Nat.Coprime (divisorTupleProduct H r) W
      · rw [if_pos hcond, if_pos ⟨hcond.1, hcond.2.1, hsq⟩]
        have hmu :
            (ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 = 1 := by
          exact_mod_cast (squarefree_iff_moebius_sq_eq_one _).mp hsq
        have htotient :
            (∏ h : H, (Nat.totient (r h) : ℝ)) =
              (Nat.totient (divisorTupleProduct H r) : ℝ) := by
          exact_mod_cast (totient_divisorTupleProduct_eq_prod hsq).symm
        have htotientNonneg :
            0 ≤ (Nat.totient (divisorTupleProduct H r) : ℝ) := by positivity
        calc
          |((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
                ∏ h : H, (Nat.totient (r h) : ℝ)) *
              F (fun h => Real.log (r h) / Real.log R)| =
              (Nat.totient (divisorTupleProduct H r) : ℝ)⁻¹ *
                |F (fun h => Real.log (r h) / Real.log R)| := by
            rw [hmu, htotient, abs_mul, one_div, abs_inv,
              abs_of_nonneg htotientNonneg]
          _ ≤ (Nat.totient (divisorTupleProduct H r) : ℝ)⁻¹ * B :=
            mul_le_mul_of_nonneg_left
              (hF (fun h => Real.log (r h) / Real.log R)) (by positivity)
          _ = B * (Nat.totient (divisorTupleProduct H r) : ℝ)⁻¹ := by ring
      · rw [if_neg hcond]
        by_cases haux : divisorTupleProduct H r < R ∧
            (∀ h : H, d h ∣ r h) ∧
            Squarefree (divisorTupleProduct H r)
        · rw [if_pos haux]
          simpa only [abs_zero] using mul_nonneg hB
            (inv_nonneg.mpr (Nat.cast_nonneg _))
        · rw [if_neg haux]
          norm_num
    · have haux : ¬(divisorTupleProduct H r < R ∧
          (∀ h : H, d h ∣ r h) ∧
          Squarefree (divisorTupleProduct H r)) := fun h => hsq h.2.2
      rw [if_neg haux]
      by_cases hcond : divisorTupleProduct H r < R ∧
          (∀ h : H, d h ∣ r h) ∧
          Nat.Coprime (divisorTupleProduct H r) W
      · rw [if_pos hcond]
        have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
        simp [hmu]
      · rw [if_neg hcond]
        norm_num
  have hinner :
      |∑ r ∈ box,
          if divisorTupleProduct H r < R ∧
              (∀ h : H, d h ∣ r h) ∧
              Nat.Coprime (divisorTupleProduct H r) W then
            ((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
              ∏ h : H, (Nat.totient (r h) : ℝ)) *
              F (fun h => Real.log (r h) / Real.log R)
          else 0| ≤
        B * ∑ r ∈ lambdaAuxiliaryTupleSupport H R d,
          (Nat.totient (divisorTupleProduct H r) : ℝ)⁻¹ := by
    calc
      |∑ r ∈ box,
          if divisorTupleProduct H r < R ∧
              (∀ h : H, d h ∣ r h) ∧
              Nat.Coprime (divisorTupleProduct H r) W then
            ((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
              ∏ h : H, (Nat.totient (r h) : ℝ)) *
              F (fun h => Real.log (r h) / Real.log R)
          else 0| ≤
          ∑ r ∈ box,
            |if divisorTupleProduct H r < R ∧
                (∀ h : H, d h ∣ r h) ∧
                Nat.Coprime (divisorTupleProduct H r) W then
              ((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
                ∏ h : H, (Nat.totient (r h) : ℝ)) *
                F (fun h => Real.log (r h) / Real.log R)
            else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ box,
          if divisorTupleProduct H r < R ∧
              (∀ h : H, d h ∣ r h) ∧
              Squarefree (divisorTupleProduct H r) then
            B * (Nat.totient (divisorTupleProduct H r) : ℝ)⁻¹
          else 0 := Finset.sum_le_sum fun r hr => hterm r hr
      _ = ∑ r ∈ lambdaAuxiliaryTupleSupport H R d,
          B * (Nat.totient (divisorTupleProduct H r) : ℝ)⁻¹ := by
        rw [lambdaAuxiliaryTupleSupport, Finset.sum_filter]
      _ = B * ∑ r ∈ lambdaAuxiliaryTupleSupport H R d,
          (Nat.totient (divisorTupleProduct H r) : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
  rw [maynardCoefficient, if_pos hcop, abs_mul]
  calc
    |∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * d h| *
        |∑ r ∈ box,
          if divisorTupleProduct H r < R ∧
              (∀ h : H, d h ∣ r h) ∧
              Nat.Coprime (divisorTupleProduct H r) W then
            ((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
              ∏ h : H, (Nat.totient (r h) : ℝ)) *
              F (fun h => Real.log (r h) / Real.log R)
          else 0| ≤
        (divisorTupleProduct H d : ℝ) *
          (B * ∑ r ∈ lambdaAuxiliaryTupleSupport H R d,
            (Nat.totient (divisorTupleProduct H r) : ℝ)⁻¹) := by
      exact mul_le_mul houter hinner (abs_nonneg _) (by positivity)
    _ = B * lambdaQuotientWeightSum H R d := by
      rw [lambdaQuotientWeightSum_eq_auxiliary_sum]
      ring

end BoundedGaps.Maynard
