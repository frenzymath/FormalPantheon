import BoundedGaps.Maynard.ImprovedGPY.TupleSupport
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite Maynard divisor coefficients

Maynard2013v3, Proposition `MainProp` (source lines 202--216), defines the
multidimensional Selberg coefficient from a simplex function `F`. This module
records the finite source-shaped coefficient and its elementary support facts;
the asymptotic estimates remain separate obligations.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators ArithmeticFunction.Moebius

/-- Coordinatewise finite box for the auxiliary divisor tuple `r`. -/
def maynardDivisorTupleBox (H : Finset ℕ) (R : ℕ) : Finset (H → ℕ) :=
  Fintype.piFinset (fun _ : H => (Finset.range R).filter (fun n => 0 < n))

theorem mem_maynardDivisorTupleBox_iff
    {H : Finset ℕ} {R : ℕ} {r : H → ℕ} :
    r ∈ maynardDivisorTupleBox H R ↔ ∀ h : H, 1 ≤ r h ∧ r h < R := by
  classical
  simp only [maynardDivisorTupleBox, Fintype.mem_piFinset, Finset.mem_filter,
    Finset.mem_range, Nat.succ_le_iff]
  aesop

theorem maynardDivisorTupleBox_coordinate_lt
    {H : Finset ℕ} {R : ℕ} {r : H → ℕ}
    (hr : r ∈ maynardDivisorTupleBox H R) (h : H) : r h < R := by
  exact (mem_maynardDivisorTupleBox_iff.mp hr) h |>.2

/-- Finite divisor-tuple support consumed by the exact sieve sums. -/
noncomputable def maynardDivisorTupleSupport
    (H : Finset ℕ) (R W : ℕ) : Finset (H → ℕ) := by
  classical
  exact (maynardDivisorTupleBox H R).filter (IsMaynardDivisorTuple H R W)

theorem mem_maynardDivisorTupleSupport_iff
    {H : Finset ℕ} {R W : ℕ} {d : H → ℕ} :
    d ∈ maynardDivisorTupleSupport H R W ↔
      d ∈ maynardDivisorTupleBox H R ∧ IsMaynardDivisorTuple H R W d := by
  classical
  simp [maynardDivisorTupleSupport]

theorem isMaynardDivisorTuple_of_mem_support
    {H : Finset ℕ} {R W : ℕ} {d : H → ℕ}
    (hd : d ∈ maynardDivisorTupleSupport H R W) :
    IsMaynardDivisorTuple H R W d :=
  (mem_maynardDivisorTupleSupport_iff.mp hd).2

/-- The finite source-shaped Maynard coefficient for a function on `H`-tuples.

The positive coordinate box and explicit product cutoff keep the auxiliary sum
finite and record the support used in the source when `F` is simplex-supported.
-/
noncomputable def maynardCoefficient
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ)
    (d : H → ℕ) : ℝ :=
  if Nat.Coprime (divisorTupleProduct H d) W then
    (∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * d h) *
      ∑ r ∈ maynardDivisorTupleBox H R,
        if divisorTupleProduct H r < R ∧
            (∀ h : H, d h ∣ r h) ∧
            Nat.Coprime (divisorTupleProduct H r) W then
          ((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
            ∏ h : H, (Nat.totient (r h) : ℝ)) *
            F (fun h => Real.log (r h) / Real.log R)
        else 0
  else 0

theorem maynardCoefficient_eq_zero_of_not_coprime
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ) (d : H → ℕ)
    (h : ¬Nat.Coprime (divisorTupleProduct H d) W) :
    maynardCoefficient H R W F d = 0 := by
  simp [maynardCoefficient, h]

theorem maynardCoefficient_eq_zero_of_not_squarefree_product
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ) (d : H → ℕ)
    (h : ¬Squarefree (divisorTupleProduct H d)) :
    maynardCoefficient H R W F d = 0 := by
  classical
  unfold maynardCoefficient
  by_cases hcop : Nat.Coprime (divisorTupleProduct H d) W
  · rw [if_pos hcop]
    have hsum :
        (∑ r ∈ maynardDivisorTupleBox H R,
          if divisorTupleProduct H r < R ∧
              (∀ h : H, d h ∣ r h) ∧
              Nat.Coprime (divisorTupleProduct H r) W then
            ((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
              ∏ h : H, (Nat.totient (r h) : ℝ)) *
              F (fun h => Real.log (r h) / Real.log R)
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      by_cases hcond : divisorTupleProduct H r < R ∧
          (∀ h : H, d h ∣ r h) ∧
          Nat.Coprime (divisorTupleProduct H r) W
      · have hprod : divisorTupleProduct H d ∣ divisorTupleProduct H r := by
          unfold divisorTupleProduct
          exact Finset.prod_dvd_prod_of_dvd d r (fun h _ => hcond.2.1 h)
        have hnot_r : ¬Squarefree (divisorTupleProduct H r) := by
          intro hsq
          exact h (hsq.squarefree_of_dvd hprod)
        have hmu : ArithmeticFunction.moebius (divisorTupleProduct H r) = 0 :=
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot_r
        rw [if_pos hcond]
        simp [hmu]
      · rw [if_neg hcond]
    rw [hsum, mul_zero]
  · simp [hcop]

theorem maynardCoefficient_eq_zero_of_product_not_lt
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ) (d : H → ℕ)
    (h : ¬divisorTupleProduct H d < R) :
    maynardCoefficient H R W F d = 0 := by
  classical
  unfold maynardCoefficient
  by_cases hcop : Nat.Coprime (divisorTupleProduct H d) W
  · rw [if_pos hcop]
    have hsum :
        (∑ r ∈ maynardDivisorTupleBox H R,
          if divisorTupleProduct H r < R ∧
              (∀ h : H, d h ∣ r h) ∧
              Nat.Coprime (divisorTupleProduct H r) W then
            ((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
              ∏ h : H, (Nat.totient (r h) : ℝ)) *
              F (fun h => Real.log (r h) / Real.log R)
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      by_cases hcond : divisorTupleProduct H r < R ∧
          (∀ h : H, d h ∣ r h) ∧
          Nat.Coprime (divisorTupleProduct H r) W
      · have hprod : divisorTupleProduct H d ∣ divisorTupleProduct H r := by
          unfold divisorTupleProduct
          exact Finset.prod_dvd_prod_of_dvd d r (fun h _ => hcond.2.1 h)
        have hrpos : 0 < divisorTupleProduct H r := by
          unfold divisorTupleProduct
          apply Finset.prod_pos
          intro h _
          exact ((mem_maynardDivisorTupleBox_iff.mp hr) h).1
        have hle : divisorTupleProduct H d ≤ divisorTupleProduct H r :=
          Nat.le_of_dvd hrpos hprod
        exact False.elim (h (lt_of_le_of_lt hle hcond.1))
      · rw [if_neg hcond]
    rw [hsum, mul_zero]
  · simp [hcop]

theorem maynardCoefficient_eq_zero_of_not_isMaynardDivisorTuple
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ) (d : H → ℕ)
    (h : ¬IsMaynardDivisorTuple H R W d) :
    maynardCoefficient H R W F d = 0 := by
  by_cases hcop : Nat.Coprime (divisorTupleProduct H d) W
  · by_cases hsq : Squarefree (divisorTupleProduct H d)
    · by_cases hlt : divisorTupleProduct H d < R
      · exact False.elim (h ⟨hlt, hcop, hsq⟩)
      · exact maynardCoefficient_eq_zero_of_product_not_lt H R W F d hlt
    · exact maynardCoefficient_eq_zero_of_not_squarefree_product H R W F d hsq
  · exact maynardCoefficient_eq_zero_of_not_coprime H R W F d hcop

theorem maynardCoefficient_ne_zero_mem_support
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ) (d : H → ℕ)
    (h : maynardCoefficient H R W F d ≠ 0) :
    d ∈ maynardDivisorTupleSupport H R W := by
  classical
  have hd : IsMaynardDivisorTuple H R W d := by
    by_contra hnot
    exact h (maynardCoefficient_eq_zero_of_not_isMaynardDivisorTuple H R W F d hnot)
  have hprod_pos : 0 < divisorTupleProduct H d :=
    Nat.pos_of_ne_zero hd.2.2.ne_zero
  have hbox : d ∈ maynardDivisorTupleBox H R :=
    mem_maynardDivisorTupleBox_iff.mpr fun h => by
      have hd_ne : d h ≠ 0 := by
        intro hzero
        apply (Nat.ne_of_gt hprod_pos)
        unfold divisorTupleProduct
        exact Finset.prod_eq_zero (Finset.mem_univ h) (by simp [hzero])
      have hcoord_le : d h ≤ divisorTupleProduct H d :=
        Nat.le_of_dvd hprod_pos (divisorTupleCoordinate_dvd_product d h)
      exact ⟨Nat.one_le_iff_ne_zero.mpr hd_ne,
        lt_of_le_of_lt hcoord_le hd.1⟩
  exact mem_maynardDivisorTupleSupport_iff.mpr ⟨hbox, hd⟩

theorem maynardCoefficient_eq_zero_of_not_mem_support
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ) (d : H → ℕ)
    (h : d ∉ maynardDivisorTupleSupport H R W) :
    maynardCoefficient H R W F d = 0 := by
  by_contra hne
  exact h (maynardCoefficient_ne_zero_mem_support H R W F d hne)

theorem abs_maynardCoefficient_le_of_bound
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ)
    (d : H → ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ x, |F x| ≤ B) :
    |maynardCoefficient H R W F d| ≤
      (divisorTupleProduct H d : ℝ) *
        (maynardDivisorTupleBox H R).card * B := by
  classical
  have hmu_real : ∀ n : ℕ, |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    intro n
    rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]
  have houter :
      |∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * d h| ≤
        (divisorTupleProduct H d : ℝ) := by
    calc
      |∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * d h| =
          ∏ h : H, |(ArithmeticFunction.moebius (d h) : ℝ) * d h| := by
            rw [Finset.abs_prod]
      _ ≤ ∏ h : H, (d h : ℝ) := by
        apply Finset.prod_le_prod
        · intro h _
          exact abs_nonneg _
        · intro h _
          have hd_nonneg : (0 : ℝ) ≤ (d h : ℝ) := by positivity
          calc
            |(ArithmeticFunction.moebius (d h) : ℝ) * d h| =
                |(ArithmeticFunction.moebius (d h) : ℝ)| * |(d h : ℝ)| :=
              abs_mul _ _
            _ = |(ArithmeticFunction.moebius (d h) : ℝ)| * (d h : ℝ) := by
              rw [abs_of_nonneg hd_nonneg]
            _ ≤ 1 * (d h : ℝ) :=
              mul_le_mul_of_nonneg_right (hmu_real (d h)) hd_nonneg
            _ = (d h : ℝ) := one_mul _
      _ = (divisorTupleProduct H d : ℝ) := by
        simp [divisorTupleProduct]
  have hterm : ∀ r ∈ maynardDivisorTupleBox H R,
      |if divisorTupleProduct H r < R ∧
          (∀ h : H, d h ∣ r h) ∧
          Nat.Coprime (divisorTupleProduct H r) W then
        ((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
          ∏ h : H, (Nat.totient (r h) : ℝ)) *
          F (fun h => Real.log (r h) / Real.log R)
      else 0| ≤ B := by
    intro r hr
    by_cases hcond : divisorTupleProduct H r < R ∧
        (∀ h : H, d h ∣ r h) ∧
        Nat.Coprime (divisorTupleProduct H r) W
    · rw [if_pos hcond, abs_mul]
      have hrpos : ∀ h : H, 0 < r h := by
        intro h
        exact Nat.lt_of_lt_of_le Nat.zero_lt_one
          ((mem_maynardDivisorTupleBox_iff.mp hr) h).1
      have hden : 1 ≤ ∏ h : H, (Nat.totient (r h) : ℝ) := by
        apply Finset.one_le_prod
        intro h _
        have htot : 0 < Nat.totient (r h) := Nat.totient_pos.mpr (hrpos h)
        exact_mod_cast (Nat.succ_le_iff.mpr htot)
      have hden_pos : 0 < ∏ h : H, (Nat.totient (r h) : ℝ) :=
        lt_of_lt_of_le zero_lt_one hden
      have hmu_sq :
          |(ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2| ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or (divisorTupleProduct H r) with h | h | h <;>
          simp [h]
      have hfrac :
          |(ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
              ∏ h : H, (Nat.totient (r h) : ℝ)| ≤ 1 := by
        rw [abs_div, abs_of_pos hden_pos]
        exact (div_le_iff₀ hden_pos).2 (by simpa using hmu_sq.trans hden)
      simpa only [one_mul] using
        (mul_le_mul hfrac
          (hF (fun h => Real.log (r h) / Real.log R))
          (abs_nonneg _) zero_le_one)
    · rw [if_neg hcond]
      simpa using hB
  have hsum :
      |∑ r ∈ maynardDivisorTupleBox H R,
          if divisorTupleProduct H r < R ∧
              (∀ h : H, d h ∣ r h) ∧
              Nat.Coprime (divisorTupleProduct H r) W then
            ((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
              ∏ h : H, (Nat.totient (r h) : ℝ)) *
              F (fun h => Real.log (r h) / Real.log R)
          else 0| ≤ (maynardDivisorTupleBox H R).card * B := by
    calc
      |∑ r ∈ maynardDivisorTupleBox H R,
          if divisorTupleProduct H r < R ∧
              (∀ h : H, d h ∣ r h) ∧
              Nat.Coprime (divisorTupleProduct H r) W then
            ((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
              ∏ h : H, (Nat.totient (r h) : ℝ)) *
              F (fun h => Real.log (r h) / Real.log R)
          else 0| ≤
          ∑ r ∈ maynardDivisorTupleBox H R,
            |if divisorTupleProduct H r < R ∧
                (∀ h : H, d h ∣ r h) ∧
                Nat.Coprime (divisorTupleProduct H r) W then
              ((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
                ∏ h : H, (Nat.totient (r h) : ℝ)) *
                F (fun h => Real.log (r h) / Real.log R)
            else 0| := by
              exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ maynardDivisorTupleBox H R, B := by
        apply Finset.sum_le_sum
        intro r hr
        exact hterm r hr
      _ = (maynardDivisorTupleBox H R).card * B := by
        simp
  unfold maynardCoefficient
  by_cases hcop : Nat.Coprime (divisorTupleProduct H d) W
  · rw [if_pos hcop, abs_mul]
    calc
      |∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * d h| *
          |∑ r ∈ maynardDivisorTupleBox H R,
              if divisorTupleProduct H r < R ∧
                  (∀ h : H, d h ∣ r h) ∧
                  Nat.Coprime (divisorTupleProduct H r) W then
                ((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
                  ∏ h : H, (Nat.totient (r h) : ℝ)) *
                  F (fun h => Real.log (r h) / Real.log R)
              else 0| ≤
          (divisorTupleProduct H d : ℝ) *
            ((maynardDivisorTupleBox H R).card * B) := by
              calc
                _ ≤ |∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * d h| *
                    ((maynardDivisorTupleBox H R).card * B) :=
                  mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
                _ ≤ (divisorTupleProduct H d : ℝ) *
                    ((maynardDivisorTupleBox H R).card * B) :=
                  mul_le_mul_of_nonneg_right houter
                    (mul_nonneg (Nat.cast_nonneg _) hB)
      _ = (divisorTupleProduct H d : ℝ) *
            (maynardDivisorTupleBox H R).card * B := by ring
  · simp [hcop]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hB

end BoundedGaps.Maynard
