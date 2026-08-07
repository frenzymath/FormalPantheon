import BoundedGaps.Maynard.MaynardLambdaMajorant

/-!
# Quotient tuples in the Maynard lambda bound

Maynard2013v3, equation `eq:LambdaSize` (source lines 304--316), replaces an
auxiliary tuple `r` divisible by a fixed divisor tuple `d` with the coordinate
quotient tuple. This file records the exact natural-number product and
squarefree consequences of that change of variables.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def divisorTupleQuotient {H : Finset ℕ} (d r : H → ℕ) : H → ℕ :=
  fun h => r h / d h

theorem divisorTuple_mul_quotient_coordinate
    {H : Finset ℕ} {d r : H → ℕ}
    (hdr : ∀ h : H, d h ∣ r h) (h : H) :
    d h * divisorTupleQuotient d r h = r h := by
  exact Nat.mul_div_cancel' (hdr h)

theorem divisorTupleProduct_mul_quotient
    {H : Finset ℕ} {d r : H → ℕ}
    (hdr : ∀ h : H, d h ∣ r h) :
    divisorTupleProduct H d *
        divisorTupleProduct H (divisorTupleQuotient d r) =
      divisorTupleProduct H r := by
  unfold divisorTupleProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro h hh
  exact divisorTuple_mul_quotient_coordinate hdr h

theorem divisorTupleProduct_quotient_eq_div
    {H : Finset ℕ} {d r : H → ℕ}
    (hdpos : 0 < divisorTupleProduct H d)
    (hdr : ∀ h : H, d h ∣ r h) :
    divisorTupleProduct H (divisorTupleQuotient d r) =
      divisorTupleProduct H r / divisorTupleProduct H d := by
  have hprod := divisorTupleProduct_mul_quotient hdr
  calc
    divisorTupleProduct H (divisorTupleQuotient d r) =
        (divisorTupleProduct H d *
          divisorTupleProduct H (divisorTupleQuotient d r)) /
            divisorTupleProduct H d :=
      (Nat.mul_div_cancel_left _ hdpos).symm
    _ = divisorTupleProduct H r / divisorTupleProduct H d := by rw [hprod]

theorem squarefree_divisorTupleProduct_and_quotient
    {H : Finset ℕ} {d r : H → ℕ}
    (hdr : ∀ h : H, d h ∣ r h)
    (hr : Squarefree (divisorTupleProduct H r)) :
    Squarefree (divisorTupleProduct H d) ∧
      Squarefree (divisorTupleProduct H (divisorTupleQuotient d r)) := by
  have hmul : Squarefree
      (divisorTupleProduct H d *
        divisorTupleProduct H (divisorTupleQuotient d r)) := by
    rw [divisorTupleProduct_mul_quotient hdr]
    exact hr
  exact ⟨hmul.of_mul_left, hmul.of_mul_right⟩

theorem coprime_divisorTupleProduct_quotient
    {H : Finset ℕ} {d r : H → ℕ}
    (hdr : ∀ h : H, d h ∣ r h)
    (hr : Squarefree (divisorTupleProduct H r)) :
    Nat.Coprime (divisorTupleProduct H d)
      (divisorTupleProduct H (divisorTupleQuotient d r)) := by
  apply Nat.coprime_of_squarefree_mul
  rw [divisorTupleProduct_mul_quotient hdr]
  exact hr

theorem divisorTupleQuotient_coordinate_pos
    {H : Finset ℕ} {d r : H → ℕ}
    (hdpos : ∀ h : H, 0 < d h)
    (hrpos : ∀ h : H, 0 < r h)
    (hdr : ∀ h : H, d h ∣ r h) (h : H) :
    0 < divisorTupleQuotient d r h := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd (hrpos h) (hdr h)
  · exact hdpos h

theorem divisorTupleQuotient_injOn
    {H : Finset ℕ} {d : H → ℕ} :
    Set.InjOn (divisorTupleQuotient d)
      {r : H → ℕ | ∀ h : H, d h ∣ r h} := by
  intro r hr s hs hrs
  funext h
  calc
    r h = d h * divisorTupleQuotient d r h :=
      (divisorTuple_mul_quotient_coordinate hr h).symm
    _ = d h * divisorTupleQuotient d s h := by rw [hrs]
    _ = s h := divisorTuple_mul_quotient_coordinate hs h

theorem divisorTupleProduct_quotient_cutoff_iff
    {H : Finset ℕ} {d r : H → ℕ} {R : ℕ}
    (hdr : ∀ h : H, d h ∣ r h) :
    divisorTupleProduct H d *
        divisorTupleProduct H (divisorTupleQuotient d r) < R ↔
      divisorTupleProduct H r < R := by
  rw [divisorTupleProduct_mul_quotient hdr]

end BoundedGaps.Maynard
