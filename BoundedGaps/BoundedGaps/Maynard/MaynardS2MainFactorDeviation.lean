import BoundedGaps.Maynard.MaynardS2MainFaceNormalization
import BoundedGaps.Maynard.MaynardS1CrossPrime
import BoundedGaps.Maynard.MaynardReciprocalSquareTail

noncomputable section

/-!
# Deviation of Maynard's restricted S2 arithmetic factor

The local factor is converted to its finite prime Euler product and bounded
using the reciprocal-totient-square tail. This formalizes Maynard2013v3,
source lines 438--440, with the fixed dimension dependence explicit.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable def maynardS2ScalarArithmeticFactor (n : ℕ) : ℝ :=
  (maynardS2G n : ℝ) * (n : ℝ) / (Nat.totient n : ℝ) ^ 2

theorem one_sub_prod_one_sub_nonneg_le_sum
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf1 : ∀ i ∈ s, f i ≤ 1) :
    0 ≤ 1 - ∏ i ∈ s, (1 - f i) ∧
      1 - ∏ i ∈ s, (1 - f i) ≤ ∑ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa0 : 0 ≤ f a := hf0 a (Finset.mem_insert_self a s)
      have hfa1 : f a ≤ 1 := hf1 a (Finset.mem_insert_self a s)
      have ih' := ih
        (fun i hi => hf0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => hf1 i (Finset.mem_insert_of_mem hi))
      have hprodNonneg : 0 ≤ ∏ i ∈ s, (1 - f i) := by
        apply Finset.prod_nonneg
        intro i hi
        exact sub_nonneg.mpr (hf1 i (Finset.mem_insert_of_mem hi))
      have hprodLe : ∏ i ∈ s, (1 - f i) ≤ 1 := by linarith [ih'.1]
      have hmulLe : (1 - f a) * ∏ i ∈ s, (1 - f i) ≤ 1 := by
        have hleftNonneg : 0 ≤ 1 - f a := by linarith
        have hleftLe : 1 - f a ≤ 1 := by linarith
        nlinarith [mul_nonneg hleftNonneg hprodNonneg,
          mul_le_mul hleftLe hprodLe hprodNonneg zero_le_one]
      have hrestLe :
          (1 - f a) * (1 - ∏ i ∈ s, (1 - f i)) ≤
            1 - ∏ i ∈ s, (1 - f i) := by
        exact mul_le_of_le_one_left ih'.1 (by linarith)
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      constructor
      · linarith
      · have hdecomp :
            1 - (1 - f a) * ∏ i ∈ s, (1 - f i) =
              f a + (1 - f a) *
                (1 - ∏ i ∈ s, (1 - f i)) := by ring
        rw [hdecomp]
        linarith [ih'.2, hrestLe]

theorem maynardS2ScalarArithmeticFactor_eq_primeProduct
    {n : ℕ} (hn : Squarefree n) :
    maynardS2ScalarArithmeticFactor n =
      ∏ p ∈ n.primeFactors,
        (1 - (1 : ℝ) / (Nat.totient p : ℝ) ^ 2) := by
  have hnProd := Nat.prod_primeFactors_of_squarefree hn
  have hphi := totient_eq_prod_primeFactors_of_squarefree hn
  unfold maynardS2ScalarArithmeticFactor
  rw [maynardS2G_apply hn.ne_zero, hphi]
  have hnCast : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast hnProd.symm
  rw [hnCast]
  push_cast
  rw [← Finset.prod_pow]
  rw [← Finset.prod_mul_distrib]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hpMem
  have hp := Nat.prime_of_mem_primeFactors hpMem
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le,
    Nat.cast_sub hp.two_le]
  have hpSub : (p : ℝ) - 1 ≠ 0 := by
    have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  field_simp [hpSub]
  ring

theorem maynardS2ScalarArithmeticFactor_mem_Icc
    {n : ℕ} (hn : Squarefree n) :
    maynardS2ScalarArithmeticFactor n ∈ Set.Icc (0 : ℝ) 1 := by
  rw [maynardS2ScalarArithmeticFactor_eq_primeProduct hn]
  have hweight (p : ℕ) (hp : p.Prime) :
      (1 : ℝ) / (Nat.totient p : ℝ) ^ 2 ≤ 1 := by
    have hphiPos : (0 : ℝ) < Nat.totient p := by
      exact_mod_cast Nat.totient_pos.mpr hp.pos
    have hphiOne : (1 : ℝ) ≤ Nat.totient p := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.totient_pos.mpr hp.pos)))
    apply (div_le_one (sq_pos_of_pos hphiPos)).2
    nlinarith
  constructor
  · apply Finset.prod_nonneg
    intro p hpMem
    have hp := Nat.prime_of_mem_primeFactors hpMem
    exact sub_nonneg.mpr (hweight p hp)
  · apply Finset.prod_le_one
    · intro p hpMem
      have hp := Nat.prime_of_mem_primeFactors hpMem
      exact sub_nonneg.mpr (hweight p hp)
    · intro p hpMem
      have hnonneg : (0 : ℝ) ≤
          1 / (Nat.totient p : ℝ) ^ 2 := by positivity
      linarith

theorem abs_maynardS2ScalarArithmeticFactor_sub_one_le
    {D n : ℕ} (hD : 0 < D) (hn : Squarefree n)
    (hcop : Nat.Coprime n (primorial D)) :
    |maynardS2ScalarArithmeticFactor n - 1| ≤ 8 / (D : ℝ) := by
  have hfactor := maynardS2ScalarArithmeticFactor_mem_Icc hn
  rw [abs_of_nonpos (sub_nonpos.mpr hfactor.2), neg_sub]
  rw [maynardS2ScalarArithmeticFactor_eq_primeProduct hn]
  let weight : ℕ → ℝ := fun p =>
    (1 : ℝ) / (Nat.totient p : ℝ) ^ 2
  have hweight_le (p : ℕ) (hp : p.Prime) : weight p ≤ 1 := by
    have hphiPos : (0 : ℝ) < Nat.totient p := by
      exact_mod_cast Nat.totient_pos.mpr hp.pos
    have hphiOne : (1 : ℝ) ≤ Nat.totient p := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.totient_pos.mpr hp.pos)))
    unfold weight
    apply (div_le_one (sq_pos_of_pos hphiPos)).2
    nlinarith
  have hdev := one_sub_prod_one_sub_nonneg_le_sum n.primeFactors weight
    (fun p hp => by unfold weight; positivity)
    (fun p hp => hweight_le p (Nat.prime_of_mem_primeFactors hp))
  have hsubset : n.primeFactors ⊆
      (Finset.Ico (D + 1) (n + 1)).filter Nat.Prime := by
    intro p hpMem
    have hp := Nat.prime_of_mem_primeFactors hpMem
    have hpDvd : p ∣ n := Nat.dvd_of_mem_primeFactors hpMem
    have hpGt : D < p :=
      prime_gt_of_dvd_coprime_primorial hp hpDvd hcop
    have hpLe : p ≤ n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero) hpDvd
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hp⟩
  calc
    1 - ∏ p ∈ n.primeFactors,
        (1 - (1 : ℝ) / (Nat.totient p : ℝ) ^ 2) ≤
        ∑ p ∈ n.primeFactors, weight p := hdev.2
    _ ≤ ∑ p ∈ (Finset.Ico (D + 1) (n + 1)).filter Nat.Prime,
        weight p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hp hpNot
      unfold weight
      positivity
    _ = primeTotientSquareTail D (n + 1) := by
      rfl
    _ ≤ 8 / (D : ℝ) := primeTotientSquareTail_le hD

theorem abs_maynardS2MainFaceArithmeticFactor_sub_one_le
    {H : Finset ℕ} {R D : ℕ} (m : H) {r : H → ℕ}
    (hD : 0 < D)
    (hr : IsMaynardDivisorTuple H R (primorial D) r) :
    |maynardS2MainFaceArithmeticFactor H m r - 1| ≤
      8 * ((Finset.univ.erase m).card : ℝ) / (D : ℝ) := by
  classical
  let off : Finset H := Finset.univ.erase m
  have hfactor : maynardS2MainFaceArithmeticFactor H m r =
      ∏ h ∈ off, maynardS2ScalarArithmeticFactor (r h) := by
    unfold maynardS2MainFaceArithmeticFactor
      maynardS2ScalarArithmeticFactor
    rfl
  have hlocal (h : H) :
      maynardS2ScalarArithmeticFactor (r h) ∈ Set.Icc (0 : ℝ) 1 :=
    maynardS2ScalarArithmeticFactor_mem_Icc (hr.coordinate_squarefree h)
  have hdev := one_sub_prod_one_sub_nonneg_le_sum off
    (fun h => 1 - maynardS2ScalarArithmeticFactor (r h))
    (fun h hh => sub_nonneg.mpr (hlocal h).2)
    (fun h hh => by linarith [(hlocal h).1])
  rw [hfactor]
  have hprodLe :
      (∏ h ∈ off, maynardS2ScalarArithmeticFactor (r h)) ≤ 1 := by
    have := hdev.1
    simp only [sub_sub_cancel] at this
    linarith
  rw [abs_of_nonpos (sub_nonpos.mpr hprodLe), neg_sub]
  calc
    1 - ∏ h ∈ off, maynardS2ScalarArithmeticFactor (r h) ≤
        ∑ h ∈ off, (1 - maynardS2ScalarArithmeticFactor (r h)) := by
      simpa only [sub_sub_cancel] using hdev.2
    _ ≤ ∑ _h ∈ off, (8 / (D : ℝ)) := by
      apply Finset.sum_le_sum
      intro h hh
      have habs := abs_maynardS2ScalarArithmeticFactor_sub_one_le hD
        (hr.coordinate_squarefree h) (hr.coordinate_coprime_W h)
      rw [abs_of_nonpos (sub_nonpos.mpr (hlocal h).2), neg_sub] at habs
      exact habs
    _ = 8 * (off.card : ℝ) / (D : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

end BoundedGaps.Maynard
