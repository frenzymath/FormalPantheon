import Mathlib.Algebra.Order.Antidiag.Nat

import BoundedGaps.Maynard.ImprovedGPY.S2FiberBounds

noncomputable section

/-!
# Ordered-factor S2 fiber bounds

Maynard2013v3, in the error part of `lmm:S2Expression1` (source lines
363--367), controls repeated divisor pairs by a fixed-order divisor function.
This file gives an exact gcd/quotient encoding into `Nat.finMulAntidiag` for
the CRT modulus. One extra coordinate records the fixed pre-sieving factor
`W`; removing it to match the source's `tau_{3k}` notation remains separate.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.omega BigOperators
local instance orderedFactorDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def divisorPairFactorEncoding
    (H : Finset ℕ) (W : ℕ) (d e : H → ℕ) :
    Option (H × Fin 3) → ℕ
  | none => W
  | some (h, j) =>
      if j = 0 then Nat.gcd (d h) (e h)
      else if j = 1 then d h / Nat.gcd (d h) (e h)
      else e h / Nat.gcd (d h) (e h)

def divisorPairFinFactorEncoding
    (H : Finset ℕ) (W : ℕ) (d e : H → ℕ) :
    Fin (Fintype.card (Option (H × Fin 3))) → ℕ :=
  fun i => divisorPairFactorEncoding H W d e
    ((Fintype.equivFin (Option (H × Fin 3))).symm i)

theorem gcd_mul_div_mul_div_eq_lcm (a b : ℕ) :
    Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b) =
      Nat.lcm a b := by
  by_cases hg : Nat.gcd a b = 0
  · obtain ⟨rfl, rfl⟩ := Nat.gcd_eq_zero_iff.mp hg
    simp
  · apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hg)
    calc
      (Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b)) *
          Nat.gcd a b =
          (Nat.gcd a b * (a / Nat.gcd a b)) *
            (Nat.gcd a b * (b / Nat.gcd a b)) := by ring
      _ = a * b := by
        rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left a b),
          Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)]
      _ = Nat.lcm a b * Nat.gcd a b := (Nat.lcm_mul_gcd a b).symm

theorem divisorPairFactorEncoding_prod
    (H : Finset ℕ) (W : ℕ) (d e : H → ℕ) :
    (∏ i, divisorPairFactorEncoding H W d e i) =
      divisorPairModulus H W d e := by
  rw [Fintype.prod_option, Fintype.prod_prod_type]
  unfold divisorPairModulus
  simp only [divisorPairFactorEncoding]
  congr 1
  apply Finset.prod_congr rfl
  intro h hh
  rw [Fin.prod_univ_three]
  simp only [↓reduceIte, OfNat.ofNat]
  exact gcd_mul_div_mul_div_eq_lcm (d h) (e h)

theorem divisorPairFinFactorEncoding_prod
    (H : Finset ℕ) (W : ℕ) (d e : H → ℕ) :
    (∏ i, divisorPairFinFactorEncoding H W d e i) =
      divisorPairModulus H W d e := by
  calc
    (∏ i, divisorPairFinFactorEncoding H W d e i) =
        ∏ i : Option (H × Fin 3), divisorPairFactorEncoding H W d e i := by
      apply Fintype.prod_equiv
        (Fintype.equivFin (Option (H × Fin 3))).symm
      intro i
      rfl
    _ = divisorPairModulus H W d e :=
      divisorPairFactorEncoding_prod H W d e

theorem divisorPairFactorEncoding_injective (H : Finset ℕ) (W : ℕ) :
    Function.Injective (fun de : (H → ℕ) × (H → ℕ) =>
      divisorPairFactorEncoding H W de.1 de.2) := by
  rintro ⟨d, e⟩ ⟨d', e'⟩ henc
  apply Prod.ext
  · funext h
    have hg : Nat.gcd (d h) (e h) = Nat.gcd (d' h) (e' h) := by
      simpa [divisorPairFactorEncoding] using congrFun henc (some (h, 0))
    have hd : d h / Nat.gcd (d h) (e h) =
        d' h / Nat.gcd (d' h) (e' h) := by
      simpa [divisorPairFactorEncoding] using congrFun henc (some (h, 1))
    calc
      d h = Nat.gcd (d h) (e h) *
          (d h / Nat.gcd (d h) (e h)) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_left (d h) (e h))).symm
      _ = Nat.gcd (d' h) (e' h) *
          (d' h / Nat.gcd (d' h) (e' h)) := by rw [hd, hg]
      _ = d' h := Nat.mul_div_cancel' (Nat.gcd_dvd_left (d' h) (e' h))
  · funext h
    have hg : Nat.gcd (d h) (e h) = Nat.gcd (d' h) (e' h) := by
      simpa [divisorPairFactorEncoding] using congrFun henc (some (h, 0))
    have he : e h / Nat.gcd (d h) (e h) =
        e' h / Nat.gcd (d' h) (e' h) := by
      simpa [divisorPairFactorEncoding] using congrFun henc (some (h, 2))
    calc
      e h = Nat.gcd (d h) (e h) *
          (e h / Nat.gcd (d h) (e h)) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_right (d h) (e h))).symm
      _ = Nat.gcd (d' h) (e' h) *
          (e' h / Nat.gcd (d' h) (e' h)) := by rw [he, hg]
      _ = e' h := Nat.mul_div_cancel' (Nat.gcd_dvd_right (d' h) (e' h))

theorem divisorPairFinFactorEncoding_injective (H : Finset ℕ) (W : ℕ) :
    Function.Injective (fun de : (H → ℕ) × (H → ℕ) =>
      divisorPairFinFactorEncoding H W de.1 de.2) := by
  intro de de' henc
  apply divisorPairFactorEncoding_injective H W
  funext i
  have hi := congrFun henc ((Fintype.equivFin (Option (H × Fin 3))) i)
  simpa [divisorPairFinFactorEncoding] using hi

def compatiblePairShiftFinFactorEncoding
    (H : Finset ℕ) (W : ℕ)
    (i : (((H → ℕ) × (H → ℕ)) × H)) :
    (Fin (Fintype.card (Option (H × Fin 3))) → ℕ) × H :=
  (divisorPairFinFactorEncoding H W i.1.1 i.1.2, i.2)

def compatiblePairShiftFinFactorContainer
    (H : Finset ℕ) (m : ℕ) :
    Finset ((Fin (Fintype.card (Option (H × Fin 3))) → ℕ) × H) :=
  (Nat.finMulAntidiag (Fintype.card (Option (H × Fin 3))) m).product
    Finset.univ

theorem compatiblePairShiftFinFactorEncoding_injective
    (H : Finset ℕ) (W : ℕ) :
    Function.Injective (compatiblePairShiftFinFactorEncoding H W) := by
  intro i j hij
  have hpairs : i.1 = j.1 :=
    divisorPairFinFactorEncoding_injective H W (congrArg Prod.fst hij)
  have hshift := congrArg
    (fun z : (Fin (Fintype.card (Option (H × Fin 3))) → ℕ) × H => z.2) hij
  change i.2 = j.2 at hshift
  exact Prod.ext hpairs hshift

theorem compatiblePairShiftFinFactorEncoding_mem_container
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W m : ℕ} (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    {i : (((H → ℕ) × (H → ℕ)) × H)}
    (hi : i ∈ (compatiblePairShiftIndex H D).filter
      (fun j => compatiblePairShiftModulus H W j = m)) :
    compatiblePairShiftFinFactorEncoding H W i ∈
      compatiblePairShiftFinFactorContainer H m := by
  classical
  obtain ⟨hiIndex, hiMod⟩ := Finset.mem_filter.mp hi
  have hiData := compatiblePairShiftIndex_data hiIndex
  have hd := hD i.1.1 hiData.1
  have he := hD i.1.2 hiData.2.1
  have hmod : divisorPairModulus H W i.1.1 i.1.2 = m := by
    simpa [compatiblePairShiftModulus] using hiMod
  have hm : m ≠ 0 := by
    rw [← hmod]
    exact (divisorPairModulus_pos hW hd he).ne'
  apply Finset.mem_product.mpr
  refine ⟨Nat.mem_finMulAntidiag.mpr ⟨?_, hm⟩, Finset.mem_univ _⟩
  change (∏ a, divisorPairFinFactorEncoding H W i.1.1 i.1.2 a) = m
  rw [divisorPairFinFactorEncoding_prod]
  exact hmod

theorem compatiblePairShiftFinFactorContainer_card
    (H : Finset ℕ) (m : ℕ) :
    (compatiblePairShiftFinFactorContainer H m).card =
      (Nat.finMulAntidiag (Fintype.card (Option (H × Fin 3))) m).card *
        Fintype.card H := by
  classical
  simp [compatiblePairShiftFinFactorContainer, Finset.card_product,
    Fintype.card_coe]

theorem modulusFiberCard_le_finMulAntidiag_mul_card
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W m : ℕ} (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    modulusFiberCard (compatiblePairShiftIndex H D)
        (compatiblePairShiftModulus H W) m ≤
      (Nat.finMulAntidiag (Fintype.card (Option (H × Fin 3))) m).card *
        Fintype.card H := by
  unfold modulusFiberCard
  calc
    ((compatiblePairShiftIndex H D).filter
        (fun i => compatiblePairShiftModulus H W i = m)).card ≤
        (compatiblePairShiftFinFactorContainer H m).card := by
      apply Finset.card_le_card_of_injOn
        (compatiblePairShiftFinFactorEncoding H W)
      · intro i hi
        exact compatiblePairShiftFinFactorEncoding_mem_container hW hD hi
      · exact (compatiblePairShiftFinFactorEncoding_injective H W).injOn
    _ = (Nat.finMulAntidiag (Fintype.card (Option (H × Fin 3))) m).card *
        Fintype.card H := compatiblePairShiftFinFactorContainer_card H m

theorem card_orderedFactorIndex (H : Finset ℕ) :
    Fintype.card (Option (H × Fin 3)) = 3 * Fintype.card H + 1 := by
  classical
  simp [Fintype.card_option, Fintype.card_prod, Fintype.card_coe]
  omega

theorem modulusFiberCard_le_orderedFactorPow
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W m : ℕ} (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hm : Squarefree m) :
    modulusFiberCard (compatiblePairShiftIndex H D)
        (compatiblePairShiftModulus H W) m ≤
      (3 * Fintype.card H + 1) ^ ω m * Fintype.card H := by
  calc
    modulusFiberCard (compatiblePairShiftIndex H D)
        (compatiblePairShiftModulus H W) m ≤
      (Nat.finMulAntidiag (Fintype.card (Option (H × Fin 3))) m).card *
        Fintype.card H := modulusFiberCard_le_finMulAntidiag_mul_card hW hD
    _ = (3 * Fintype.card H + 1) ^ ω m * Fintype.card H := by
      rw [Nat.card_finMulAntidiag_of_squarefree hm, card_orderedFactorIndex]

theorem sum_maxProgressionDiscrepancy_comp_le_orderedFactorPow
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W : ℕ}
    (hW : Squarefree W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) (x : ℕ) :
    (∑ i ∈ compatiblePairShiftIndex H D,
        maxProgressionDiscrepancy x (compatiblePairShiftModulus H W i)) ≤
      ∑ m ∈ (compatiblePairShiftIndex H D).image
          (compatiblePairShiftModulus H W),
        (((3 * Fintype.card H + 1) ^ ω m * Fintype.card H : ℕ) : ℝ) *
          maxProgressionDiscrepancy x m := by
  rw [sum_comp_eq_sum_modulusFiberCard]
  apply Finset.sum_le_sum
  intro m hm
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast modulusFiberCard_le_orderedFactorPow
      (Nat.pos_of_ne_zero hW.ne_zero) hD
      (squarefree_of_mem_compatiblePairShiftModulus_image hW hD hm)
  · exact maxProgressionDiscrepancy_nonneg x m

end BoundedGaps.Maynard
