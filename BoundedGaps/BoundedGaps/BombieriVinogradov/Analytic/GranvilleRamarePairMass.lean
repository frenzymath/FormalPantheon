import BoundedGaps.BombieriVinogradov.Analytic.GranvilleRamareMoments
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# The nonnegative pair mass in the Granville--Ramare estimate

This file proves the error-mass estimate in Granville--Ramare1996,
Proposition 10.1, printed p. 43.  The statement and its role in the final
`4 / 3` constant are reviewed under `SEM-457`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

private def squarefreeLcmPairs (Z B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc 0 Z ×ˢ Finset.Ioc 0 Z).filter
    (fun p => Nat.lcm p.1 p.2 ≤ B ∧ Squarefree p.1 ∧ Squarefree p.2)

private abbrev GcdDecompositionTriple := Σ _a : ℕ, Σ _b : ℕ, ℕ

/-- The enlarged support after writing `d = g * a` and `e = g * b`.
Only squarefreeness of `a` and `b` is retained; dropping the remaining
coprimality and product-cutoff conditions gives the required upper bound. -/
private def gcdDecompositionTriples (Z B : ℕ) :
    Finset GcdDecompositionTriple :=
  ((Finset.Ioc 0 Z).filter Squarefree).sigma (fun a =>
    ((Finset.Ioc 0 Z).filter Squarefree).sigma (fun b =>
      Finset.Ioc 0 (B / (a * b))))

private def decomposeLcmPair (p : ℕ × ℕ) : GcdDecompositionTriple :=
  ⟨p.1 / Nat.gcd p.1 p.2,
    ⟨p.2 / Nat.gcd p.1 p.2, Nat.gcd p.1 p.2⟩⟩

private theorem pairMass_eq_card_squarefreeLcmPairs (Z B : ℕ) :
    (∑ d ∈ Finset.Ioc 0 Z,
      ∑ e ∈ (Finset.Ioc 0 Z).filter (fun e => Nat.lcm d e ≤ B),
        (((ArithmeticFunction.moebius d : ℤ) : ℝ)) ^ 2 *
          (((ArithmeticFunction.moebius e : ℤ) : ℝ)) ^ 2) =
      ((squarefreeLcmPairs Z B).card : ℝ) := by
  unfold squarefreeLcmPairs
  rw [Finset.natCast_card_filter, Finset.sum_product]
  simp_rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hlcm : Nat.lcm d e ≤ B <;>
    by_cases hdSq : Squarefree d <;>
      by_cases heSq : Squarefree e <;> simp [hlcm, hdSq, heSq]

private theorem lcm_eq_gcd_mul_div_mul_div
    {d e : ℕ} (hd : 0 < d) :
    Nat.lcm d e = Nat.gcd d e *
      ((d / Nat.gcd d e) * (e / Nat.gcd d e)) := by
  have hgPos : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left e hd
  have hcop : Nat.Coprime (d / Nat.gcd d e) (e / Nat.gcd d e) :=
    Nat.coprime_div_gcd_div_gcd hgPos
  calc
    Nat.lcm d e = Nat.lcm
        (Nat.gcd d e * (d / Nat.gcd d e))
        (Nat.gcd d e * (e / Nat.gcd d e)) := by
          rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left d e),
            Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)]
    _ = Nat.gcd d e *
        Nat.lcm (d / Nat.gcd d e) (e / Nat.gcd d e) := by
          rw [Nat.lcm_mul_left]
    _ = _ := by rw [hcop.lcm_eq_mul]

private theorem card_squarefreeLcmPairs_le_gcdDecompositionTriples
    (Z B : ℕ) :
    (squarefreeLcmPairs Z B).card ≤
      (gcdDecompositionTriples Z B).card := by
  apply Finset.card_le_card_of_injOn decomposeLcmPair
  · intro p hp
    rcases Finset.mem_filter.mp hp with
      ⟨hpProd, hlcm, hdSq, heSq⟩
    rcases Finset.mem_product.mp hpProd with ⟨hdZ, heZ⟩
    have hdPos : 0 < p.1 := (Finset.mem_Ioc.mp hdZ).1
    have hePos : 0 < p.2 := (Finset.mem_Ioc.mp heZ).1
    have hgPos : 0 < Nat.gcd p.1 p.2 :=
      Nat.gcd_pos_of_pos_left p.2 hdPos
    have haPos : 0 < p.1 / Nat.gcd p.1 p.2 :=
      Nat.div_pos
        (Nat.le_of_dvd hdPos (Nat.gcd_dvd_left p.1 p.2)) hgPos
    have hbPos : 0 < p.2 / Nat.gcd p.1 p.2 :=
      Nat.div_pos
        (Nat.le_of_dvd hePos (Nat.gcd_dvd_right p.1 p.2)) hgPos
    have haSq : Squarefree (p.1 / Nat.gcd p.1 p.2) :=
      hdSq.squarefree_of_dvd
        (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left p.1 p.2))
    have hbSq : Squarefree (p.2 / Nat.gcd p.1 p.2) :=
      heSq.squarefree_of_dvd
        (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right p.1 p.2))
    have hlcmEq := lcm_eq_gcd_mul_div_mul_div (e := p.2) hdPos
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨haPos, ?_⟩, haSq⟩, ?_⟩
    · exact (Nat.div_le_self p.1 _).trans (Finset.mem_Ioc.mp hdZ).2
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hbPos, ?_⟩, hbSq⟩, ?_⟩
    · exact (Nat.div_le_self p.2 _).trans (Finset.mem_Ioc.mp heZ).2
    change Nat.gcd p.1 p.2 ∈ Finset.Ioc 0
      (B / ((p.1 / Nat.gcd p.1 p.2) *
        (p.2 / Nat.gcd p.1 p.2)))
    apply Finset.mem_Ioc.mpr
    refine ⟨hgPos, (Nat.le_div_iff_mul_le (Nat.mul_pos haPos hbPos)).2 ?_⟩
    simpa only [← hlcmEq] using hlcm
  · intro p _hp q _hq hpq
    apply Prod.ext
    · have hfirst := congrArg
        (fun x : GcdDecompositionTriple => x.1 * x.2.2) hpq
      calc
        p.1 = (p.1 / Nat.gcd p.1 p.2) * Nat.gcd p.1 p.2 :=
          (Nat.div_mul_cancel (Nat.gcd_dvd_left p.1 p.2)).symm
        _ = (q.1 / Nat.gcd q.1 q.2) * Nat.gcd q.1 q.2 := by
          simpa only [decomposeLcmPair] using hfirst
        _ = q.1 := Nat.div_mul_cancel (Nat.gcd_dvd_left q.1 q.2)
    · have hsecond := congrArg
        (fun x : GcdDecompositionTriple => x.2.1 * x.2.2) hpq
      calc
        p.2 = (p.2 / Nat.gcd p.1 p.2) * Nat.gcd p.1 p.2 :=
          (Nat.div_mul_cancel (Nat.gcd_dvd_right p.1 p.2)).symm
        _ = (q.2 / Nat.gcd q.1 q.2) * Nat.gcd q.1 q.2 := by
          simpa only [decomposeLcmPair] using hsecond
        _ = q.2 := Nat.div_mul_cancel (Nat.gcd_dvd_right q.1 q.2)

private theorem card_gcdDecompositionTriples (Z B : ℕ) :
    ((gcdDecompositionTriples Z B).card : ℝ) =
      ∑ a ∈ (Finset.Ioc 0 Z).filter Squarefree,
        ∑ b ∈ (Finset.Ioc 0 Z).filter Squarefree,
          ((B / (a * b) : ℕ) : ℝ) := by
  simp [gcdDecompositionTriples, Finset.card_sigma, Nat.card_Ioc]

private theorem sum_inv_squarefree_eq_moebiusSquareMoment (Z : ℕ) :
    (∑ a ∈ (Finset.Ioc 0 Z).filter Squarefree, (a : ℝ)⁻¹) =
      ∑ a ∈ Finset.Ioc 0 Z,
        (((ArithmeticFunction.moebius a : ℤ) : ℝ)) ^ 2 / (a : ℝ) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]
  by_cases haSq : Squarefree a <;> simp [haSq]

private theorem sum_cast_div_le_squarefreeMoment_sq (Z B : ℕ) :
    (∑ a ∈ (Finset.Ioc 0 Z).filter Squarefree,
      ∑ b ∈ (Finset.Ioc 0 Z).filter Squarefree,
        ((B / (a * b) : ℕ) : ℝ)) ≤
      (B : ℝ) *
        (∑ a ∈ (Finset.Ioc 0 Z).filter Squarefree, (a : ℝ)⁻¹) ^ 2 := by
  calc
    _ ≤ ∑ a ∈ (Finset.Ioc 0 Z).filter Squarefree,
        ∑ b ∈ (Finset.Ioc 0 Z).filter Squarefree,
          (B : ℝ) / ((a * b : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro a _ha
      apply Finset.sum_le_sum
      intro b _hb
      exact Nat.cast_div_le
    _ = _ := by
      rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have ha0 : (a : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1).1.ne'
      have hb0 : (b : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1).1.ne'
      push_cast
      field_simp

/-- The nonnegative lcm-filtered pair mass in the proof of
Granville--Ramare1996, Proposition 10.1. -/
theorem sum_sq_moebius_pair_lcm_le
    {Z B : ℕ} (hZ : 1 ≤ Z) :
    (∑ d ∈ Finset.Ioc 0 Z,
      ∑ e ∈ (Finset.Ioc 0 Z).filter
        (fun e => Nat.lcm d e ≤ B),
        (((ArithmeticFunction.moebius d : ℤ) : ℝ)) ^ 2 *
          (((ArithmeticFunction.moebius e : ℤ) : ℝ)) ^ 2) ≤
      (B : ℝ) *
        ((2 / 3 : ℝ) * (Real.log (Z : ℝ) + 3)) ^ 2 := by
  rw [pairMass_eq_card_squarefreeLcmPairs]
  have hcardNat := card_squarefreeLcmPairs_le_gcdDecompositionTriples Z B
  have hcardReal :
      ((squarefreeLcmPairs Z B).card : ℝ) ≤
        ((gcdDecompositionTriples Z B).card : ℝ) := by
    exact_mod_cast hcardNat
  have hmoment := sum_sq_moebius_div_le_two_thirds hZ
  have hmoment' :
      (∑ a ∈ (Finset.Ioc 0 Z).filter Squarefree, (a : ℝ)⁻¹) ≤
        (2 / 3 : ℝ) * (Real.log (Z : ℝ) + 3) := by
    rw [sum_inv_squarefree_eq_moebiusSquareMoment]
    exact hmoment
  have hsumNonneg :
      0 ≤ ∑ a ∈ (Finset.Ioc 0 Z).filter Squarefree, (a : ℝ)⁻¹ := by
    exact Finset.sum_nonneg fun a _ha => inv_nonneg.mpr (Nat.cast_nonneg a)
  have hrightNonneg :
      0 ≤ (2 / 3 : ℝ) * (Real.log (Z : ℝ) + 3) := by
    have hlog : 0 ≤ Real.log (Z : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hZ)
    positivity
  calc
    ((squarefreeLcmPairs Z B).card : ℝ) ≤
        ((gcdDecompositionTriples Z B).card : ℝ) := hcardReal
    _ = ∑ a ∈ (Finset.Ioc 0 Z).filter Squarefree,
        ∑ b ∈ (Finset.Ioc 0 Z).filter Squarefree,
          ((B / (a * b) : ℕ) : ℝ) := card_gcdDecompositionTriples Z B
    _ ≤ (B : ℝ) *
        (∑ a ∈ (Finset.Ioc 0 Z).filter Squarefree, (a : ℝ)⁻¹) ^ 2 :=
      sum_cast_div_le_squarefreeMoment_sq Z B
    _ ≤ (B : ℝ) *
        ((2 / 3 : ℝ) * (Real.log (Z : ℝ) + 3)) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · exact (sq_le_sq₀ hsumNonneg hrightNonneg).2 hmoment'
      · positivity

end BoundedGaps.Maynard
