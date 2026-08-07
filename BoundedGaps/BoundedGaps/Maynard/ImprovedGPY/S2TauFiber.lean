import BoundedGaps.Maynard.ImprovedGPY.S2OrderedFactorFiber

noncomputable section

/-!
# Source-shaped tau bounds for S2 modulus fibers

Maynard2013v3, in the error part of `lmm:S2Expression1` (source lines
363--367), bounds the divisor-pair multiplicity at a squarefree modulus `m`
by `tau_{3k}(m)`.  This file removes the fixed `W` coordinate from the ordered
factor encoding and obtains the corresponding `(3k)^(omega m)` bound.  The
project's combined pair/shift index retains one explicit factor `k`.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.omega BigOperators
local instance tauFiberDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def divisorPairCoordinateFactorEncoding
    (H : Finset ℕ) (d e : H → ℕ) : H × Fin 3 → ℕ :=
  fun i => divisorPairFactorEncoding H 1 d e (some i)

def divisorPairFinCoordinateFactorEncoding
    (H : Finset ℕ) (d e : H → ℕ) :
    Fin (Fintype.card (H × Fin 3)) → ℕ :=
  fun i => divisorPairCoordinateFactorEncoding H d e
    ((Fintype.equivFin (H × Fin 3)).symm i)

theorem divisorPairCoordinateFactorEncoding_prod
    (H : Finset ℕ) (d e : H → ℕ) :
    (∏ i, divisorPairCoordinateFactorEncoding H d e i) =
      ∏ h : H, divisorTupleLcm H d e h := by
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro h hh
  rw [Fin.prod_univ_three]
  simp only [divisorPairCoordinateFactorEncoding,
    divisorPairFactorEncoding, ↓reduceIte, OfNat.ofNat]
  exact gcd_mul_div_mul_div_eq_lcm (d h) (e h)

theorem divisorPairFinCoordinateFactorEncoding_prod
    (H : Finset ℕ) (d e : H → ℕ) :
    (∏ i, divisorPairFinCoordinateFactorEncoding H d e i) =
      ∏ h : H, divisorTupleLcm H d e h := by
  calc
    (∏ i, divisorPairFinCoordinateFactorEncoding H d e i) =
        ∏ i : H × Fin 3, divisorPairCoordinateFactorEncoding H d e i := by
      apply Fintype.prod_equiv (Fintype.equivFin (H × Fin 3)).symm
      intro i
      rfl
    _ = ∏ h : H, divisorTupleLcm H d e h :=
      divisorPairCoordinateFactorEncoding_prod H d e

theorem divisorPairCoordinateFactorEncoding_injective (H : Finset ℕ) :
    Function.Injective (fun de : (H → ℕ) × (H → ℕ) =>
      divisorPairCoordinateFactorEncoding H de.1 de.2) := by
  intro de de' henc
  apply divisorPairFactorEncoding_injective H 1
  funext i
  cases i with
  | none => rfl
  | some i => exact congrFun henc i

theorem divisorPairFinCoordinateFactorEncoding_injective (H : Finset ℕ) :
    Function.Injective (fun de : (H → ℕ) × (H → ℕ) =>
      divisorPairFinCoordinateFactorEncoding H de.1 de.2) := by
  intro de de' henc
  apply divisorPairCoordinateFactorEncoding_injective H
  funext i
  have hi := congrFun henc ((Fintype.equivFin (H × Fin 3)) i)
  simpa [divisorPairFinCoordinateFactorEncoding] using hi

def compatiblePairShiftTauEncoding
    (H : Finset ℕ) (i : (((H → ℕ) × (H → ℕ)) × H)) :
    (Fin (Fintype.card (H × Fin 3)) → ℕ) × H :=
  (divisorPairFinCoordinateFactorEncoding H i.1.1 i.1.2, i.2)

def compatiblePairShiftTauContainer
    (H : Finset ℕ) (W m : ℕ) :
    Finset ((Fin (Fintype.card (H × Fin 3)) → ℕ) × H) :=
  (Nat.finMulAntidiag (Fintype.card (H × Fin 3)) (m / W)).product
    Finset.univ

theorem compatiblePairShiftTauEncoding_injective (H : Finset ℕ) :
    Function.Injective (compatiblePairShiftTauEncoding H) := by
  intro i j hij
  have hpairs : i.1 = j.1 :=
    divisorPairFinCoordinateFactorEncoding_injective H (congrArg Prod.fst hij)
  have hshift := congrArg
    (fun z : (Fin (Fintype.card (H × Fin 3)) → ℕ) × H => z.2) hij
  change i.2 = j.2 at hshift
  exact Prod.ext hpairs hshift

theorem compatiblePairShiftTauEncoding_mem_container
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W m : ℕ} (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    {i : (((H → ℕ) × (H → ℕ)) × H)}
    (hi : i ∈ (compatiblePairShiftIndex H D).filter
      (fun j => compatiblePairShiftModulus H W j = m)) :
    compatiblePairShiftTauEncoding H i ∈
      compatiblePairShiftTauContainer H W m := by
  classical
  obtain ⟨hiIndex, hiMod⟩ := Finset.mem_filter.mp hi
  have hiData := compatiblePairShiftIndex_data hiIndex
  have hd := hD i.1.1 hiData.1
  have he := hD i.1.2 hiData.2.1
  have hmod : divisorPairModulus H W i.1.1 i.1.2 = m := by
    simpa [compatiblePairShiftModulus] using hiMod
  have hquot : m / W = ∏ h : H, divisorTupleLcm H i.1.1 i.1.2 h := by
    rw [← hmod]
    unfold divisorPairModulus
    exact Nat.mul_div_cancel_left _ hW
  have hquot_ne : m / W ≠ 0 := by
    rw [hquot]
    apply Finset.prod_ne_zero_iff.mpr
    intro h hh
    exact (divisorTupleLcm_pos_of_isMaynard hd he h).ne'
  apply Finset.mem_product.mpr
  refine ⟨Nat.mem_finMulAntidiag.mpr ⟨?_, hquot_ne⟩, Finset.mem_univ _⟩
  change (∏ a, divisorPairFinCoordinateFactorEncoding H i.1.1 i.1.2 a) =
    m / W
  rw [divisorPairFinCoordinateFactorEncoding_prod]
  exact hquot.symm

theorem compatiblePairShiftTauContainer_card
    (H : Finset ℕ) (W m : ℕ) :
    (compatiblePairShiftTauContainer H W m).card =
      (Nat.finMulAntidiag (Fintype.card (H × Fin 3)) (m / W)).card *
        Fintype.card H := by
  classical
  simp [compatiblePairShiftTauContainer, Finset.card_product,
    Fintype.card_coe]

theorem modulusFiberCard_le_finMulAntidiag_div_mul_card
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W m : ℕ} (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    modulusFiberCard (compatiblePairShiftIndex H D)
        (compatiblePairShiftModulus H W) m ≤
      (Nat.finMulAntidiag (Fintype.card (H × Fin 3)) (m / W)).card *
        Fintype.card H := by
  unfold modulusFiberCard
  calc
    ((compatiblePairShiftIndex H D).filter
        (fun i => compatiblePairShiftModulus H W i = m)).card ≤
        (compatiblePairShiftTauContainer H W m).card := by
      apply Finset.card_le_card_of_injOn (compatiblePairShiftTauEncoding H)
      · intro i hi
        exact compatiblePairShiftTauEncoding_mem_container hW hD hi
      · exact (compatiblePairShiftTauEncoding_injective H).injOn
    _ = (Nat.finMulAntidiag (Fintype.card (H × Fin 3)) (m / W)).card *
        Fintype.card H := compatiblePairShiftTauContainer_card H W m

theorem card_tauFactorIndex (H : Finset ℕ) :
    Fintype.card (H × Fin 3) = 3 * Fintype.card H := by
  classical
  simp [Fintype.card_prod, Fintype.card_coe]
  omega

theorem omega_eq_card_primeFactors (n : ℕ) :
    ω n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
    Nat.toFinset_factors]

theorem omega_le_of_dvd {a b : ℕ} (hab : a ∣ b) (hb : b ≠ 0) :
    ω a ≤ ω b := by
  rw [omega_eq_card_primeFactors, omega_eq_card_primeFactors]
  exact Finset.card_le_card (Nat.primeFactors_mono hab hb)

theorem modulusFiberCard_le_tauPow
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W m : ℕ}
    (hH : H.Nonempty) (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hm : Squarefree m) (hWm : W ∣ m) :
    modulusFiberCard (compatiblePairShiftIndex H D)
        (compatiblePairShiftModulus H W) m ≤
      (3 * Fintype.card H) ^ ω m * Fintype.card H := by
  have hquotSq : Squarefree (m / W) :=
    hm.squarefree_of_dvd (Nat.div_dvd_of_dvd hWm)
  have homega : ω (m / W) ≤ ω m :=
    omega_le_of_dvd (Nat.div_dvd_of_dvd hWm) hm.ne_zero
  calc
    modulusFiberCard (compatiblePairShiftIndex H D)
        (compatiblePairShiftModulus H W) m ≤
      (Nat.finMulAntidiag (Fintype.card (H × Fin 3)) (m / W)).card *
        Fintype.card H := modulusFiberCard_le_finMulAntidiag_div_mul_card hW hD
    _ = (3 * Fintype.card H) ^ ω (m / W) * Fintype.card H := by
      rw [Nat.card_finMulAntidiag_of_squarefree hquotSq, card_tauFactorIndex]
    _ ≤ (3 * Fintype.card H) ^ ω m * Fintype.card H := by
      apply Nat.mul_le_mul_right
      apply Nat.pow_le_pow_right
      · haveI : Nonempty H := hH.to_subtype
        have hcard : 0 < Fintype.card H := Fintype.card_pos
        omega
      · exact homega

theorem W_dvd_of_mem_compatiblePairShiftModulus_image
    {H : Finset ℕ} {D : Finset (H → ℕ)} {W m : ℕ}
    (hm : m ∈ (compatiblePairShiftIndex H D).image
      (compatiblePairShiftModulus H W)) :
    W ∣ m := by
  classical
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
  unfold compatiblePairShiftModulus divisorPairModulus
  exact dvd_mul_right W _

theorem sum_maxProgressionDiscrepancy_comp_le_tauPow
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W : ℕ}
    (hH : H.Nonempty) (hW : Squarefree W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) (x : ℕ) :
    (∑ i ∈ compatiblePairShiftIndex H D,
        maxProgressionDiscrepancy x (compatiblePairShiftModulus H W i)) ≤
      ∑ m ∈ (compatiblePairShiftIndex H D).image
          (compatiblePairShiftModulus H W),
        (((3 * Fintype.card H) ^ ω m * Fintype.card H : ℕ) : ℝ) *
          maxProgressionDiscrepancy x m := by
  rw [sum_comp_eq_sum_modulusFiberCard]
  apply Finset.sum_le_sum
  intro m hm
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast modulusFiberCard_le_tauPow hH
      (Nat.pos_of_ne_zero hW.ne_zero) hD
      (squarefree_of_mem_compatiblePairShiftModulus_image hW hD hm)
      (W_dvd_of_mem_compatiblePairShiftModulus_image hm)
  · exact maxProgressionDiscrepancy_nonneg x m

end BoundedGaps.Maynard
