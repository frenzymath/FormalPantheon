import BoundedGaps.Maynard.MaynardPrimeDivisorMean

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

/-! Coordinatewise boxes for a fixed shared-prime collision. -/

def coordinatePrimeCollisionBox
    (H : Finset ℕ) (W R : ℕ) (a b : H) (p : ℕ) :
    Finset (H → ℕ) :=
  Fintype.piFinset (fun h =>
    if h = a ∨ h = b then
      squarefreeCoprimePrimeDivisorSupport W R p
    else preSievedCommonCoordinateSupport W R)

def reciprocalTotientTupleWeight
    (H : Finset ℕ) (u : H → ℕ) : ℝ :=
  ∏ h : H, (1 : ℝ) / Nat.totient (u h)

theorem reciprocalTotientTupleWeight_sum_pi_eq_prod
    {H : Finset ℕ} (S : H → Finset ℕ) :
    (∑ u ∈ Fintype.piFinset S,
      reciprocalTotientTupleWeight H u) =
      ∏ h : H, ∑ n ∈ S h, (1 : ℝ) / Nat.totient n := by
  unfold reciprocalTotientTupleWeight
  exact (Finset.prod_univ_sum S
    (fun h : H => fun n => (1 : ℝ) / Nat.totient n)).symm

theorem mem_coordinatePrimeCollisionBox_of_independent
    {H : Finset ℕ} {R W : ℕ} {u : H → ℕ}
    {a b : H} {p : ℕ}
    (hu : u ∈ preSievedSimplexTupleSupport H R W)
    (hpa : p ∣ u a) (hpb : p ∣ u b) :
    u ∈ coordinatePrimeCollisionBox H W R a b p := by
  rw [coordinatePrimeCollisionBox, Fintype.mem_piFinset]
  intro h
  by_cases hha : h = a
  · subst h
    simp only [eq_self, true_or, ↓reduceIte]
    have hdata := preSievedSimplexTupleSupport_coordinate hu a
    have hprodPos : 0 < divisorTupleProduct H u := by
      unfold divisorTupleProduct
      apply Finset.prod_pos
      intro i hi
      exact (preSievedSimplexTupleSupport_coordinate hu i).1
    have hcoordLe : u a ≤ divisorTupleProduct H u :=
      Nat.le_of_dvd hprodPos (divisorTupleCoordinate_dvd_product u a)
    have hcoordLt : u a < R := lt_of_le_of_lt hcoordLe
      (mem_preSievedSimplexTupleSupport_iff.mp hu).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hdata.1, hcoordLt.le⟩,
      ⟨hdata.2.1, hdata.2.2, hpa⟩⟩
  by_cases hhb : h = b
  · subst h
    simp only [eq_self, or_true, ↓reduceIte]
    have hdata := preSievedSimplexTupleSupport_coordinate hu b
    have hprodPos : 0 < divisorTupleProduct H u := by
      unfold divisorTupleProduct
      apply Finset.prod_pos
      intro i hi
      exact (preSievedSimplexTupleSupport_coordinate hu i).1
    have hcoordLe : u b ≤ divisorTupleProduct H u :=
      Nat.le_of_dvd hprodPos (divisorTupleCoordinate_dvd_product u b)
    have hcoordLt : u b < R := lt_of_le_of_lt hcoordLe
      (mem_preSievedSimplexTupleSupport_iff.mp hu).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hdata.1, hcoordLt.le⟩,
      ⟨hdata.2.1, hdata.2.2, hpb⟩⟩
  · simp only [hha, hhb, or_false, ↓reduceIte]
    have huCommon := (mem_preSievedSimplexTupleSupport_iff.mp hu).1
    have huh := Fintype.mem_piFinset.mp huCommon h
    exact huh

theorem reciprocalTotientTupleWeight_sum_primeCollision_le_box
    {H : Finset ℕ} {R W : ℕ} {a b : H} {p : ℕ} :
    (∑ u ∈ (preSievedSimplexTupleSupport H R W).filter
        (fun u => p ∣ u a ∧ p ∣ u b),
      reciprocalTotientTupleWeight H u) ≤
      ∏ h : H, ∑ n ∈
        (if h = a ∨ h = b then
          squarefreeCoprimePrimeDivisorSupport W R p
        else preSievedCommonCoordinateSupport W R),
        (1 : ℝ) / Nat.totient n := by
  calc
    (∑ u ∈ (preSievedSimplexTupleSupport H R W).filter
        (fun u => p ∣ u a ∧ p ∣ u b),
      reciprocalTotientTupleWeight H u) ≤
        ∑ u ∈ coordinatePrimeCollisionBox H W R a b p,
          reciprocalTotientTupleWeight H u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro u hu
        have huData := Finset.mem_filter.mp hu
        exact mem_coordinatePrimeCollisionBox_of_independent huData.1
          huData.2.1 huData.2.2
      · intro u huBox huNot
        unfold reciprocalTotientTupleWeight
        positivity
    _ = ∏ h : H, ∑ n ∈
        (if h = a ∨ h = b then
          squarefreeCoprimePrimeDivisorSupport W R p
        else preSievedCommonCoordinateSupport W R),
        (1 : ℝ) / Nat.totient n := by
      exact reciprocalTotientTupleWeight_sum_pi_eq_prod _

theorem coordinatePrimeCollisionMass_eq
    {H : Finset ℕ} {a b : H} (hab : a ≠ b) {M P : ℝ} :
    (∏ h : H, if h = a ∨ h = b then P else M) =
      P ^ 2 * M ^ (Fintype.card H - 2) := by
  classical
  have hfilter :
      (Finset.univ : Finset H).filter (fun h => h = a ∨ h = b) = {a, b} := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
  have hnfilter :
      (Finset.univ : Finset H).filter (fun h => ¬(h = a ∨ h = b)) =
        (Finset.univ.erase a).erase b := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    simp only [not_or, ne_eq, and_true]
    exact and_comm
  rw [Finset.prod_ite, hfilter, hnfilter]
  simp only [Finset.prod_const, Fintype.card_coe]
  rw [Finset.card_pair hab]
  have hbErase : b ∈ (Finset.univ : Finset H).erase a := by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact hab.symm
  rw [Finset.card_erase_of_mem hbErase, Finset.card_erase_of_mem
    (Finset.mem_univ a)]
  have hcard : (Finset.univ : Finset H).card = H.card := by simp
  rw [hcard]
  have hexp : H.card - 1 - 1 = H.card - 2 := by omega
  rw [hexp]

end BoundedGaps.Maynard
