import PrimesRestrictedDigits.SieveDecomposition.Definitions

/-!
# Strict-rough and weak-smooth factorization

This isolates the unique factorization used when Maynard puts `q = d * e` in the proof of
Lemma 7.4.

Source: `MAYNARD-PRD-PUBLISHED`, proof of Lemma 7.4, pp. 153--154.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Every prime divisor of `n` is weakly at most `z`. -/
def weakSmoothPredicate (z : Real) (n : Nat) : Prop :=
  ∀ p, p.Prime → p ∣ n → (p : Real) ≤ z

@[simp] theorem weakSmoothPredicate_one (z : Real) :
    weakSmoothPredicate z 1 := by
  intro p hp hpd
  exact (hp.not_dvd_one hpd).elim

theorem strictRoughPredicate_antitone_threshold
    {z1 z2 : Real} (hz : z1 ≤ z2) {n : Nat}
    (hn : strictRoughPredicate z2 n) : strictRoughPredicate z1 n := by
  intro p hp hpn
  exact hz.trans_lt (hn p hp hpn)

theorem weakSmoothPredicate_mono_threshold
    {z1 z2 : Real} (hz : z1 ≤ z2) {n : Nat}
    (hn : weakSmoothPredicate z1 n) : weakSmoothPredicate z2 n := by
  intro p hp hpn
  exact (hn p hp hpn).trans hz

/-- A strict-rough integer at threshold five is coprime to the decimal base. -/
theorem strictRoughPredicate_coprime_ten
    {z : Real} (hz : 5 ≤ z) {n : Nat}
    (hn : strictRoughPredicate z n) : n.Coprime 10 := by
  rw [show 10 = 2 * 5 by norm_num, Nat.coprime_mul_iff_right]
  constructor
  · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro htwo
    have hbound := hn 2 Nat.prime_two htwo
    norm_num at hbound
    linarith
  · have hpFive : Nat.Prime 5 := by decide
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpFive]
    intro hfive
    exact (not_lt_of_ge hz) (hn 5 hpFive hfive)

/-- Strict-rough and weak-smooth factors at the same threshold are coprime. -/
theorem rough_smooth_coprime
    {z : Real} {d e : Nat}
    (hd : strictRoughPredicate z d)
    (he : weakSmoothPredicate z e) : d.Coprime e := by
  by_contra hcoprime
  rcases Nat.Prime.not_coprime_iff_dvd.mp hcoprime with
    ⟨p, hp, hpd, hpe⟩
  exact (not_lt_of_ge (he p hp hpe)) (hd p hp hpd)

/-- A product has at most one positive strict-rough/weak-smooth
factorization at a fixed threshold. -/
theorem rough_smooth_mul_injective
    {z : Real} {d1 e1 d2 e2 : Nat}
    (hd1Pos : 0 < d1) (hd2Pos : 0 < d2)
    (hd1 : strictRoughPredicate z d1)
    (hd2 : strictRoughPredicate z d2)
    (he1 : weakSmoothPredicate z e1)
    (he2 : weakSmoothPredicate z e2)
    (hproduct : d1 * e1 = d2 * e2) : d1 = d2 ∧ e1 = e2 := by
  have hd1e2 : d1.Coprime e2 := rough_smooth_coprime hd1 he2
  have hd2e1 : d2.Coprime e1 := rough_smooth_coprime hd2 he1
  have hd1Dvd : d1 ∣ d2 := by
    apply hd1e2.dvd_of_dvd_mul_right
    exact ⟨e1, hproduct.symm⟩
  have hd2Dvd : d2 ∣ d1 := by
    apply hd2e1.dvd_of_dvd_mul_right
    exact ⟨e2, hproduct⟩
  have hd : d1 = d2 := Nat.dvd_antisymm hd1Dvd hd2Dvd
  subst d2
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hd1Pos hproduct⟩

/-- Inject the nonnegative mass of a finite rough/smooth product family into
any finite carrier containing all its products. -/
theorem sum_rough_smooth_products_le
    {D E Q : Finset Nat} {z : Real} {f : Nat → Real}
    (hDPos : ∀ d, d ∈ D → 0 < d)
    (hDrough : ∀ d, d ∈ D → strictRoughPredicate z d)
    (hEsmooth : ∀ e, e ∈ E → weakSmoothPredicate z e)
    (himage : ∀ d, d ∈ D → ∀ e, e ∈ E → d * e ∈ Q)
    (hf : ∀ q, q ∈ Q → 0 ≤ f q) :
    (∑ d ∈ D, ∑ e ∈ E, f (d * e)) ≤ ∑ q ∈ Q, f q := by
  classical
  let pairs := D.product E
  let multiply : Nat × Nat → Nat := fun pair => pair.1 * pair.2
  have hinjective : (pairs : Set (Nat × Nat)).InjOn multiply := by
    rintro ⟨d1, e1⟩ hp1 ⟨d2, e2⟩ hp2 hproduct
    have hp1Data := Finset.mem_product.mp hp1
    have hp2Data := Finset.mem_product.mp hp2
    have heq := rough_smooth_mul_injective
      (hDPos d1 hp1Data.1) (hDPos d2 hp2Data.1)
      (hDrough d1 hp1Data.1) (hDrough d2 hp2Data.1)
      (hEsmooth e1 hp1Data.2) (hEsmooth e2 hp2Data.2) hproduct
    exact Prod.ext heq.1 heq.2
  have hsubset : pairs.image multiply ⊆ Q := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨⟨d, e⟩, hp, rfl⟩
    have hpData := Finset.mem_product.mp hp
    exact himage d hpData.1 e hpData.2
  rw [← Finset.sum_product']
  change (∑ pair ∈ pairs, f (multiply pair)) ≤ _
  calc
    (∑ pair ∈ pairs, f (multiply pair)) =
        ∑ q ∈ pairs.image multiply, f q :=
      (Finset.sum_image hinjective).symm
    _ ≤ ∑ q ∈ Q, f q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro q hqQ _
      exact hf q hqQ

end PrimesRestrictedDigits
