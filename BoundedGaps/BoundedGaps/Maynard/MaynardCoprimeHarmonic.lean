import BoundedGaps.Maynard.Distribution
import Mathlib.NumberTheory.Harmonic.Bounds

noncomputable section

/-!
# A finite coprime harmonic bound

Quotient/remainder blocks modulo `W` give an elementary upper bound with the
correct reduced-residue density.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def coprimeHarmonicSum (W Q : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ (Finset.Icc 1 Q).filter (Nat.Coprime · W), (1 : ℝ) / n

theorem card_coprimeResidues (W : ℕ) :
    (coprimeResidues W).card = Nat.totient W := by
  unfold coprimeResidues
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext x
  simp [Nat.coprime_comm]

private def coprimeBlockEncoding (W : ℕ) (n : ℕ) : ℕ × ℕ :=
  (n % W, n / W)

private def coprimeBlockWeight (W : ℕ) (x : ℕ × ℕ) : ℝ :=
  if x.2 = 0 then 1 else 1 / ((x.2 : ℝ) * W)

theorem coprimeBlockEncoding_injective
    {W : ℕ} :
    Function.Injective (coprimeBlockEncoding W) := by
  intro a b hab
  have hmod : a % W = b % W := congrArg Prod.fst hab
  have hdiv : a / W = b / W := congrArg Prod.snd hab
  calc
    a = a % W + W * (a / W) := (Nat.mod_add_div a W).symm
    _ = b % W + W * (b / W) := by rw [hmod, hdiv]
    _ = b := Nat.mod_add_div b W

theorem coprime_mod_mem_coprimeResidues
    {W n : ℕ} (hW : 0 < W) (hn : Nat.Coprime n W) :
    n % W ∈ coprimeResidues W := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (Nat.mod_lt n hW), ?_⟩
  rw [Nat.coprime_iff_gcd_eq_one] at hn ⊢
  calc
    (n % W).gcd W = W.gcd n := (Nat.gcd_rec W n).symm
    _ = n.gcd W := Nat.gcd_comm W n
    _ = 1 := hn

theorem coprimeBlockEncoding_mem_product
    {W Q n : ℕ} (hW : 0 < W)
    (hn : n ∈ (Finset.Icc 1 Q).filter (Nat.Coprime · W)) :
    coprimeBlockEncoding W n ∈
      coprimeResidues W ×ˢ Finset.range (Q + 1) := by
  have hnData := Finset.mem_filter.mp hn
  apply Finset.mem_product.mpr
  refine ⟨coprime_mod_mem_coprimeResidues hW hnData.2, ?_⟩
  apply Finset.mem_range.mpr
  have hdivLe : n / W ≤ n := Nat.div_le_self n W
  exact lt_of_le_of_lt (hdivLe.trans (Finset.mem_Icc.mp hnData.1).2) (Nat.lt_succ_self Q)

theorem one_div_le_coprimeBlockWeight
    {W Q n : ℕ} (hW : 0 < W)
    (hn : n ∈ (Finset.Icc 1 Q).filter (Nat.Coprime · W)) :
    (1 : ℝ) / n ≤ coprimeBlockWeight W (coprimeBlockEncoding W n) := by
  have hnPos : 0 < n := zero_lt_one.trans_le
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  by_cases hq : n / W = 0
  · simp only [coprimeBlockWeight, coprimeBlockEncoding, hq, if_true]
    exact (div_le_one (by exact_mod_cast hnPos)).mpr (by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hnPos.ne'))
  · simp only [coprimeBlockWeight, coprimeBlockEncoding, hq, if_false]
    have hqPos : 0 < n / W := Nat.pos_of_ne_zero hq
    have hprodPos : (0 : ℝ) < (n / W : ℕ) * W := by
      exact_mod_cast Nat.mul_pos hqPos hW
    have hprodLeNat : (n / W) * W ≤ n := Nat.div_mul_le_self n W
    have hprodLe : ((n / W : ℕ) * W : ℝ) ≤ n := by
      exact_mod_cast hprodLeNat
    simpa [coprimeBlockEncoding, mul_comm] using
      one_div_le_one_div_of_le hprodPos hprodLe

theorem sum_range_coprimeBlockWeight
    {W Q : ℕ} (hW : 0 < W) :
    (∑ q ∈ Finset.range (Q + 1),
        if q = 0 then (1 : ℝ) else 1 / ((q : ℝ) * W)) =
      1 + ((harmonic Q : ℚ) : ℝ) / W := by
  have hrange : Finset.range (Q + 1) =
      insert 0 (Finset.Icc 1 Q) := by
    ext q
    simp
    omega
  rw [hrange, Finset.sum_insert (by simp)]
  simp only [if_pos]
  have hterms :
      (∑ q ∈ Finset.Icc 1 Q,
          if q = 0 then (1 : ℝ) else 1 / ((q : ℝ) * W)) =
        ∑ q ∈ Finset.Icc 1 Q, ((1 : ℝ) / q) / W := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqOne : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hq0 : q ≠ 0 := by omega
    have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hqOne)
    have hWR : (0 : ℝ) < W := by exact_mod_cast hW
    rw [if_neg hq0]
    field_simp [ne_of_gt hqR, ne_of_gt hWR]
  rw [hterms, ← Finset.sum_div]
  congr 2
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

theorem coprimeHarmonicSum_le
    {W Q : ℕ} (hW : 0 < W) :
    coprimeHarmonicSum W Q ≤
      (Nat.totient W : ℝ) *
        (1 + ((harmonic Q : ℚ) : ℝ) / W) := by
  classical
  let S := (Finset.Icc 1 Q).filter (Nat.Coprime · W)
  let T := coprimeResidues W ×ˢ Finset.range (Q + 1)
  let f := coprimeBlockEncoding W
  let g := coprimeBlockWeight W
  have hinj : Function.Injective f := coprimeBlockEncoding_injective
  have himage : S.image f ⊆ T := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    exact coprimeBlockEncoding_mem_product hW hn
  calc
    coprimeHarmonicSum W Q = ∑ n ∈ S, (1 : ℝ) / n := by rfl
    _ ≤ ∑ n ∈ S, g (f n) := by
      apply Finset.sum_le_sum
      intro n hn
      exact one_div_le_coprimeBlockWeight hW hn
    _ = ∑ x ∈ S.image f, g x := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hinj hab
    _ ≤ ∑ x ∈ T, g x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro x hx hxNot
      unfold g coprimeBlockWeight
      split_ifs <;> positivity
    _ = (Nat.totient W : ℝ) *
        (1 + ((harmonic Q : ℚ) : ℝ) / W) := by
      unfold T g coprimeBlockWeight
      rw [Finset.sum_product]
      simp only
      rw [Finset.sum_const, nsmul_eq_mul, card_coprimeResidues,
        sum_range_coprimeBlockWeight hW]

end BoundedGaps.Maynard
