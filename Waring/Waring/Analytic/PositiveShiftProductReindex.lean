import Waring.Analytic.RestrictedQuadraticFiber
import Waring.Analytic.WeylFifthPhaseCorrelation

/-!
# Reindexing positive Weyl shifts by their product

The zero-based triple-shift simplex in `weylDThree` is exactly the disjoint
union of Chen's restricted triple-product fibers.  This file proves the
corresponding finite-sum identity for an arbitrary factor-dependent summand.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The flattened zero-based index set for three positive Weyl shifts. -/
def positiveShiftTripleChoices (P : Nat) :
    Finset (Sigma fun _ : Nat ↦ Sigma fun _ : Nat ↦ Nat) :=
  (Finset.range P).sigma fun h₁ ↦
    (Finset.range (P - h₁ - 1)).sigma fun h₂ ↦
      Finset.range (P - h₁ - 1 - h₂ - 1)

/-- The flattened union of restricted divisor fibers on their exact
`P ^ 3 / 27` product support. -/
def restrictedProductTripleChoices (P : Nat) :
    Finset (Sigma fun _ : Nat ↦ Sigma fun _ : Nat ↦ Nat) :=
  (Finset.Icc 1 (P ^ 3 / 27)).sigma fun z ↦
    restrictedTripleDivisorChoices P z

private def positiveShiftToProduct
    (u : Sigma fun _ : Nat ↦ Sigma fun _ : Nat ↦ Nat) :
    Sigma fun _ : Nat ↦ Sigma fun _ : Nat ↦ Nat :=
  let l₁ := u.1 + 1
  let l₂ := u.2.1 + 1
  let l₃ := u.2.2 + 1
  ⟨l₁ * l₂ * l₃, ⟨l₁ * l₂, l₁⟩⟩

private def productToPositiveShift
    (u : Sigma fun _ : Nat ↦ Sigma fun _ : Nat ↦ Nat) :
    Sigma fun _ : Nat ↦ Sigma fun _ : Nat ↦ Nat :=
  ⟨u.2.2 - 1, ⟨u.2.1 / u.2.2 - 1, u.1 / u.2.1 - 1⟩⟩

private theorem positiveShiftToProduct_mem {P : Nat}
    {u : Sigma fun _ : Nat ↦ Sigma fun _ : Nat ↦ Nat}
    (hu : u ∈ positiveShiftTripleChoices P) :
    positiveShiftToProduct u ∈ restrictedProductTripleChoices P := by
  rcases u with ⟨h₁, ⟨h₂, h₃⟩⟩
  have hranges : h₁ < P ∧ h₂ < P - h₁ - 1 ∧
      h₃ < P - h₁ - 1 - h₂ - 1 := by
    simpa [positiveShiftTripleChoices] using hu
  let l₁ := h₁ + 1
  let l₂ := h₂ + 1
  let l₃ := h₃ + 1
  let z := l₁ * l₂ * l₃
  let d := l₁ * l₂
  have hsum : l₁ + l₂ + l₃ ≤ P := by
    dsimp [l₁, l₂, l₃]
    omega
  have hzpos : 0 < z := by
    dsimp [z, l₁, l₂, l₃]
    positivity
  have hdvdz : d ∣ z := by
    refine ⟨l₃, ?_⟩
    dsimp [d, z]
  have hl₁dvdd : l₁ ∣ d := by
    exact ⟨l₂, by simp [d]⟩
  have hfiber : (⟨d, l₁⟩ : Sigma fun _ : Nat ↦ Nat) ∈
      restrictedTripleDivisorChoices P z := by
    rw [restrictedTripleDivisorChoices, Finset.mem_filter]
    constructor
    · rw [tripleDivisorChoices, Finset.mem_sigma]
      exact ⟨Nat.mem_divisors.mpr ⟨hdvdz, Nat.ne_of_gt hzpos⟩,
        Nat.mem_divisors.mpr ⟨hl₁dvdd, by
          dsimp [d, l₁, l₂]
          positivity⟩⟩
    · have hdl₁ : d / l₁ = l₂ := by
        dsimp [d]
        exact Nat.mul_div_right l₂ (by positivity : 0 < l₁)
      have hzd : z / d = l₃ := by
        dsimp [z, d]
        exact Nat.mul_div_right l₃ (by
          dsimp [l₁, l₂]
          positivity : 0 < l₁ * l₂)
      simpa [hdl₁, hzd] using hsum
  have hsupport : 27 * z ≤ P ^ 3 := by
    apply restrictedTripleDivisorCount_support
    rw [restrictedTripleDivisorCount, Finset.card_pos]
    exact ⟨⟨d, l₁⟩, hfiber⟩
  have hzupper : z ≤ P ^ 3 / 27 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 27)]
    simpa [Nat.mul_comm] using hsupport
  rw [restrictedProductTripleChoices, Finset.mem_sigma]
  change z ∈ Finset.Icc 1 (P ^ 3 / 27) ∧
    (⟨d, l₁⟩ : Sigma fun _ : Nat ↦ Nat) ∈
      restrictedTripleDivisorChoices P z
  exact ⟨Finset.mem_Icc.mpr ⟨hzpos, hzupper⟩, hfiber⟩

private theorem productToPositiveShift_mem {P : Nat}
    {u : Sigma fun _ : Nat ↦ Sigma fun _ : Nat ↦ Nat}
    (hu : u ∈ restrictedProductTripleChoices P) :
    productToPositiveShift u ∈ positiveShiftTripleChoices P := by
  rcases u with ⟨z, ⟨d, a⟩⟩
  have huData : z ∈ Finset.Icc 1 (P ^ 3 / 27) ∧
      (⟨d, a⟩ : Sigma fun _ : Nat ↦ Nat) ∈
        restrictedTripleDivisorChoices P z := by
    simpa [restrictedProductTripleChoices] using hu
  have hchoice := restrictedTripleDivisorChoice_data huData.2
  have hzpos : 0 < z := lt_of_lt_of_le Nat.zero_lt_one
    (Finset.mem_Icc.mp huData.1).1
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hchoice.1.1 hzpos
  have hapos : 0 < a := Nat.pos_of_dvd_of_pos hchoice.1.2 hdpos
  have hadivpos : 0 < d / a :=
    Nat.div_pos (Nat.le_of_dvd hdpos hchoice.1.2) hapos
  have hddivpos : 0 < z / d :=
    Nat.div_pos (Nat.le_of_dvd hzpos hchoice.1.1) hdpos
  have hsumStored :
      (a - 1 + 1) + (d / a - 1 + 1) + (z / d - 1 + 1) ≤ P := by
    simpa [Nat.sub_add_cancel hapos, Nat.sub_add_cancel hadivpos,
      Nat.sub_add_cancel hddivpos] using hchoice.2
  have hranges := (mem_three_positiveShift_range_iff P
    (a - 1) (d / a - 1) (z / d - 1)).2 hsumStored
  simpa only [positiveShiftTripleChoices, productToPositiveShift,
    Finset.mem_sigma] using hranges

private theorem productToPositiveShift_leftInverse {P : Nat}
    {u : Sigma fun _ : Nat ↦ Sigma fun _ : Nat ↦ Nat}
    (_hu : u ∈ positiveShiftTripleChoices P) :
    productToPositiveShift (positiveShiftToProduct u) = u := by
  rcases u with ⟨h₁, ⟨h₂, h₃⟩⟩
  simp [positiveShiftToProduct, productToPositiveShift]

private theorem productToPositiveShift_rightInverse {P : Nat}
    {u : Sigma fun _ : Nat ↦ Sigma fun _ : Nat ↦ Nat}
    (hu : u ∈ restrictedProductTripleChoices P) :
    positiveShiftToProduct (productToPositiveShift u) = u := by
  rcases u with ⟨z, ⟨d, a⟩⟩
  have huData : z ∈ Finset.Icc 1 (P ^ 3 / 27) ∧
      (⟨d, a⟩ : Sigma fun _ : Nat ↦ Nat) ∈
        restrictedTripleDivisorChoices P z := by
    simpa [restrictedProductTripleChoices] using hu
  have hchoice := restrictedTripleDivisorChoice_data huData.2
  have hzpos : 0 < z := lt_of_lt_of_le Nat.zero_lt_one
    (Finset.mem_Icc.mp huData.1).1
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hchoice.1.1 hzpos
  have hapos : 0 < a := Nat.pos_of_dvd_of_pos hchoice.1.2 hdpos
  have hadivpos : 0 < d / a :=
    Nat.div_pos (Nat.le_of_dvd hdpos hchoice.1.2) hapos
  have hddivpos : 0 < z / d :=
    Nat.div_pos (Nat.le_of_dvd hzpos hchoice.1.1) hdpos
  have hda : a * (d / a) = d := Nat.mul_div_cancel' hchoice.1.2
  have hzd : d * (z / d) = z := Nat.mul_div_cancel' hchoice.1.1
  simp only [positiveShiftToProduct, productToPositiveShift]
  simp [Nat.sub_add_cancel hapos, Nat.sub_add_cancel hadivpos,
    Nat.sub_add_cancel hddivpos, hda, hzd]

/-- Reindex the nested zero-based triple-shift simplex as the disjoint union
of restricted product fibers. -/
theorem sum_positiveShiftTriple_eq_sum_restrictedProduct
    {M : Type*} [AddCommMonoid M] (P : Nat)
    (f : Nat → Nat → Nat → M) :
    (∑ h₁ ∈ Finset.range P,
      ∑ h₂ ∈ Finset.range (P - h₁ - 1),
        ∑ h₃ ∈ Finset.range (P - h₁ - 1 - h₂ - 1),
          f (h₁ + 1) (h₂ + 1) (h₃ + 1)) =
      ∑ z ∈ Finset.Icc 1 (P ^ 3 / 27),
        ∑ x ∈ restrictedTripleDivisorChoices P z,
          f x.2 (x.1 / x.2) (z / x.1) := by
  have hflat :
      (∑ u ∈ positiveShiftTripleChoices P,
          f (u.1 + 1) (u.2.1 + 1) (u.2.2 + 1)) =
        ∑ u ∈ restrictedProductTripleChoices P,
          f u.2.2 (u.2.1 / u.2.2) (u.1 / u.2.1) := by
    apply Finset.sum_bij'
      (fun u _ ↦ positiveShiftToProduct u)
      (fun u _ ↦ productToPositiveShift u)
    · exact fun _ hu ↦ positiveShiftToProduct_mem hu
    · exact fun _ hu ↦ productToPositiveShift_mem hu
    · exact fun _ hu ↦ productToPositiveShift_leftInverse hu
    · exact fun _ hu ↦ productToPositiveShift_rightInverse hu
    · intro u hu
      rcases u with ⟨h₁, ⟨h₂, h₃⟩⟩
      simp [positiveShiftToProduct]
  simpa only [positiveShiftTripleChoices, restrictedProductTripleChoices,
    Finset.sum_sigma'] using hflat

/-- For the rational fifth-power phase, the third Weyl aggregate is exactly
the sum of the restricted quadratic values grouped by their shift product. -/
theorem weylDThree_fifthPowerChar_eq_restrictedQuadraticValue
    {q : Nat} [NeZero q] (a : ZMod q) (P : Nat) :
    weylDThree (fifthPowerChar a) P =
      ∑ z ∈ Finset.Icc 1 (P ^ 3 / 27),
        ∑ x ∈ restrictedTripleDivisorChoices P z,
          restrictedQuadraticValue a P z x := by
  have hremaining (h₁ h₂ h₃ : Nat) :
      P - h₁ - 1 - h₂ - 1 - h₃ - 1 =
        P - ((h₁ + 1) + (h₂ + 1) + (h₃ + 1)) := by
    omega
  rw [weylDThree]
  simp_rw [norm_thirdPositiveShiftSum_fifthPowerChar_eq, hremaining]
  simpa only [restrictedQuadraticValue] using
    (sum_positiveShiftTriple_eq_sum_restrictedProduct P
      (fun l₁ l₂ l₃ ↦
        ‖∑ y ∈ Finset.range (P - (l₁ + l₂ + l₃)),
          fifthQuadraticChar a l₁ l₂ l₃ (y + 1)‖))

end Waring.Analytic
