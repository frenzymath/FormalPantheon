import PrimesRestrictedDigits.Statement
/-! # Comparability -/

namespace PrimesRestrictedDigits

/- The paper's strict `asymp` relation, with constants uniform over every
  parameter satisfying `valid`. -/
def UniformStrictComparableOn {ι : Type*} (valid : ι → Prop)
    (f g : ι → ℝ) : Prop :=
  ∃ lower upper : ℝ,
    0 < lower ∧ 0 < upper ∧
      ∀ i, valid i → lower * f i < g i ∧ g i < upper * f i

/-- Uniform strict comparability is symmetric after reciprocating its two
positive witnesses. No sign condition on the compared functions is needed. -/
theorem uniformStrictComparableOn_comm {ι : Type*}
    {valid : ι → Prop} {f g : ι → ℝ} :
    UniformStrictComparableOn valid f g ↔
      UniformStrictComparableOn valid g f := by
  constructor
  · rintro ⟨lower, upper, hlower, hupper, h⟩
    refine ⟨upper⁻¹, lower⁻¹, inv_pos.mpr hupper, inv_pos.mpr hlower, ?_⟩
    intro i hi
    obtain ⟨hlowerBound, hupperBound⟩ := h i hi
    exact ⟨(inv_mul_lt_iff₀ hupper).2 hupperBound,
      (lt_inv_mul_iff₀ hlower).2 hlowerBound⟩
  · rintro ⟨lower, upper, hlower, hupper, h⟩
    refine ⟨upper⁻¹, lower⁻¹, inv_pos.mpr hupper, inv_pos.mpr hlower, ?_⟩
    intro i hi
    obtain ⟨hlowerBound, hupperBound⟩ := h i hi
    exact ⟨(inv_mul_lt_iff₀ hupper).2 hupperBound,
      (lt_inv_mul_iff₀ hlower).2 hlowerBound⟩

theorem quantitativeTheorem_iff_uniformStrictComparableOn :
    quantitativeTheorem ↔
      UniformStrictComparableOn
          (fun parameter : Fin 10 × ℝ => 4 ≤ parameter.2)
          (fun parameter =>
            (restrictedCount parameter.1 parameter.2 : ℝ) /
              Real.log parameter.2)
          (fun parameter => (restrictedPrimeCount parameter.1 parameter.2 : ℝ)) ∧
        UniformStrictComparableOn
          (fun parameter : Fin 10 × ℝ => 4 ≤ parameter.2)
          (fun parameter =>
            parameter.2 ^ (Real.log (9 : ℝ) / Real.log (10 : ℝ)) /
              Real.log parameter.2)
          (fun parameter =>
            (restrictedCount parameter.1 parameter.2 : ℝ) /
              Real.log parameter.2) := by
  constructor
  · rintro ⟨c₁, c₂, c₃, c₄, hc₁, hc₂, hc₃, hc₄, h⟩
    refine ⟨⟨c₁, c₂, hc₁, hc₂, ?_⟩, ⟨c₃, c₄, hc₃, hc₄, ?_⟩⟩
    · rintro ⟨a, X⟩ hX
      exact ⟨(h a X hX).1, (h a X hX).2.1⟩
    · rintro ⟨a, X⟩ hX
      exact ⟨(h a X hX).2.2.1, (h a X hX).2.2.2⟩
  · rintro ⟨⟨c₁, c₂, hc₁, hc₂, hprime⟩,
      ⟨c₃, c₄, hc₃, hc₄, hcount⟩⟩
    refine ⟨c₁, c₂, c₃, c₄, hc₁, hc₂, hc₃, hc₄, ?_⟩
    intro a X hX
    exact ⟨(hprime (a, X) hX).1, (hprime (a, X) hX).2,
      (hcount (a, X) hX).1, (hcount (a, X) hX).2⟩

/--
The proposition is exactly equivalent to the literal orientation of both `asymp` links in the
published Theorem 1.1.
-/
theorem quantitativeTheorem_iff_paperStrictComparableOn :
    quantitativeTheorem ↔
      UniformStrictComparableOn
          (fun parameter : Fin 10 × ℝ => 4 ≤ parameter.2)
          (fun parameter =>
            (restrictedPrimeCount parameter.1 parameter.2 : ℝ))
          (fun parameter =>
            (restrictedCount parameter.1 parameter.2 : ℝ) /
              Real.log parameter.2) ∧
        UniformStrictComparableOn
          (fun parameter : Fin 10 × ℝ => 4 ≤ parameter.2)
          (fun parameter =>
            (restrictedCount parameter.1 parameter.2 : ℝ) /
              Real.log parameter.2)
          (fun parameter =>
            parameter.2 ^ (Real.log (9 : ℝ) / Real.log (10 : ℝ)) /
              Real.log parameter.2) := by
  rw [quantitativeTheorem_iff_uniformStrictComparableOn]
  constructor
  · rintro ⟨hprime, hcount⟩
    exact ⟨uniformStrictComparableOn_comm.mp hprime,
      uniformStrictComparableOn_comm.mp hcount⟩
  · rintro ⟨hprime, hcount⟩
    exact ⟨uniformStrictComparableOn_comm.mp hprime,
      uniformStrictComparableOn_comm.mp hcount⟩

end PrimesRestrictedDigits
