import Waring.Analytic.HuaTranslation

/-!
# Derivative data for Hua's prime-power induction

Hua's recursion only needs a chosen exact factorization `F' = p^t D` whose
normalized factor is nonzero modulo `p`.  Carrying this data explicitly avoids
identifying two canonical content quotients definitionally.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- An exact derivative normalization for an integer polynomial at `p`. -/
structure HuaDerivativeData (p : Nat) (F : Polynomial Int) where
  /-- The extracted derivative coefficient exponent. -/
  exponent : Nat
  /-- The normalized integer derivative. -/
  normalized : Polynomial Int
  /-- Exact derivative factorization. -/
  derivative_eq :
    F.derivative = Polynomial.C ((p : Int) ^ exponent) * normalized
  /-- The normalized derivative is nonzero modulo `p`. -/
  map_normalized_ne_zero :
    normalized.map (Int.castRingHom (ZMod p)) ≠ 0

/-- Distinct roots of the chosen normalized derivative. -/
noncomputable def HuaDerivativeData.roots {p : Nat} [Fact p.Prime]
    {F : Polynomial Int} (d : HuaDerivativeData p F) : Finset (ZMod p) :=
  (d.normalized.map (Int.castRingHom (ZMod p))).roots.toFinset

/-- Polynomial multiplicity of a root of the chosen normalized derivative. -/
noncomputable def HuaDerivativeData.multiplicity {p : Nat} [Fact p.Prime]
    {F : Polynomial Int} (d : HuaDerivativeData p F) (x : ZMod p) : Nat :=
  Polynomial.rootMultiplicity x
    (d.normalized.map (Int.castRingHom (ZMod p)))

/-- Total root multiplicity of the chosen normalized derivative. -/
noncomputable def HuaDerivativeData.complexity {p : Nat} [Fact p.Prime]
    {F : Polynomial Int} (d : HuaDerivativeData p F) : Nat :=
  ∑ x ∈ d.roots, d.multiplicity x

/-- Derivative complexity is the cardinality of the normalized derivative's
root multiset. -/
theorem HuaDerivativeData.complexity_eq_card_roots
    {p : Nat} [Fact p.Prime] {F : Polynomial Int}
    (d : HuaDerivativeData p F) :
    d.complexity =
      (d.normalized.map (Int.castRingHom (ZMod p))).roots.card := by
  simpa only [HuaDerivativeData.complexity, HuaDerivativeData.roots,
    HuaDerivativeData.multiplicity, Polynomial.count_roots] using
      (Multiset.toFinset_sum_count_eq
        (d.normalized.map (Int.castRingHom (ZMod p))).roots)

/-- Total normalized derivative-root multiplicity is bounded by its degree. -/
theorem HuaDerivativeData.complexity_le_natDegree
    {p : Nat} [Fact p.Prime] {F : Polynomial Int}
    (d : HuaDerivativeData p F) :
    d.complexity ≤
      (d.normalized.map (Int.castRingHom (ZMod p))).natDegree := by
  rw [d.complexity_eq_card_roots]
  exact Polynomial.card_roots' _

/-- Every member of the chosen normalized derivative root set has positive
polynomial multiplicity. -/
theorem HuaDerivativeData.multiplicity_pos_of_mem
    {p : Nat} [Fact p.Prime] {F : Polynomial Int}
    (d : HuaDerivativeData p F) {x : ZMod p} (hx : x ∈ d.roots) :
    1 ≤ d.multiplicity x := by
  apply (Polynomial.rootMultiplicity_pos').2
  constructor
  · exact d.map_normalized_ne_zero
  · apply (Polynomial.mem_roots d.map_normalized_ne_zero).1
    simpa only [HuaDerivativeData.roots, Multiset.mem_toFinset] using hx

/-- The canonical content quotient supplies derivative data whenever the
integer derivative is nonzero. -/
noncomputable def canonicalHuaDerivativeData
    {p : Nat} [Fact p.Prime] (F : Polynomial Int)
    (hderivative : F.derivative ≠ 0) : HuaDerivativeData p F where
  exponent := huaDerivativeExponent p F
  normalized := huaNormalizedDerivative p F
  derivative_eq := derivative_eq_C_pow_mul_huaNormalizedDerivative p F
  map_normalized_ne_zero := huaDerivativePolynomial_ne_zero F hderivative

/-- Scaling and translating commutes with multiplication by a constant
polynomial. -/
theorem huaScaledTranslate_C_mul (p : Nat) (x c : Int)
    (A : Polynomial Int) :
    huaScaledTranslate p x (Polynomial.C c * A) =
      Polynomial.C c * huaScaledTranslate p x A := by
  simp [huaScaledTranslate, Polynomial.taylor_apply, Polynomial.comp_assoc]

/-- Differentiating a scaled Taylor difference contributes one factor of the
scale and translates the original derivative. -/
theorem derivative_scaledTaylorDifference_eq_C_mul_huaScaledTranslate
    (p : Nat) (x : Int) (F : Polynomial Int) :
    (scaledTaylorDifference (p : Int) x F).derivative =
      Polynomial.C (p : Int) * huaScaledTranslate p x F.derivative := by
  simp [scaledTaylorDifference, huaScaledTranslate, Polynomial.taylor_apply,
    Polynomial.derivative_comp, Polynomial.comp_assoc]

end Waring.Analytic
