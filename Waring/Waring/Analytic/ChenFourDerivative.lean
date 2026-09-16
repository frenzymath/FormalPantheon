import Waring.Analytic.ChenFourMultiplicity

/-!
# Derivative roots in Chen's Lemma 4

This file packages the formal derivative of Chen's quintic phase and proves
that its roots modulo a prime have total multiplicity at most four.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Chen's quintic phase as a formal polynomial. -/
noncomputable def fifthPolynomialFormal {R : Type*} [Semiring R]
    (a₀ a₁ a₂ a₃ a₄ : R) : Polynomial R :=
  Polynomial.monomial 5 a₀ + Polynomial.monomial 4 a₁ +
    Polynomial.monomial 3 a₂ + Polynomial.monomial 2 a₃ +
    Polynomial.monomial 1 a₄

@[simp] theorem eval_fifthPolynomialFormal {R : Type*} [Semiring R]
    (a₀ a₁ a₂ a₃ a₄ x : R) :
    (fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄).eval x =
      fifthPolynomial a₀ a₁ a₂ a₃ a₄ x := by
  simp [fifthPolynomialFormal, fifthPolynomial]

/-- The formal derivative of `fifthPolynomial`. -/
noncomputable def fifthPolynomialDerivative {R : Type*} [Semiring R]
    (a₀ a₁ a₂ a₃ a₄ : R) : Polynomial R :=
  Polynomial.monomial 4 (5 * a₀) +
    Polynomial.monomial 3 (4 * a₁) +
    Polynomial.monomial 2 (3 * a₂) +
    Polynomial.monomial 1 (2 * a₃) + Polynomial.monomial 0 a₄

/-- The explicit derivative agrees with Mathlib's formal derivative. -/
theorem derivative_fifthPolynomialFormal {R : Type*} [CommSemiring R]
    (a₀ a₁ a₂ a₃ a₄ : R) :
    (fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄).derivative =
      fifthPolynomialDerivative a₀ a₁ a₂ a₃ a₄ := by
  simp [fifthPolynomialFormal, fifthPolynomialDerivative, mul_comm]
  norm_num

@[simp] theorem eval_fifthPolynomialDerivative {R : Type*} [Semiring R]
    (a₀ a₁ a₂ a₃ a₄ x : R) :
    (fifthPolynomialDerivative a₀ a₁ a₂ a₃ a₄).eval x =
      5 * a₀ * x ^ 4 + 4 * a₁ * x ^ 3 + 3 * a₂ * x ^ 2 +
        2 * a₃ * x + a₄ := by
  simp [fifthPolynomialDerivative]

/-- The formal derivative has degree at most four, including when leading
coefficients vanish. -/
theorem natDegree_fifthPolynomialDerivative_le {R : Type*} [Semiring R]
    (a₀ a₁ a₂ a₃ a₄ : R) :
    (fifthPolynomialDerivative a₀ a₁ a₂ a₃ a₄).natDegree ≤ 4 := by
  have hterm (a : R) (n : Nat) (hn : n ≤ 4) :
      (Polynomial.monomial n a).natDegree ≤ 4 :=
    (Polynomial.natDegree_monomial_le a).trans hn
  unfold fifthPolynomialDerivative
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact hterm _ 4 le_rfl
        · exact hterm _ 3 (by omega)
      · exact hterm _ 2 (by omega)
    · exact hterm (2 * a₃) 1 (by omega)
  · exact hterm a₄ 0 (by omega)

/-- Over a prime field of characteristic greater than five, primitiveness of
the five coefficients makes the formal derivative nonzero. -/
theorem fifthPolynomialDerivative_ne_zero {p : Nat} (hpPrime : p.Prime)
    (hp : 11 ≤ p) (a₀ a₁ a₂ a₃ a₄ : ZMod p)
    (hcoeff : a₀ ≠ 0 ∨ a₁ ≠ 0 ∨ a₂ ≠ 0 ∨ a₃ ≠ 0 ∨ a₄ ≠ 0) :
    fifthPolynomialDerivative a₀ a₁ a₂ a₃ a₄ ≠ 0 := by
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hcast (n : Nat) (hnPos : 0 < n) (hn : n < p) :
      (n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hnPos hn
  intro hzero
  rcases hcoeff with ha₀ | ha₁ | ha₂ | ha₃ | ha₄
  · have hc := congrArg (fun f : Polynomial (ZMod p) ↦ f.coeff 4) hzero
    norm_num [fifthPolynomialDerivative, Polynomial.coeff_monomial] at hc
    exact ha₀ (hc.resolve_left (hcast 5 (by omega) (by omega)))
  · have hc := congrArg (fun f : Polynomial (ZMod p) ↦ f.coeff 3) hzero
    norm_num [fifthPolynomialDerivative, Polynomial.coeff_monomial] at hc
    exact ha₁ (hc.resolve_left (hcast 4 (by omega) (by omega)))
  · have hc := congrArg (fun f : Polynomial (ZMod p) ↦ f.coeff 2) hzero
    norm_num [fifthPolynomialDerivative, Polynomial.coeff_monomial] at hc
    exact ha₂ (hc.resolve_left (hcast 3 (by omega) (by omega)))
  · have hc := congrArg (fun f : Polynomial (ZMod p) ↦ f.coeff 1) hzero
    norm_num [fifthPolynomialDerivative, Polynomial.coeff_monomial] at hc
    exact ha₃ (hc.resolve_left (hcast 2 (by omega) (by omega)))
  · have hc := congrArg (fun f : Polynomial (ZMod p) ↦ f.coeff 0) hzero
    exact ha₄ (by simpa [fifthPolynomialDerivative] using hc)

/-- Distinct critical residues of the quintic phase. Mathlib defines the roots
of the zero polynomial to be empty, so uses as a complete stationary set must
also carry `fifthPolynomialDerivative_ne_zero`. -/
noncomputable def fifthDerivativeRoots {p : Nat} [Fact p.Prime]
    (a₀ a₁ a₂ a₃ a₄ : ZMod p) : Finset (ZMod p) :=
  (fifthPolynomialDerivative a₀ a₁ a₂ a₃ a₄).roots.toFinset

/-- Multiplicity of a critical residue in the formal derivative. -/
noncomputable def fifthDerivativeMultiplicity {p : Nat} [Fact p.Prime]
    (a₀ a₁ a₂ a₃ a₄ x : ZMod p) : Nat :=
  Polynomial.rootMultiplicity x
    (fifthPolynomialDerivative a₀ a₁ a₂ a₃ a₄)

/-- Vanishing of a nonzero formal derivative is membership in its finite set
of distinct roots. -/
theorem eval_fifthPolynomialDerivative_eq_zero_iff_mem_roots {p : Nat}
    [Fact p.Prime] (a₀ a₁ a₂ a₃ a₄ x : ZMod p)
    (hderivative : fifthPolynomialDerivative a₀ a₁ a₂ a₃ a₄ ≠ 0) :
    (fifthPolynomialDerivative a₀ a₁ a₂ a₃ a₄).eval x = 0 ↔
      x ∈ fifthDerivativeRoots a₀ a₁ a₂ a₃ a₄ := by
  rw [fifthDerivativeRoots, Multiset.mem_toFinset,
    Polynomial.mem_roots hderivative, Polynomial.IsRoot.def]

/-- Every listed critical residue has positive multiplicity. -/
theorem fifthDerivativeMultiplicity_pos_of_mem {p : Nat} [Fact p.Prime]
    (a₀ a₁ a₂ a₃ a₄ : ZMod p) {x : ZMod p}
    (hx : x ∈ fifthDerivativeRoots a₀ a₁ a₂ a₃ a₄) :
    1 ≤ fifthDerivativeMultiplicity a₀ a₁ a₂ a₃ a₄ x := by
  apply (Polynomial.rootMultiplicity_pos').2
  apply (Polynomial.mem_roots').1
  simpa [fifthDerivativeRoots] using hx

/-- The sum of the distinct derivative-root multiplicities is at most four. -/
theorem sum_fifthDerivativeMultiplicity_le_four {p : Nat} [Fact p.Prime]
    (a₀ a₁ a₂ a₃ a₄ : ZMod p) :
    ∑ x ∈ fifthDerivativeRoots a₀ a₁ a₂ a₃ a₄,
        fifthDerivativeMultiplicity a₀ a₁ a₂ a₃ a₄ x ≤ 4 := by
  let derivative := fifthPolynomialDerivative a₀ a₁ a₂ a₃ a₄
  calc
    ∑ x ∈ fifthDerivativeRoots a₀ a₁ a₂ a₃ a₄,
        fifthDerivativeMultiplicity a₀ a₁ a₂ a₃ a₄ x =
        derivative.roots.card := by
      simpa only [fifthDerivativeRoots, fifthDerivativeMultiplicity,
        Polynomial.count_roots] using
          (Multiset.toFinset_sum_count_eq derivative.roots)
    _ ≤ derivative.natDegree := Polynomial.card_roots' derivative
    _ ≤ 4 := natDegree_fifthPolynomialDerivative_le a₀ a₁ a₂ a₃ a₄

/-- Any stationary exponents on Mathlib's finite derivative-root set, bounded
by root multiplicity plus one, have total normalized induction weight at most
one. The later stationary-residue bridge supplies derivative nonzeroness. -/
theorem sum_fifthDerivative_stationaryWeight_le_one {p : Nat} [Fact p.Prime]
    (hp : 11 ≤ p) (a₀ a₁ a₂ a₃ a₄ : ZMod p) (sigma : ZMod p → Nat)
    (hsigma : ∀ x ∈ fifthDerivativeRoots a₀ a₁ a₂ a₃ a₄,
      sigma x ≤ fifthDerivativeMultiplicity a₀ a₁ a₂ a₃ a₄ x + 1) :
    ∑ x ∈ fifthDerivativeRoots a₀ a₁ a₂ a₃ a₄,
        (p : Real) ^ ((sigma x : Real) / 5 - 1) ≤ 1 := by
  exact sum_chen_four_stationaryWeight_le_one p
    (fifthDerivativeRoots a₀ a₁ a₂ a₃ a₄)
    (fifthDerivativeMultiplicity a₀ a₁ a₂ a₃ a₄) sigma hp
    (fun x hx ↦ fifthDerivativeMultiplicity_pos_of_mem a₀ a₁ a₂ a₃ a₄ hx)
    (sum_fifthDerivativeMultiplicity_le_four a₀ a₁ a₂ a₃ a₄) hsigma

end Waring.Analytic
