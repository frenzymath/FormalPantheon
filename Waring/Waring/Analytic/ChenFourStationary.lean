import Waring.Analytic.ChenFourDerivative

/-!
# Stationary residue decomposition in Chen's Lemma 4

This file proves the exact last-digit Taylor decomposition and character
cancellation used in the prime-power induction [CHEN1964-EN, p. 1549].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The last-digit shift has square zero modulo `p^2*s`. -/
theorem primeLastDigit_sq_eq_zero (p s : Nat)
    (xi : ZMod (p * (p * s))) :
    (((p * s : Nat) : ZMod (p * (p * s))) * xi) ^ 2 = 0 := by
  calc
    (((p * s : Nat) : ZMod (p * (p * s))) * xi) ^ 2 =
        ((p * (p * s) : Nat) : ZMod (p * (p * s))) *
          (s : ZMod (p * (p * s))) * xi ^ 2 := by
      push_cast
      ring
    _ = 0 := by rw [ZMod.natCast_self]; simp

/-- Taylor expansion at a last-digit shift is exactly linear modulo
`p^2*s`. -/
theorem fifthPolynomial_add_primeLastDigit (p s : Nat)
    (a₀ a₁ a₂ a₃ a₄ eta xi : ZMod (p * (p * s))) :
    fifthPolynomial a₀ a₁ a₂ a₃ a₄
        (eta + ((p * s : Nat) : ZMod (p * (p * s))) * xi) =
      fifthPolynomial a₀ a₁ a₂ a₃ a₄ eta +
        (fifthPolynomialDerivative a₀ a₁ a₂ a₃ a₄).eval eta *
          (((p * s : Nat) : ZMod (p * (p * s))) * xi) := by
  rw [← eval_fifthPolynomialFormal, Polynomial.eval_add_of_sq_eq_zero]
  · rw [derivative_fifthPolynomialFormal, eval_fifthPolynomialFormal]
  · exact primeLastDigit_sq_eq_zero p s xi

/-- Reindex a complete polynomial sum into residue classes modulo `p*s` and
their final base-`p` digit. -/
theorem polynomialCompleteSum_primeLastDigit_reindex (p s : Nat)
    [NeZero p] [NeZero s] (a₀ a₁ a₂ a₃ a₄ : ZMod (p * (p * s))) :
    polynomialCompleteSum a₀ a₁ a₂ a₃ a₄ =
      ∑ eta : Fin (p * s),
        ZMod.stdAddChar
            (fifthPolynomial a₀ a₁ a₂ a₃ a₄
              ((eta : Nat) : ZMod (p * (p * s)))) *
          ∑ xi : Fin p,
            ZMod.stdAddChar
              ((fifthPolynomialDerivative a₀ a₁ a₂ a₃ a₄).eval
                  ((eta : Nat) : ZMod (p * (p * s))) *
                (((p * s : Nat) : ZMod (p * (p * s))) *
                  ((xi : Nat) : ZMod (p * (p * s))))) := by
  rw [polynomialCompleteSum]
  rw [← (ZMod.finEquiv (p * (p * s))).toEquiv.sum_comp]
  rw [← (finProdFinEquiv : Fin p × Fin (p * s) ≃
    Fin (p * (p * s))).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro eta _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xi _
  rw [show
      (ZMod.finEquiv (p * (p * s))).toEquiv (finProdFinEquiv (xi, eta)) =
        ((eta : Nat) : ZMod (p * (p * s))) +
          (p * s : Nat) * ((xi : Nat) : ZMod (p * (p * s))) by
    change ZMod.finEquiv (p * (p * s)) (finProdFinEquiv (xi, eta)) = _
    rw [zmod_finEquiv_apply]
    change ((eta.val + (p * s) * xi.val : Nat) : ZMod (p * (p * s))) = _
    push_cast
    ring]
  rw [fifthPolynomial_add_primeLastDigit]
  rw [ZMod.stdAddChar.map_add_eq_mul]

/-- Scaling the reduction of a residue modulo `p` back by the complementary
modulus agrees with multiplying the original residue by that modulus. -/
theorem zmodScale_val_reduction (p m : Nat) [NeZero p] [NeZero m]
    (x : ZMod p)
    (a : ZMod (p * m)) :
    zmodScale p m (x * (a.val : ZMod p)) =
      (m : ZMod (p * m)) * (x.val : ZMod (p * m)) * a := by
  calc
    zmodScale p m (x * (a.val : ZMod p)) =
        zmodScale p m ((x.val * a.val : Nat) : ZMod p) := by
      congr 1
      rw [Nat.cast_mul, x.natCast_zmod_val]
    _ = (m : ZMod (p * m)) *
        ((x.val * a.val : Nat) : ZMod (p * m)) := by
      simpa only [Int.cast_natCast] using
        zmodScale_intCast p m ((x.val * a.val : Nat) : Int)
    _ = (m : ZMod (p * m)) * (x.val : ZMod (p * m)) * a := by
      rw [Nat.cast_mul, a.natCast_zmod_val]
      ring

/-- Canonical reduction from a composite modulus `p*m` to its factor `p`. -/
def zmodPrimeReduction (p m : Nat) : ZMod (p * m) →+* ZMod p :=
  ZMod.castHom (dvd_mul_right p m) (ZMod p)

@[simp] theorem zmodPrimeReduction_apply_eq_val (p m : Nat) [NeZero p]
    [NeZero m] (a : ZMod (p * m)) :
    zmodPrimeReduction p m a = (a.val : ZMod p) := by
  rw [zmodPrimeReduction, ZMod.castHom_apply, ZMod.cast_eq_val]

/-- Reduction along a divisor of the modulus commutes with evaluation of the
formal quintic derivative. -/
theorem castHom_eval_fifthPolynomialDerivative {p q : Nat} (hpq : p ∣ q)
    (a₀ a₁ a₂ a₃ a₄ x : ZMod q) :
    ZMod.castHom hpq (ZMod p)
        ((fifthPolynomialDerivative a₀ a₁ a₂ a₃ a₄).eval x) =
      (fifthPolynomialDerivative
          (ZMod.castHom hpq (ZMod p) a₀)
          (ZMod.castHom hpq (ZMod p) a₁)
          (ZMod.castHom hpq (ZMod p) a₂)
          (ZMod.castHom hpq (ZMod p) a₃)
          (ZMod.castHom hpq (ZMod p) a₄)).eval
        (ZMod.castHom hpq (ZMod p) x) := by
  simp only [eval_fifthPolynomialDerivative, map_add, map_mul, map_pow,
    map_ofNat]

/-- The preceding compatibility specialized to `zmodPrimeReduction`. -/
theorem zmodPrimeReduction_eval_fifthPolynomialDerivative (p m : Nat)
    (a₀ a₁ a₂ a₃ a₄ x : ZMod (p * m)) :
    zmodPrimeReduction p m
        ((fifthPolynomialDerivative a₀ a₁ a₂ a₃ a₄).eval x) =
      (fifthPolynomialDerivative
          (zmodPrimeReduction p m a₀) (zmodPrimeReduction p m a₁)
          (zmodPrimeReduction p m a₂) (zmodPrimeReduction p m a₃)
          (zmodPrimeReduction p m a₄)).eval (zmodPrimeReduction p m x) := by
  simpa only [zmodPrimeReduction] using
    castHom_eval_fifthPolynomialDerivative (dvd_mul_right p m)
      a₀ a₁ a₂ a₃ a₄ x

/-- The final digit sum is a complete linear character modulo `p`; it
vanishes exactly away from a derivative root modulo `p`. -/
theorem sum_primeLastDigit_eq_ite (p s : Nat) [NeZero p] [NeZero s]
    (derivativeValue : ZMod (p * (p * s))) :
    ∑ xi : Fin p,
        ZMod.stdAddChar
          (derivativeValue *
            (((p * s : Nat) : ZMod (p * (p * s))) *
              ((xi : Nat) : ZMod (p * (p * s))))) =
      if ((derivativeValue.val : Nat) : ZMod p) = 0 then p else 0 := by
  let c : ZMod p := derivativeValue.val
  calc
    ∑ xi : Fin p,
        ZMod.stdAddChar
          (derivativeValue *
            (((p * s : Nat) : ZMod (p * (p * s))) *
              ((xi : Nat) : ZMod (p * (p * s))))) =
        ∑ xi : Fin p, ZMod.stdAddChar
          (zmodScale p (p * s) (((xi : Nat) : ZMod p) * c)) := by
      apply Finset.sum_congr rfl
      intro xi _
      congr 1
      rw [zmodScale_val_reduction]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt xi.isLt]
      push_cast
      ring
    _ = if c = 0 then p else 0 := by
      simpa using sum_fin_stdAddChar_zmodScale p (p * s) c
    _ = if ((derivativeValue.val : Nat) : ZMod p) = 0 then p else 0 := rfl

/-- Only residue classes whose derivative vanishes modulo `p` survive the
last-digit character sum. -/
theorem polynomialCompleteSum_eq_stationaryResidues (p s : Nat)
    [NeZero p] [NeZero s] (a₀ a₁ a₂ a₃ a₄ : ZMod (p * (p * s))) :
    polynomialCompleteSum a₀ a₁ a₂ a₃ a₄ =
      ∑ eta : Fin (p * s),
        if (((fifthPolynomialDerivative a₀ a₁ a₂ a₃ a₄).eval
              ((eta : Nat) : ZMod (p * (p * s)))).val : ZMod p) = 0
        then (p : Complex) * ZMod.stdAddChar
          (fifthPolynomial a₀ a₁ a₂ a₃ a₄
            ((eta : Nat) : ZMod (p * (p * s))))
        else 0 := by
  rw [polynomialCompleteSum_primeLastDigit_reindex]
  apply Finset.sum_congr rfl
  intro eta _
  rw [sum_primeLastDigit_eq_ite]
  split_ifs <;> simp_all [mul_comm]

/-- The surviving condition expressed as membership in the derivative zero
set after canonical reduction to `ZMod p`. -/
theorem polynomialCompleteSum_eq_stationaryResidues_reduced (p s : Nat)
    [NeZero p] [NeZero s] (a₀ a₁ a₂ a₃ a₄ : ZMod (p * (p * s))) :
    polynomialCompleteSum a₀ a₁ a₂ a₃ a₄ =
      ∑ eta : Fin (p * s),
        if (fifthPolynomialDerivative
              (zmodPrimeReduction p (p * s) a₀)
              (zmodPrimeReduction p (p * s) a₁)
              (zmodPrimeReduction p (p * s) a₂)
              (zmodPrimeReduction p (p * s) a₃)
              (zmodPrimeReduction p (p * s) a₄)).eval
            (zmodPrimeReduction p (p * s)
              ((eta : Nat) : ZMod (p * (p * s)))) = 0
        then (p : Complex) * ZMod.stdAddChar
          (fifthPolynomial a₀ a₁ a₂ a₃ a₄
            ((eta : Nat) : ZMod (p * (p * s))))
        else 0 := by
  rw [polynomialCompleteSum_eq_stationaryResidues]
  apply Finset.sum_congr rfl
  intro eta _
  rw [← zmodPrimeReduction_eval_fifthPolynomialDerivative]
  rw [zmodPrimeReduction_apply_eq_val]

/-- For primitive reduced coefficients, the surviving residue classes are
indexed by the finite root set of the reduced derivative. -/
theorem polynomialCompleteSum_eq_derivativeRootResidues (p s : Nat)
    [Fact p.Prime] [NeZero p] [NeZero s]
    (a₀ a₁ a₂ a₃ a₄ : ZMod (p * (p * s))) (hp : 11 ≤ p)
    (hcoeff :
      zmodPrimeReduction p (p * s) a₀ ≠ 0 ∨
      zmodPrimeReduction p (p * s) a₁ ≠ 0 ∨
      zmodPrimeReduction p (p * s) a₂ ≠ 0 ∨
      zmodPrimeReduction p (p * s) a₃ ≠ 0 ∨
      zmodPrimeReduction p (p * s) a₄ ≠ 0) :
    polynomialCompleteSum a₀ a₁ a₂ a₃ a₄ =
      ∑ eta : Fin (p * s),
        if zmodPrimeReduction p (p * s)
              ((eta : Nat) : ZMod (p * (p * s))) ∈
            fifthDerivativeRoots
              (zmodPrimeReduction p (p * s) a₀)
              (zmodPrimeReduction p (p * s) a₁)
              (zmodPrimeReduction p (p * s) a₂)
              (zmodPrimeReduction p (p * s) a₃)
              (zmodPrimeReduction p (p * s) a₄)
        then (p : Complex) * ZMod.stdAddChar
          (fifthPolynomial a₀ a₁ a₂ a₃ a₄
            ((eta : Nat) : ZMod (p * (p * s))))
        else 0 := by
  rw [polynomialCompleteSum_eq_stationaryResidues_reduced]
  apply Finset.sum_congr rfl
  intro eta _
  have hderivative :=
    fifthPolynomialDerivative_ne_zero (Fact.out) hp _ _ _ _ _ hcoeff
  have hroot := eval_fifthPolynomialDerivative_eq_zero_iff_mem_roots
    _ _ _ _ _ (zmodPrimeReduction p (p * s)
      ((eta : Nat) : ZMod (p * (p * s)))) hderivative
  simp only [hroot]

/-- In the decomposition `eta = r + p*k`, canonical reduction of `eta`
modulo `p` is the low digit `r`. -/
theorem zmodPrimeReduction_finPrimeBlocks (p s : Nat)
    [NeZero p] [NeZero s] (k : Fin s) (r : Fin p) :
    zmodPrimeReduction p (p * s)
        (((finPrimeBlocks p s (k, r)).val : Nat) :
          ZMod (p * (p * s))) =
      ((r.val : Nat) : ZMod p) := by
  rw [zmodPrimeReduction_apply_eq_val, ZMod.val_natCast]
  have hlt : (finPrimeBlocks p s (k, r)).val < p * (p * s) := by
    exact (finPrimeBlocks p s (k, r)).isLt.trans_le (by
      exact le_mul_of_one_le_left' NeZero.one_le)
  rw [Nat.mod_eq_of_lt hlt, finPrimeBlocks_val]
  push_cast
  simp

/-- A sum over finite representatives selected by a residue finset is the
corresponding sum over that finset in `ZMod p`. -/
theorem sum_fin_ite_mem_zmod (p : Nat) [NeZero p]
    {M : Type*} [AddCommMonoid M] (roots : Finset (ZMod p))
    (f : ZMod p → M) :
    (∑ r : Fin p,
        if ((r.val : Nat) : ZMod p) ∈ roots
        then f ((r.val : Nat) : ZMod p)
        else 0) =
      ∑ x ∈ roots, f x := by
  simp_rw [← zmod_finEquiv_apply]
  let g : ZMod p → M := fun x ↦ if x ∈ roots then f x else 0
  change (∑ r : Fin p, g (ZMod.finEquiv p r)) = _
  have hsum := (ZMod.finEquiv p).toEquiv.sum_comp g
  change (∑ r : Fin p, g (ZMod.finEquiv p r)) =
    ∑ x : ZMod p, g x at hsum
  calc
    _ = ∑ x : ZMod p, g x := hsum
    _ = ∑ x ∈ roots, f x := by simp [g]

/-- The stationary-residue identity reindexed into its exact fibers modulo
`p`, with one block for each low residue `r`. -/
theorem polynomialCompleteSum_eq_derivativeRootBlocks (p s : Nat)
    [Fact p.Prime] [NeZero p] [NeZero s]
    (a₀ a₁ a₂ a₃ a₄ : ZMod (p * (p * s))) (hp : 11 ≤ p)
    (hcoeff :
      zmodPrimeReduction p (p * s) a₀ ≠ 0 ∨
      zmodPrimeReduction p (p * s) a₁ ≠ 0 ∨
      zmodPrimeReduction p (p * s) a₂ ≠ 0 ∨
      zmodPrimeReduction p (p * s) a₃ ≠ 0 ∨
      zmodPrimeReduction p (p * s) a₄ ≠ 0) :
    polynomialCompleteSum a₀ a₁ a₂ a₃ a₄ =
      ∑ k : Fin s, ∑ r : Fin p,
        if ((r.val : Nat) : ZMod p) ∈
            fifthDerivativeRoots
              (zmodPrimeReduction p (p * s) a₀)
              (zmodPrimeReduction p (p * s) a₁)
              (zmodPrimeReduction p (p * s) a₂)
              (zmodPrimeReduction p (p * s) a₃)
              (zmodPrimeReduction p (p * s) a₄)
        then (p : Complex) * ZMod.stdAddChar
          (fifthPolynomial a₀ a₁ a₂ a₃ a₄
            (((finPrimeBlocks p s (k, r)).val : Nat) :
              ZMod (p * (p * s))))
        else 0 := by
  rw [polynomialCompleteSum_eq_derivativeRootResidues p s
    a₀ a₁ a₂ a₃ a₄ hp hcoeff]
  rw [← (finPrimeBlocks p s).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro r _
  rw [zmodPrimeReduction_finPrimeBlocks]

/-- The representative in `Fin (p*s)` lying over a root `x : ZMod p` and
having high coordinate `k : Fin s`. -/
def derivativeRootBlockIndex (p s : Nat) [NeZero p] [NeZero s]
    (x : ZMod p) (k : Fin s) : Fin (p * s) :=
  finPrimeBlocks p s (k, (ZMod.finEquiv p).symm x)

/-- A root-block representative reduces to its indexing root modulo `p`. -/
theorem zmodPrimeReduction_derivativeRootBlockIndex (p s : Nat)
    [NeZero p] [NeZero s] (x : ZMod p) (k : Fin s) :
    zmodPrimeReduction p (p * s)
        (((derivativeRootBlockIndex p s x k).val : Nat) :
          ZMod (p * (p * s))) = x := by
  rw [derivativeRootBlockIndex, zmodPrimeReduction_finPrimeBlocks]
  rw [← zmod_finEquiv_apply]
  exact (ZMod.finEquiv p).apply_symm_apply x

/-- The exact stationary decomposition with an outer sum over distinct
derivative roots and an inner sum over the corresponding residue block. -/
theorem polynomialCompleteSum_eq_sum_derivativeRootBlocks (p s : Nat)
    [Fact p.Prime] [NeZero p] [NeZero s]
    (a₀ a₁ a₂ a₃ a₄ : ZMod (p * (p * s))) (hp : 11 ≤ p)
    (hcoeff :
      zmodPrimeReduction p (p * s) a₀ ≠ 0 ∨
      zmodPrimeReduction p (p * s) a₁ ≠ 0 ∨
      zmodPrimeReduction p (p * s) a₂ ≠ 0 ∨
      zmodPrimeReduction p (p * s) a₃ ≠ 0 ∨
      zmodPrimeReduction p (p * s) a₄ ≠ 0) :
    polynomialCompleteSum a₀ a₁ a₂ a₃ a₄ =
      ∑ x ∈ fifthDerivativeRoots
          (zmodPrimeReduction p (p * s) a₀)
          (zmodPrimeReduction p (p * s) a₁)
          (zmodPrimeReduction p (p * s) a₂)
          (zmodPrimeReduction p (p * s) a₃)
          (zmodPrimeReduction p (p * s) a₄),
        ∑ k : Fin s, (p : Complex) * ZMod.stdAddChar
          (fifthPolynomial a₀ a₁ a₂ a₃ a₄
            (((derivativeRootBlockIndex p s x k).val : Nat) :
              ZMod (p * (p * s)))) := by
  rw [polynomialCompleteSum_eq_derivativeRootBlocks p s
    a₀ a₁ a₂ a₃ a₄ hp hcoeff]
  let roots := fifthDerivativeRoots
    (zmodPrimeReduction p (p * s) a₀)
    (zmodPrimeReduction p (p * s) a₁)
    (zmodPrimeReduction p (p * s) a₂)
    (zmodPrimeReduction p (p * s) a₃)
    (zmodPrimeReduction p (p * s) a₄)
  calc
    (∑ k : Fin s, ∑ r : Fin p,
        if ((r.val : Nat) : ZMod p) ∈ roots
        then (p : Complex) * ZMod.stdAddChar
          (fifthPolynomial a₀ a₁ a₂ a₃ a₄
            (((finPrimeBlocks p s (k, r)).val : Nat) :
              ZMod (p * (p * s))))
        else 0) =
        ∑ k : Fin s, ∑ x ∈ roots,
          (p : Complex) * ZMod.stdAddChar
            (fifthPolynomial a₀ a₁ a₂ a₃ a₄
              (((derivativeRootBlockIndex p s x k).val : Nat) :
                ZMod (p * (p * s)))) := by
      apply Finset.sum_congr rfl
      intro k _
      let block : ZMod p → Complex := fun x ↦
        (p : Complex) * ZMod.stdAddChar
          (fifthPolynomial a₀ a₁ a₂ a₃ a₄
            (((derivativeRootBlockIndex p s x k).val : Nat) :
              ZMod (p * (p * s))))
      have hr (r : Fin p) :
          (ZMod.finEquiv p).symm ((r.val : Nat) : ZMod p) = r := by
        rw [← zmod_finEquiv_apply]
        exact (ZMod.finEquiv p).symm_apply_apply r
      simpa only [block, derivativeRootBlockIndex, hr] using
        sum_fin_ite_mem_zmod p roots block
    _ = ∑ x ∈ roots, ∑ k : Fin s,
          (p : Complex) * ZMod.stdAddChar
            (fifthPolynomial a₀ a₁ a₂ a₃ a₄
              (((derivativeRootBlockIndex p s x k).val : Nat) :
                ZMod (p * (p * s)))) := by
      rw [Finset.sum_comm]

-- These compatibility signatures retain the nonzero instances used uniformly
-- by the surrounding root-block API, even where the definition reduces without one.
attribute [nolint unusedArguments] derivativeRootBlockIndex

end Waring.Analytic
