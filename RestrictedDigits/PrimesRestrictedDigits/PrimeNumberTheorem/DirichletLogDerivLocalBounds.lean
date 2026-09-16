import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletLocalZeroSumReal

/-!
# Real bounds from Dirichlet local-zero expansions

This file packages the two real-part consequences of the nonprincipal local
zero expansion used in `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Theorem 11.3.
The same absolute error coefficient controls both the unselected and selected
forms.
-/

open Complex

namespace PrimesRestrictedDigits

private lemma neg_re_le_neg_add_of_norm_sub_le
    (z w : Complex) {lower error : Real}
    (hNorm : ‖z - w‖ ≤ error) (hLower : lower ≤ w.re) :
    (-z).re ≤ -lower + error := by
  have hErrorLower : -error ≤ (z - w).re := by
    exact neg_le_of_abs_le ((Complex.abs_re_le_norm (z - w)).trans hNorm)
  have hIdentity : (-z).re = -w.re - (z - w).re := by
    simp only [Complex.neg_re, Complex.sub_re]
    ring
  rw [hIdentity]
  linarith

/-- One absolute local-expansion coefficient controls both standard upper
bounds for the negative real logarithmic derivative of a nonprincipal
Dirichlet L-function. The second form retains the contribution of a selected
same-height zero. -/
theorem exists_nonprincipal_neg_re_logDeriv_local_bounds :
    ∃ C : Real, 0 < C ∧
      (∀ {q : Nat} [NeZero q]
          (chi : DirichletCharacter Complex q),
          chi ≠ 1 →
          ∀ t sigma : Real, 1 < sigma → sigma ≤ 2 →
            (-logDeriv chi.LFunction
              ((sigma : Complex) + Complex.I * (t : Complex))).re ≤
              C * Real.log ((q : Real) * (|t| + 4))) ∧
      ∀ {q : Nat} [NeZero q]
        (chi : DirichletCharacter Complex q),
        chi ≠ 1 →
        ∀ t beta sigma : Real,
          5 / 6 ≤ beta →
          chi.LFunction
            ((beta : Complex) + Complex.I * (t : Complex)) = 0 →
          1 < sigma → sigma ≤ 2 →
          (-logDeriv chi.LFunction
            ((sigma : Complex) + Complex.I * (t : Complex))).re ≤
            -(1 / (sigma - beta)) +
              C * Real.log ((q : Real) * (|t| + 4)) := by
  obtain ⟨C, hCPos, hLocal⟩ :=
    dirichletLFunction_logDeriv_localZeroSum_bound
  refine ⟨C, hCPos, ?_, ?_⟩
  · intro q _ chi hchi t sigma hSigma hSigmaUpper
    have hSigmaLower : 5 / 6 ≤ sigma := by linarith
    have hsNonzero :
        chi.LFunction
          ((sigma : Complex) + Complex.I * (t : Complex)) ≠ 0 := by
      apply DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (.inl hchi)
      simpa using hSigma.le
    have hError := hLocal chi hchi t sigma hSigmaLower hSigmaUpper hsNonzero
    have hSum := dirichletLFunctionLocalZeroSum_re_nonneg
      hchi (t := t) (sigma := sigma) hSigma
    simpa using neg_re_le_neg_add_of_norm_sub_le
      (logDeriv chi.LFunction
        ((sigma : Complex) + Complex.I * (t : Complex)))
      (dirichletLFunctionLocalZeroSum chi t
        ((sigma : Complex) + Complex.I * (t : Complex))) hError hSum
  · intro q _ chi hchi t beta sigma hBeta hZero hSigma hSigmaUpper
    have hSigmaLower : 5 / 6 ≤ sigma := by linarith
    have hsNonzero :
        chi.LFunction
          ((sigma : Complex) + Complex.I * (t : Complex)) ≠ 0 := by
      apply DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (.inl hchi)
      simpa using hSigma.le
    have hError := hLocal chi hchi t sigma hSigmaLower hSigmaUpper hsNonzero
    have hSelected := one_div_sub_le_dirichletLFunctionLocalZeroSum_re
      hchi (t := t) (beta := beta) (sigma := sigma) hBeta hZero hSigma
    exact neg_re_le_neg_add_of_norm_sub_le
      (logDeriv chi.LFunction
        ((sigma : Complex) + Complex.I * (t : Complex)))
      (dirichletLFunctionLocalZeroSum chi t
        ((sigma : Complex) + Complex.I * (t : Complex))) hError hSelected

end PrimesRestrictedDigits
