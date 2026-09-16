import PrimesRestrictedDigits.PrimeNumberTheorem.TwistedPerronRemainder
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronEdgeBounds

/-!
# Raw Dirichlet Perron error composition

This module combines the corrected weak-sum Perron remainder with the exact
principal and nonprincipal contour-edge estimates. The right-line coefficient
is shared by both branches, while each branch retains its own edge constants.
-/

namespace PrimesRestrictedDigits

/-- One Perron remainder coefficient simultaneously gives the exact raw
nonprincipal and principal error bounds. -/
theorem DirichletPerronLogDerivBounds.exists_norm_dirichletVonMangoldtSum_branches_le
    {c C : Real} (h : DirichletPerronLogDerivBounds c C) :
    ∃ P : Real, 0 < P ∧
      (∀ {q : Nat} [NeZero q]
          (chi : DirichletCharacter Complex q),
        IsDecimalSmooth q → chi ≠ 1 →
        ∀ x T : Real,
          4 ≤ x → 2 ≤ T → T ≤ x →
          norm (dirichletVonMangoldtSum chi x) ≤
            P * x * Real.log x ^ 2 / T +
              (1 / (2 * Real.pi)) *
                (6 * C * x / T *
                    (Real.log ((q : Real) * (T + 4)) /
                        Real.log x + c / 5) +
                  8 * C * x ^ dirichletPerronLeftLine c q T *
                    Real.log ((q : Real) * (T + 4)) ^ 2)) ∧
      (∀ {q : Nat} [NeZero q],
        IsDecimalSmooth q →
        ∀ x T : Real,
          4 ≤ x → 2 ≤ T → T ≤ x →
          norm (dirichletVonMangoldtSum
              (1 : DirichletCharacter Complex q) x - (x : Complex)) ≤
            P * x * Real.log x ^ 2 / T +
              (1 / (2 * Real.pi)) *
                (6 * (C + 8 * Real.log 5) * x / T *
                    (Real.log ((q : Real) * (T + 4)) /
                        Real.log x + c / 5) +
                  (8 * (C + 8 * Real.log 5) + 20 / c) *
                    x ^ dirichletPerronLeftLine c q T *
                      Real.log ((q : Real) * (T + 4)) ^ 2)) := by
  obtain ⟨P, hP, hPerron⟩ :=
    exists_norm_dirichletVonMangoldtSum_sub_integral_rightLine_le
  refine ⟨P, hP, ?_, ?_⟩
  · intro q inst chi hq hchi x T hx hT hTx
    have hRight := hPerron chi x T hx hT hTx
    have hEdge :=
      h.norm_nonprincipalDirichletPerronIntegral_le chi hq hchi hx hT
    calc
      norm (dirichletVonMangoldtSum chi x) =
          norm ((dirichletVonMangoldtSum chi x -
              dirichletPerronIntegral chi x
                (1 + 1 / Real.log x) T) +
            dirichletPerronIntegral chi x
              (1 + 1 / Real.log x) T) := by
        congr 1
        ring
      _ ≤ norm (dirichletVonMangoldtSum chi x -
              dirichletPerronIntegral chi x
                (1 + 1 / Real.log x) T) +
            norm (dirichletPerronIntegral chi x
              (1 + 1 / Real.log x) T) := norm_add_le _ _
      _ ≤ _ := add_le_add hRight hEdge
  · intro q inst hq x T hx hT hTx
    have hRight := hPerron
      (1 : DirichletCharacter Complex q) x T hx hT hTx
    have hEdge :=
      h.norm_principalDirichletPerronIntegral_sub_self_le hq hx hT
    calc
      norm (dirichletVonMangoldtSum
          (1 : DirichletCharacter Complex q) x - (x : Complex)) =
          norm ((dirichletVonMangoldtSum
              (1 : DirichletCharacter Complex q) x -
                dirichletPerronIntegral
                  (1 : DirichletCharacter Complex q) x
                    (1 + 1 / Real.log x) T) +
            (dirichletPerronIntegral
                (1 : DirichletCharacter Complex q) x
                  (1 + 1 / Real.log x) T - (x : Complex))) := by
        congr 1
        ring
      _ ≤ norm (dirichletVonMangoldtSum
              (1 : DirichletCharacter Complex q) x -
                dirichletPerronIntegral
                  (1 : DirichletCharacter Complex q) x
                    (1 + 1 / Real.log x) T) +
            norm (dirichletPerronIntegral
                (1 : DirichletCharacter Complex q) x
                  (1 + 1 / Real.log x) T - (x : Complex)) :=
        norm_add_le _ _
      _ ≤ _ := add_le_add hRight hEdge

end PrimesRestrictedDigits
