import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletCharacterAverage
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronOptimizedError

/-!
# Exponential progression error for decimal-smooth levels

This inserts the no-exceptional-zero character estimates into the exact
average, as in `MONTGOMERY-VAUGHAN-MNT-I`, Corollary 11.17, pp. 379--380.
-/

namespace PrimesRestrictedDigits

/-- A common exponential remainder for weak von Mangoldt sums in every
coprime residue class at a decimal-smooth level in the source's modulus range. -/
theorem exists_abs_vonMangoldtProgressionSum_sub_main_exp_sqrt_log_le :
    ∃ d M L0 : Real,
      0 < d ∧ 0 < M ∧ Real.log 4 <= L0 ∧
      ∀ q : Nat,
        0 < q -> IsDecimalSmooth q ->
        ∀ a : Nat,
          Nat.Coprime a q ->
          ∀ x : Real,
            Real.exp L0 <= x ->
            (q : Real) <=
              Real.exp (2 * d * Real.sqrt (Real.log x)) ->
            abs (vonMangoldtProgressionSum q a x -
              x / (q.totient : Real)) <=
                M * x /
                  Real.exp (d * Real.sqrt (Real.log x)) := by
  obtain ⟨d, M, L0, hd, hM, hL0, hNonprincipal, hPrincipal⟩ :=
    exists_norm_dirichletVonMangoldtSum_exp_sqrt_log_branches_le
  refine ⟨d, M, L0, hd, hM, hL0, ?_⟩
  intro q hq hSmooth a ha x hxCutoff hqHeight
  letI : NeZero q := ⟨hq.ne'⟩
  let E : Real :=
    M * x / Real.exp (d * Real.sqrt (Real.log x))
  have hxPos : 0 < x := (Real.exp_pos L0).trans_le hxCutoff
  have hE : 0 <= E := by
    dsimp [E]
    positivity
  apply abs_vonMangoldtProgressionSum_sub_main_le_of_character_bounds
    ha x E hE
  · intro chi hchi
    dsimp [E]
    exact hNonprincipal chi hSmooth hchi x hxCutoff hqHeight
  · dsimp [E]
    exact hPrincipal hSmooth x hxCutoff hqHeight

end PrimesRestrictedDigits
