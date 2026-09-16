import Mathlib.NumberTheory.DirichletCharacter.Bounds
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletResidueClass
import PrimesRestrictedDigits.PrimeNumberTheorem.TwistedPerron

/-!
# Quantitative finite character averaging

This records Montgomery--Vaughan Eq. (11.22), p. 377, in the project's weak
floor-cutoff convention and proves that common principal/nonprincipal twisted
errors pass through the character average with no totient loss.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

open Finset

/-- The weak von Mangoldt sum in one natural residue class. -/
noncomputable def vonMangoldtProgressionSum
    (q a : Nat) (x : Real) : Real :=
  ∑ n ∈ (Ioc 0 ⌊x⌋₊).filter (fun n => n ≡ a [MOD q]),
    ArithmeticFunction.vonMangoldt n

/-- Exact finite character orthogonality for the weak progression sum. -/
theorem vonMangoldtProgressionSum_eq_character_average
    {q a : Nat} [NeZero q] (ha : Nat.Coprime a q) (x : Real) :
    (vonMangoldtProgressionSum q a x : Complex) =
      (q.totient : Complex)⁻¹ *
        ∑ chi : DirichletCharacter Complex q,
          chi ((a : ZMod q)⁻¹) *
            dirichletVonMangoldtSum chi x := by
  simpa only [vonMangoldtProgressionSum, dirichletVonMangoldtSum] using
    (sum_vonMangoldt_modEq_eq_character_average
      (s := Ioc 0 ⌊x⌋₊) ha)

/-- Common principal and nonprincipal twisted bounds pass through the exact
character average without enlarging their coefficient. -/
theorem abs_vonMangoldtProgressionSum_sub_main_le_of_character_bounds
    {q a : Nat} [NeZero q] (ha : Nat.Coprime a q)
    (x E : Real) (_hE : 0 <= E)
    (hNonprincipal :
      ∀ chi : DirichletCharacter Complex q,
        chi ≠ 1 -> norm (dirichletVonMangoldtSum chi x) <= E)
    (hPrincipal :
      norm (dirichletVonMangoldtSum
        (1 : DirichletCharacter Complex q) x - (x : Complex)) <= E) :
    abs (vonMangoldtProgressionSum q a x -
      x / (q.totient : Real)) <= E := by
  classical
  let u : ZMod q := (a : ZMod q)⁻¹
  let error (chi : DirichletCharacter Complex q) : Complex :=
    dirichletVonMangoldtSum chi x -
      if chi = 1 then (x : Complex) else 0
  have huUnit : IsUnit u := by
    refine ⟨(ZMod.unitOfCoprime a ha)⁻¹, ?_⟩
    exact (ZMod.inv_coe_unit (ZMod.unitOfCoprime a ha)).symm
  have hMain :
      ∑ chi : DirichletCharacter Complex q,
          chi u * (if chi = 1 then (x : Complex) else 0) =
        (x : Complex) := by
    simp [MulChar.one_apply huUnit]
  have hError :
      ∀ chi : DirichletCharacter Complex q, norm (error chi) <= E := by
    intro chi
    by_cases hchi : chi = 1
    · subst chi
      simpa [error] using hPrincipal
    · simpa [error, hchi] using hNonprincipal chi hchi
  have hTerm :
      ∀ chi : DirichletCharacter Complex q,
        norm (chi u * error chi) <= E := by
    intro chi
    rw [norm_mul]
    calc
      norm (chi u) * norm (error chi) <= 1 * norm (error chi) :=
        mul_le_mul_of_nonneg_right
          (DirichletCharacter.norm_le_one chi u) (norm_nonneg _)
      _ <= 1 * E :=
        mul_le_mul_of_nonneg_left (hError chi) (by norm_num)
      _ = E := one_mul E
  have hCard :
      Fintype.card (DirichletCharacter Complex q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity
      Complex q
  have hSum :
      norm (∑ chi : DirichletCharacter Complex q, chi u * error chi) <=
        (q.totient : Real) * E := by
    calc
      norm (∑ chi : DirichletCharacter Complex q, chi u * error chi) <=
          ∑ chi : DirichletCharacter Complex q,
            norm (chi u * error chi) := norm_sum_le _ _
      _ <= ∑ _chi : DirichletCharacter Complex q, E := by
        exact Finset.sum_le_sum fun chi _ => hTerm chi
      _ = (q.totient : Real) * E := by simp [hCard]
  have hAverage :
      (vonMangoldtProgressionSum q a x : Complex) =
        (q.totient : Complex)⁻¹ *
          ∑ chi : DirichletCharacter Complex q,
            chi u * dirichletVonMangoldtSum chi x := by
    simpa only [u] using
      vonMangoldtProgressionSum_eq_character_average ha x
  have hPhiPosNat : 0 < q.totient :=
    Nat.totient_pos.mpr (NeZero.pos q)
  have hPhiPos : (0 : Real) < q.totient := by
    exact_mod_cast hPhiPosNat
  have hMainCast :
      ((x / (q.totient : Real) : Real) : Complex) =
        (q.totient : Complex)⁻¹ * (x : Complex) := by
    push_cast
    field_simp [hPhiPos.ne']
  have hErrorIdentity :
      ((vonMangoldtProgressionSum q a x -
          x / (q.totient : Real) : Real) : Complex) =
        (q.totient : Complex)⁻¹ *
          ∑ chi : DirichletCharacter Complex q, chi u * error chi := by
    rw [Complex.ofReal_sub, hAverage, hMainCast]
    calc
      (q.totient : Complex)⁻¹ *
            ∑ chi : DirichletCharacter Complex q,
              chi u * dirichletVonMangoldtSum chi x -
          (q.totient : Complex)⁻¹ * (x : Complex) =
          (q.totient : Complex)⁻¹ *
            ((∑ chi : DirichletCharacter Complex q,
                chi u * dirichletVonMangoldtSum chi x) - (x : Complex)) := by
        ring
      _ = (q.totient : Complex)⁻¹ *
          ((∑ chi : DirichletCharacter Complex q,
              chi u * dirichletVonMangoldtSum chi x) -
            ∑ chi : DirichletCharacter Complex q,
              chi u * (if chi = 1 then (x : Complex) else 0)) := by
        rw [hMain]
      _ = (q.totient : Complex)⁻¹ *
          ∑ chi : DirichletCharacter Complex q, chi u * error chi := by
        congr 1
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro chi hchi
        dsimp [error]
        ring
  have hNorm :
      norm (((vonMangoldtProgressionSum q a x -
          x / (q.totient : Real) : Real) : Complex)) <= E := by
    rw [hErrorIdentity, norm_mul, norm_inv, Complex.norm_natCast]
    calc
      ((q.totient : Real)⁻¹) *
          norm (∑ chi : DirichletCharacter Complex q,
            chi u * error chi) <=
          ((q.totient : Real)⁻¹) * ((q.totient : Real) * E) :=
        mul_le_mul_of_nonneg_left hSum (inv_nonneg.mpr hPhiPos.le)
      _ = E := by field_simp [hPhiPos.ne']
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hNorm

end PrimesRestrictedDigits
