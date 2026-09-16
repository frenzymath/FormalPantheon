import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Rat.Cast.Order

/-!
# Rational approximation bands for the lattice estimate

This file defines the repaired `F(Q,E)` carrier from published Proposition 13.3 and Lemma
14.2. The zero error scale means exact equality.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The source's factor-ten error band, repaired at `E=0`. -/
def latticeRationalErrorInBand (X E nu : Real) : Prop :=
  (E = 0 ∧ nu = 0) ∨
    (0 < E ∧ E / X / 10 < |nu| ∧ |nu| <= E / X)

theorem latticeRationalErrorInBand_zero_iff {X nu : Real} :
    latticeRationalErrorInBand X 0 nu ↔ nu = 0 := by
  simp [latticeRationalErrorInBand]

theorem latticeRationalErrorInBand_of_pos_iff
    {X E nu : Real} (hE : 0 < E) :
    latticeRationalErrorInBand X E nu ↔
      E / X / 10 < |nu| ∧ |nu| <= E / X := by
  simp [latticeRationalErrorInBand, hE, hE.ne']

theorem latticeRationalErrorInBand_abs_le
    {X E nu : Real} (h : latticeRationalErrorInBand X E nu) :
    |nu| <= E / X := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hE, _, hupper⟩
  · simp
  · exact hupper

/-- Frequencies with a canonically reduced rational approximation in the
source denominator and error bands. -/
noncomputable def latticeRationalApproximationBand
    {X : Nat} (Q E : Real) : Finset (Fin X) := by
  classical
  exact Finset.univ.filter fun a =>
    ∃ r : Rat,
      (r.den : Real) <= Q ∧
      Q < 10 * (r.den : Real) ∧
      latticeRationalErrorInBand (X : Real) E
        (((a : Nat) : Real) / (X : Real) - (r : Real))

/-- The canonical rational carrier is exactly the source's signed,
positive-denominator, coprime formulation. -/
theorem mem_latticeRationalApproximationBand_iff
    {X : Nat} {a : Fin X} {Q E : Real} :
    a ∈ latticeRationalApproximationBand Q E ↔
      ∃ b : Int, ∃ q : Nat,
        0 < q ∧
        (q : Real) <= Q ∧
        Q < 10 * (q : Real) ∧
        b.natAbs.Coprime q ∧
        latticeRationalErrorInBand (X : Real) E
          (((a : Nat) : Real) / (X : Real) -
            (b : Real) / (q : Real)) := by
  classical
  rw [latticeRationalApproximationBand, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, hrUpper, hrLower, herror⟩
    refine ⟨r.num, r.den, r.den_pos, hrUpper, hrLower, r.reduced, ?_⟩
    simpa only [Rat.cast_def] using herror
  · rintro ⟨b, q, hq, hqUpper, hqLower, hcoprime, herror⟩
    let r : Rat := (b : Rat) / (q : Rat)
    have hqInt : (0 : Int) < (q : Int) := by exact_mod_cast hq
    have hcoprimeInt : b.natAbs.Coprime (q : Int).natAbs := by
      simpa using hcoprime
    have hdenInt : (r.den : Int) = (q : Int) := by
      dsimp only [r]
      exact Rat.den_div_eq_of_coprime hqInt hcoprimeInt
    have hden : r.den = q := by exact_mod_cast hdenInt
    have hcast : (r : Real) = (b : Real) / (q : Real) := by
      dsimp only [r]
      rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    refine ⟨r, ?_, ?_, ?_⟩
    · simpa only [hden] using hqUpper
    · simpa only [hden] using hqLower
    · simpa only [hcast] using herror

end

end PrimesRestrictedDigits
