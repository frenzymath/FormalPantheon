import PrimesRestrictedDigits.SieveAsymptotics.TypeIIAffineHalfspaces
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Weak affine presentation of the ordered exponent simplex

The ordered sum-one simplex used by Proposition 7.2 is presented by finite weak affine walls.
This is a reusable structural constructor for the terminal-V target path; it contains no
counting estimate.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem typeIIExponentSimplexPresentation_value_single
    {d : Nat} (i : Fin d) (a : Real) (x : Fin d -> Real) :
    typeIIAffineValue (Pi.single i a) x = a * x i := by
  classical
  simp [typeIIAffineValue, Pi.single_apply]

private theorem typeIIExponentSimplexPresentation_value_sub_single
    {d : Nat} (i j : Fin d) (x : Fin d -> Real) :
    typeIIAffineValue (Pi.single i 1 - Pi.single j 1) x = x i - x j := by
  rw [typeIIAffineValue]
  simp_rw [Pi.sub_apply, sub_mul]
  rw [Finset.sum_sub_distrib]
  simp [Pi.single_apply]

private def typeIIExponentSimplexPresentation_sum_normal {d : Nat} :
    Fin 2 -> Fin d -> Real :=
  ![fun _ => (1 : Real), fun _ => (-1 : Real)]

private theorem typeIIExponentSimplexPresentation_value_sum_normal
    {d : Nat} (c : Fin 2) (x : Fin d -> Real) :
    typeIIAffineValue (typeIIExponentSimplexPresentation_sum_normal c) x =
      if c = 0 then ∑ i, x i else -(∑ i, x i) := by
  fin_cases c <;>
    simp [typeIIExponentSimplexPresentation_sum_normal, typeIIAffineValue]

private def typeIIExponentSimplexPresentation_sum_bound : Fin 2 -> Real :=
  ![(1 : Real), (-1 : Real)]

/-- A finite weak affine presentation of the ordered sum-one simplex. -/
noncomputable def typeIIExponentSimplexPresentation
    {k : Nat} (eta : Real) :
    TypeIIAffineHalfspacePresentation
      (typeIIExponentSimplex (ell := k + 1) eta) where
  constraintCount := (k + 1) + (k + 2)
  normal := Fin.append
    (fun i => Pi.single i (-1 : Real))
    (Fin.append
      (fun i : Fin k => Pi.single i.castSucc 1 - Pi.single i.succ 1)
      typeIIExponentSimplexPresentation_sum_normal)
  bound := Fin.append (fun _ => -eta)
    (Fin.append (fun _ => 0)
      typeIIExponentSimplexPresentation_sum_bound)
  mem_iff := by
    intro x
    rw [Fin.forall_fin_add]
    constructor
    · rintro ⟨hlower, hmonotone, hsum⟩
      refine ⟨?_, ?_⟩
      · intro i
        simp only [Fin.append_left,
          typeIIExponentSimplexPresentation_value_single, neg_one_mul]
        linarith [hlower i]
      · rw [Fin.forall_fin_add]
        refine ⟨?_, ?_⟩
        · intro i
          simp only [Fin.append_right, Fin.append_left,
            typeIIExponentSimplexPresentation_value_sub_single]
          linarith [(Fin.monotone_iff_le_succ.mp hmonotone) i]
        · intro c
          fin_cases c <;>
            simp [Fin.append_right,
              typeIIExponentSimplexPresentation_value_sum_normal,
              typeIIExponentSimplexPresentation_sum_bound, hsum]
    · rintro ⟨hlower, htail⟩
      rw [Fin.forall_fin_add] at htail
      refine ⟨?_, ?_, ?_⟩
      · intro i
        have hi := hlower i
        simp only [Fin.append_left,
          typeIIExponentSimplexPresentation_value_single,
          neg_one_mul] at hi
        linarith
      · apply Fin.monotone_iff_le_succ.mpr
        intro i
        have hi := htail.1 i
        simp only [Fin.append_right, Fin.append_left,
          typeIIExponentSimplexPresentation_value_sub_single] at hi
        linarith
      · have hupper := htail.2 (0 : Fin 2)
        have hlowerSum := htail.2 (1 : Fin 2)
        simp [Fin.append_right,
          typeIIExponentSimplexPresentation_value_sum_normal,
          typeIIExponentSimplexPresentation_sum_bound] at hupper
        norm_num [Fin.append_right,
          typeIIExponentSimplexPresentation_value_sum_normal,
          typeIIExponentSimplexPresentation_sum_bound] at hlowerSum
        linarith

/-- Raw-coordinate reuse of the successor-shaped simplex presentation. -/
noncomputable def typeIIExponentSimplexPresentationRaw
    {d : Nat} (eta : Real) (hd : 0 < d) :
    TypeIIAffineHalfspacePresentation
      (typeIIExponentSimplex (ell := d) eta) :=
  (Nat.sub_one_add_one_eq_of_pos hd) ▸
    typeIIExponentSimplexPresentation (k := d - 1) eta

end

end PrimesRestrictedDigits
