import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6NativeLabelBranchPruning
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Candidate-label finite overapproximation

The finite candidate set gives necessary conditions for label membership, not sufficient
conditions for target nonemptiness.
-/

open Set

namespace PrimesRestrictedDigits

noncomputable section

def i6D731Sigma00000 : Fin 5 → Bool := ![false, false, false, false, false]
def i6D731Sigma00010 : Fin 5 → Bool := ![false, false, false, true, false]
def i6D731Sigma10010 : Fin 5 → Bool := ![true, false, false, true, false]
def i6D731Sigma11010 : Fin 5 → Bool := ![true, true, false, true, false]
def i6D731Sigma11110 : Fin 5 → Bool := ![true, true, true, true, false]
def i6D731Sigma11111 : Fin 5 → Bool := ![true, true, true, true, true]

def i6D731CandidateLabels : Finset i6D691Label :=
  {(false, ((2 : Fin 3), i6D731Sigma00000)),
   (false, ((2 : Fin 3), i6D731Sigma00010)),
   (true, ((0 : Fin 3), i6D731Sigma11111)),
   (true, ((1 : Fin 3), i6D731Sigma11110)),
   (true, ((1 : Fin 3), i6D731Sigma11111)),
   (true, ((2 : Fin 3), i6D731Sigma00010)),
   (true, ((2 : Fin 3), i6D731Sigma10010)),
   (true, ((2 : Fin 3), i6D731Sigma11010)),
   (true, ((2 : Fin 3), i6D731Sigma11110)),
   (true, ((2 : Fin 3), i6D731Sigma11111))}

private theorem sigma_eq_iff_values (sigma tau : Fin 5 → Bool) :
    sigma = tau ↔
      (sigma 0 = tau 0 ∧ sigma 1 = tau 1 ∧ sigma 2 = tau 2 ∧
        sigma 3 = tau 3 ∧ sigma 4 = tau 4) := by
  constructor
  · intro h
    subst tau
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    funext i
    fin_cases i <;> simp_all

theorem i6D731_active_mem_candidates
    (label : i6D691Label)
    (h : sectionSixFirstLowBelowI6D731BranchPrunedLabel label) :
    label ∈ i6D731CandidateLabels := by
  rcases label with ⟨rho, b, sigma⟩
  rcases h with ⟨hactive, hrho, hb0, hb1⟩
  cases rho <;> fin_cases b
  all_goals
    have h0 := hactive.1.1
    have h1 := hactive.1.2.1
    have h2 := hactive.1.2.2.1
    have h3 := hactive.1.2.2.2
    have h4 := hactive.2
    simp only at h0 h1 h2 h3 h4
    cases hs0 : sigma (0 : Fin 5)
    <;> cases hs1 : sigma (1 : Fin 5)
    <;> cases hs2 : sigma (2 : Fin 5)
    <;> cases hs3 : sigma (3 : Fin 5)
    <;> cases hs4 : sigma (4 : Fin 5)
    <;> simp_all [i6D731CandidateLabels, i6D731Sigma00000,
      i6D731Sigma00010, i6D731Sigma10010, i6D731Sigma11010,
      i6D731Sigma11110, i6D731Sigma11111, Finset.mem_insert,
      Finset.mem_singleton, sigma_eq_iff_values]

end

end PrimesRestrictedDigits
