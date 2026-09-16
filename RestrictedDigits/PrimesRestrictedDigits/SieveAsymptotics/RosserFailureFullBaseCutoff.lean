import PrimesRestrictedDigits.SieveAsymptotics.RosserFailureFullRecurrenceShell
import PrimesRestrictedDigits.SieveAsymptotics.RosserCutoffRecurrence

/-!
# Complete upper base-cutoff split

This is the full-sum form of Iwaniec's Eq. (4.6). Above the cubic-root base, the positive-rank
shell is empty and only the rank-zero layer at the outer cutoff remains.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The complete upper correction splits at the cubic-root base cutoff. -/
theorem upperRosserFailureSum_eq_rankZero_add_baseCutoff
    (P : Finset Nat) (nu : Nat → Real) (level z : Real)
    (hprime : ∀ p ∈ P, p.Prime) (hlevel : 0 <= level)
    (hbase : iwaniecBaseCutoff level <= z) :
    upperRosserFailureSum P nu level z =
      upperRosserFailureSumAtRank P nu level z 0 +
        upperRosserFailureSum P nu level (iwaniecBaseCutoff level) := by
  have hbaseZero : upperRosserFailureSumAtRank P nu level
      (iwaniecBaseCutoff level) 0 = 0 := by
    apply upperRosserFailureSumAtRank_eq_zero_of_cutoffPow_le
      P nu level (iwaniecBaseCutoff level) 0 hprime
    simpa using (iwaniecBaseCutoff_pow_three hlevel).le
  have hfilter : P.filter (fun p : Nat =>
    iwaniecBaseCutoff level <= (p : Real) ∧ (p : Real) < z ∧
        (p : Real) ^ 3 < level) = ∅ := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · intro hp
      have hpPrime := hprime p hp.1
      have hpNonneg : (0 : Real) <= p := by
        exact_mod_cast hpPrime.pos.le
      have hcube : level <= (p : Real) ^ (3 : Nat) :=
        (iwaniecBaseCutoff_le_iff_cube_le hlevel hpNonneg).mp hp.2.1
      exact (not_lt_of_ge hcube hp.2.2.2).elim
    · intro hp
      have hfalse : False := by
        simp at hp
      exact hfalse.elim
  rw [upperRosserFailureSum_eq_cutoff_add_sum_lower_full_gated
    P nu level (iwaniecBaseCutoff level) z hprime hbase]
  rw [hbaseZero, hfilter, Finset.sum_empty]
  ring

end PrimesRestrictedDigits
