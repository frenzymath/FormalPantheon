import Waring.Analytic.FourierCoefficientSum

/-!
# Diophantine minimum sums

This file proves the rational-grid reciprocal-distance estimate used in the
last stage of Chen's Lemma 9 [CHEN1964-EN, p. 1560].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The minimum of the trivial length bound and the reciprocal
least-residue bound, with the zero residue assigned the trivial bound. -/
noncomputable def diophantineMinWeight (q P : Nat) [NeZero q]
    (h : ZMod q) : Real :=
  if h = 0 then P else min (P : Real) (leastResidueWeight q h)

/-- The zero-safe reciprocal-distance weight is nonnegative. -/
theorem diophantineMinWeight_nonneg (q P : Nat) [NeZero q]
    (h : ZMod q) : 0 ≤ diophantineMinWeight q P h := by
  by_cases hh : h = 0
  · simp [diophantineMinWeight, hh]
  · simp only [diophantineMinWeight, hh, ↓reduceIte]
    exact le_min (by positivity) (by simp [leastResidueWeight]; positivity)

/-- One complete residue system costs at most its zero term plus the paired
harmonic least-residue sum. -/
theorem sum_diophantineMinWeight_le (q P : Nat) [NeZero q] :
    (∑ h : ZMod q, diophantineMinWeight q P h) ≤
      (P : Real) + q * Real.log q := by
  let residues : Finset (ZMod q) := Finset.univ
  have hzero : (0 : ZMod q) ∈ residues := by simp [residues]
  rw [← Finset.sum_erase_add residues (diophantineMinWeight q P) hzero]
  have hnonzero :
      (∑ h ∈ residues.erase 0, diophantineMinWeight q P h) ≤
        ∑ h ∈ residues.erase 0, leastResidueWeight q h := by
    apply Finset.sum_le_sum
    intro h hh
    rw [diophantineMinWeight, if_neg (Finset.ne_of_mem_erase hh)]
    exact min_le_right _ _
  have hweightZero : leastResidueWeight q (0 : ZMod q) = 0 := by
    simp [leastResidueWeight]
  have hweightSplit :
      (∑ h ∈ residues.erase 0, leastResidueWeight q h) =
        ∑ h : ZMod q, leastResidueWeight q h := by
    rw [← Finset.sum_erase_add residues (leastResidueWeight q) hzero]
    simp only [hweightZero, add_zero]
  calc
    (∑ h ∈ residues.erase 0, diophantineMinWeight q P h) +
          diophantineMinWeight q P 0 ≤
        (∑ h ∈ residues.erase 0, leastResidueWeight q h) + P := by
      gcongr
      simp [diophantineMinWeight]
    _ = (P : Real) + ∑ h : ZMod q, leastResidueWeight q h := by
      rw [hweightSplit]
      ring
    _ ≤ (P : Real) + q * Real.log q := by
      gcongr
      exact sum_leastResidueWeight_le_log q

/-- A residue occurs at most `X / q + 1` times among `0,...,X-1`. -/
theorem card_range_zmod_fiber_le (q X : Nat) [NeZero q] (h : ZMod q) :
    ((Finset.range X).filter (fun i : Nat ↦ (i : ZMod q) = h)).card ≤ X / q + 1 := by
  let fiber := (Finset.range X).filter (fun i : Nat ↦ (i : ZMod q) = h)
  have hinj : fiber.card ≤ (Finset.range (X / q + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun i ↦ i / q)
    · intro i hi
      have hiData : i < X ∧ (i : ZMod q) = h := by
        simpa [fiber] using hi
      simpa only [Finset.mem_coe, Finset.mem_range, Nat.succ_eq_add_one] using
        Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt hiData.1))
    · intro i hi j hj hij
      have hcast : (i : ZMod q) = (j : ZMod q) := by
        have hi' : (i : ZMod q) = h := (by simpa [fiber] using hi :
          i < X ∧ (i : ZMod q) = h).2
        have hj' : (j : ZMod q) = h := (by simpa [fiber] using hj :
          j < X ∧ (j : ZMod q) = h).2
        exact hi'.trans hj'.symm
      have hmod : i % q = j % q :=
        (ZMod.natCast_eq_natCast_iff' i j q).mp hcast
      change i / q = j / q at hij
      calc
        i = i % q + q * (i / q) := (Nat.mod_add_div i q).symm
        _ = j % q + q * (j / q) := by rw [hmod, hij]
        _ = j := Nat.mod_add_div j q
  simpa [fiber] using hinj

/-- Multiplication by a unit and repetition over an initial interval cost at
most the maximal residue-fiber cardinality times one complete residue sum. -/
theorem sum_range_diophantineMinWeight_mul_le
    (q P X : Nat) [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    (∑ i ∈ Finset.range X,
        diophantineMinWeight q P (a * (i : ZMod q))) ≤
      ((X / q + 1 : Nat) : Real) *
        ((P : Real) + q * Real.log q) := by
  let residue : Nat → ZMod q := fun i ↦ i
  have hmaps : ∀ i ∈ Finset.range X,
      residue i ∈ (Finset.univ : Finset (ZMod q)) := by simp
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps
    (fun h ↦ diophantineMinWeight q P (a * h))]
  have hsum :
      (∑ h : ZMod q,
          ∑ _i ∈ Finset.range X with residue _i = h,
            diophantineMinWeight q P (a * h)) ≤
        ∑ h : ZMod q, ((X / q + 1 : Nat) : Real) *
          diophantineMinWeight q P (a * h) := by
    apply Finset.sum_le_sum
    intro h hh
    simp only [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast card_range_zmod_fiber_le q X h
    · exact diophantineMinWeight_nonneg q P (a * h)
  calc
    (∑ h : ZMod q,
        ∑ _i ∈ Finset.range X with residue _i = h,
          diophantineMinWeight q P (a * h)) ≤
        ∑ h : ZMod q, ((X / q + 1 : Nat) : Real) *
          diophantineMinWeight q P (a * h) := hsum
    _ = ((X / q + 1 : Nat) : Real) *
          ∑ h : ZMod q, diophantineMinWeight q P (a * h) := by
      rw [Finset.mul_sum]
    _ = ((X / q + 1 : Nat) : Real) *
          ∑ h : ZMod q, diophantineMinWeight q P h := by
      obtain ⟨u, rfl⟩ := ha
      congr 1
      simpa using (Equiv.sum_comp u.mulLeft (diophantineMinWeight q P))
    _ ≤ ((X / q + 1 : Nat) : Real) *
          ((P : Real) + q * Real.log q) := by
      gcongr
      exact sum_diophantineMinWeight_le q P

-- The nonzero modulus is retained in this fiber-bound signature so it remains
-- interchangeable with the surrounding `ZMod q` counting API.
attribute [nolint unusedArguments] card_range_zmod_fiber_le

end Waring.Analytic
