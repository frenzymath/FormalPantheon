import BoundedGaps.Maynard.SimplexQuadraticMoments
import BoundedGaps.Maynard.SmallKCertificate
import BoundedGaps.Maynard.SmallKCompositionTable

/-!
# Finite composition regrouping for Maynard moments

The multinomial moment module leaves a composition sum indexed by
`Finset.piAntidiag`.  This file proves its first-coordinate recurrence by an
explicit finite bijection, evaluates the resulting rational dynamic program,
and checks the archived `smallKGFormula` rows for dimensions 105 and 104.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

set_option maxRecDepth 100000

def compositionWeight (k : ℕ) (q : Fin k → ℕ) : ℚ :=
  ∏ i, (Nat.factorial (2 * q i) : ℚ) / Nat.factorial (q i)

def compositionMoment (k c : ℕ) : ℚ :=
  ∑ q ∈ (Finset.univ : Finset (Fin k)).piAntidiag c, compositionWeight k q

theorem compositionWeight_succ {n : ℕ} (j : ℕ) (q : Fin n → ℕ) :
    compositionWeight (n + 1) (Fin.cons j q) =
      ((Nat.factorial (2 * j) : ℚ) / Nat.factorial j) * compositionWeight n q := by
  unfold compositionWeight
  rw [Fin.prod_univ_succ]
  rfl

theorem compositionMoment_succ_recurrence (n c : ℕ) :
    compositionMoment (n + 1) c =
      ∑ j ∈ Finset.range (c + 1),
        ((Nat.factorial (2 * j) : ℚ) / Nat.factorial j) *
          compositionMoment n (c - j) := by
  unfold compositionMoment
  let S := (Finset.univ : Finset (Fin (n + 1))).piAntidiag c
  let T := (Finset.range (c + 1)).sigma
    (fun j => (Finset.univ : Finset (Fin n)).piAntidiag (c - j))
  have hsum :
      (∑ q ∈ S, compositionWeight (n + 1) q) =
        ∑ p ∈ T, ((Nat.factorial (2 * p.1) : ℚ) / Nat.factorial p.1) *
          compositionWeight n p.2 := by
    apply Finset.sum_bij (s := S) (t := T)
      (f := compositionWeight (n + 1))
      (g := fun p => ((Nat.factorial (2 * p.1) : ℚ) / Nat.factorial p.1) *
        compositionWeight n p.2)
      (fun q hq => Sigma.mk (q 0) (fun i : Fin n => q i.succ))
    · intro q hq
      apply Finset.mem_sigma.2
      have hsumq := (Finset.mem_piAntidiag.mp hq).1
      have hq0 : q 0 ≤ c := by
        have hnonneg : 0 ≤ ∑ i : Fin n, q i.succ := Nat.zero_le _
        rw [Fin.sum_univ_succ] at hsumq
        omega
      refine ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hq0), ?_⟩
      apply Finset.mem_piAntidiag.2
      constructor
      · rw [Fin.sum_univ_succ] at hsumq
        have htail : ∑ i : Fin n, q i.succ = c - q 0 := by omega
        exact htail
      · intro i hi
        simp
    · intro q₁ hq₁ q₂ hq₂ h
      funext i
      have h0 : q₁ 0 = q₂ 0 := by simpa using congrArg (fun p => p.1) h
      have ht (j : Fin n) : q₁ j.succ = q₂ j.succ := by
        simpa using congrArg (fun p => p.2 j) h
      exact Fin.cases h0 ht i
    · intro p hp
      refine ⟨Fin.cons p.1 p.2, ?_, ?_⟩
      · apply Finset.mem_piAntidiag.2
        rcases Finset.mem_sigma.mp hp with ⟨hpj, hpq⟩
        refine ⟨?_, by simp⟩
        have hs := (Finset.mem_piAntidiag.mp hpq).1
        have hj : p.1 ≤ c := Nat.le_of_lt_succ (Finset.mem_range.mp hpj)
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        calc
          p.1 + ∑ i, p.2 i = p.1 + (c - p.1) := by rw [hs]
          _ = c := by omega
      · apply Sigma.ext
        · rfl
        · simp
    · intro q hq
      have hqeq : q = Fin.cons (q 0) (fun i : Fin n => q i.succ) := by
        funext i
        exact Fin.cases rfl (fun j => rfl) i
      rw [hqeq]
      simpa [Fin.cons] using
        (compositionWeight_succ (n := n) (q 0) (fun i : Fin n => q i.succ))
  rw [hsum, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]

def compositionMomentDP : ℕ → ℕ → ℚ
  | 0, c => if c = 0 then 1 else 0
  | n + 1, c =>
      ∑ j ∈ Finset.range (c + 1),
        ((Nat.factorial (2 * j) : ℚ) / Nat.factorial j) *
          compositionMomentDP n (c - j)

theorem compositionMoment_zero (c : ℕ) :
    compositionMoment 0 c = compositionMomentDP 0 c := by
  unfold compositionMoment compositionMomentDP
  by_cases hc : c = 0
  · subst c
    simp [compositionWeight]
  · simp [hc]

theorem compositionMoment_eq_dp (k c : ℕ) :
    compositionMoment k c = compositionMomentDP k c := by
  induction k generalizing c with
  | zero => exact compositionMoment_zero c
  | succ n ih =>
    rw [compositionMoment_succ_recurrence]
    simp_rw [ih]
    rfl

set_option maxHeartbeats 10000000 in
theorem smallKGFormula_dp_recurrence (c : Fin 11) (k : ℕ) :
    (smallKGFormula c.1 (k + 1) : ℚ) / Nat.factorial c.1 =
      ∑ j ∈ Finset.range (c.1 + 1),
        ((Nat.factorial (2 * j) : ℚ) / Nat.factorial j) *
          (smallKGFormula (c.1 - j) k : ℚ) /
            Nat.factorial (c.1 - j) := by
  fin_cases c <;>
    simp [smallKGFormula, Finset.sum_range_succ, Nat.choose_succ_succ,
      smallKCompositionWeight_sum_eq_table_nat,
      smallKCompositionWeight_cast_sum_eq_table_nat,
      smallKCompositionWeightTable] <;> ring

set_option maxHeartbeats 10000000 in
theorem compositionMomentDP_eq_smallKGFormula_div_factorial
    (k : ℕ) (c : Fin 11) :
    compositionMomentDP k c.1 =
      (smallKGFormula c.1 k : ℚ) / Nat.factorial c.1 := by
  induction k generalizing c with
  | zero =>
      fin_cases c <;>
        norm_num [compositionMomentDP, smallKGFormula,
          smallKPositiveCompositions, smallKCompositionWeight,
          Finset.sum_range_succ]
  | succ k ih =>
      rw [compositionMomentDP, smallKGFormula_dp_recurrence]
      apply Finset.sum_congr rfl
      intro j hj
      have hcj : c.1 - j < 11 :=
        lt_of_le_of_lt (Nat.sub_le c.1 j) c.isLt
      rw [ih ⟨c.1 - j, hcj⟩]
      ring

theorem compositionMoment_eq_smallKGFormula_div_factorial
    (k : ℕ) (c : Fin 11) :
    compositionMoment k c.1 =
      (smallKGFormula c.1 k : ℚ) / Nat.factorial c.1 := by
  rw [compositionMoment_eq_dp]
  exact compositionMomentDP_eq_smallKGFormula_div_factorial k c

theorem compositionMoment_105_eq_smallKG (c : Fin 11) :
    compositionMoment 105 c.1 =
      smallKG105 c.1 / Nat.factorial c.1 := by
  rw [compositionMoment_eq_smallKGFormula_div_factorial,
    smallKG105_eq_formula]

theorem compositionMoment_104_eq_smallKG (c : Fin 11) :
    compositionMoment 104 c.1 =
      smallKG104 c.1 / Nat.factorial c.1 := by
  rw [compositionMoment_eq_smallKGFormula_div_factorial,
    smallKG104_eq_formula]

theorem composition_term_identity (k b c : ℕ) (q : Fin k → ℕ)
    (hq : q ∈ (Finset.univ : Finset (Fin k)).piAntidiag c) :
    (Nat.multinomial (Finset.univ : Finset (Fin k)) q : ℚ) *
        (((∏ i, (2 * q i).factorial : ℕ) : ℚ) * b.factorial /
          (k + b + ∑ i, 2 * q i).factorial) =
      ((c.factorial : ℚ) * b.factorial / (k + b + 2 * c).factorial) *
        compositionWeight k q := by
  have hsum : ∑ i, q i = c := (Finset.mem_piAntidiag.mp hq).1
  have hsum2 : ∑ i, 2 * q i = 2 * c := by
    rw [← Finset.mul_sum]
    omega
  have hmulti := Nat.multinomial_spec
    (s := (Finset.univ : Finset (Fin k))) (f := q)
  rw [hsum] at hmulti
  rw [hsum2]
  unfold compositionWeight
  rw [Finset.prod_div_distrib]
  push_cast at hmulti ⊢
  field_simp
  rw [← hmulti]
  norm_cast
  ring

theorem simplexQuadratic_moment_compact (k b c : ℕ) :
    (∫ t in maynardSimplex k, simplexQuadraticIntegrand k b c t) =
      (((b.factorial : ℚ) * c.factorial /
          (k + b + 2 * c).factorial * compositionMoment k c) : ℝ) := by
  rw [simplexQuadratic_moment_formula]
  have hsum :
      (∑ q ∈ (Finset.univ : Finset (Fin k)).piAntidiag c,
        (Nat.multinomial (Finset.univ : Finset (Fin k)) q : ℝ) *
          (((∏ i, (2 * q i).factorial : ℕ) : ℝ) * b.factorial /
            (k + b + ∑ i, 2 * q i).factorial)) =
      ∑ q ∈ (Finset.univ : Finset (Fin k)).piAntidiag c,
        (((c.factorial : ℚ) * b.factorial /
            (k + b + 2 * c).factorial) : ℝ) * compositionWeight k q := by
    apply Finset.sum_congr rfl
    intro q hq
    have hterm := composition_term_identity k b c q hq
    have htermR := congrArg (fun z : ℚ => (z : ℝ)) hterm
    convert htermR using 1 <;> push_cast <;> ring
  rw [hsum]
  have hcast : (compositionMoment k c : ℝ) =
      ∑ q ∈ (Finset.univ : Finset (Fin k)).piAntidiag c,
        (compositionWeight k q : ℝ) := by
    unfold compositionMoment
    norm_cast
  calc
    (∑ q ∈ (Finset.univ : Finset (Fin k)).piAntidiag c,
        (((c.factorial : ℚ) * b.factorial /
            (k + b + 2 * c).factorial) : ℝ) * compositionWeight k q) =
      (((c.factorial : ℚ) * b.factorial /
          (k + b + 2 * c).factorial) : ℝ) *
        ∑ q ∈ (Finset.univ : Finset (Fin k)).piAntidiag c,
          (compositionWeight k q : ℝ) := by
      symm
      rw [Finset.mul_sum]
    _ = (((c.factorial : ℚ) * b.factorial /
          (k + b + 2 * c).factorial) : ℝ) *
        (compositionMoment k c : ℝ) := by rw [hcast]
    _ = (((b.factorial : ℚ) * c.factorial /
          (k + b + 2 * c).factorial * compositionMoment k c) : ℝ) := by
      unfold compositionMoment
      push_cast
      ring

theorem simplexQuadratic_moment_105_smallKG (b : ℕ) (c : Fin 11) :
    (∫ t in maynardSimplex 105, simplexQuadraticIntegrand 105 b c.1 t) =
      ((Nat.factorial b : ℚ) /
        Nat.factorial (105 + b + 2 * c.1) * smallKG105 c.1 : ℝ) := by
  rw [simplexQuadratic_moment_compact, compositionMoment_105_eq_smallKG]
  push_cast
  field_simp

theorem simplexQuadratic_moment_104_smallKG (b : ℕ) (c : Fin 11) :
    (∫ t in maynardSimplex 104, simplexQuadraticIntegrand 104 b c.1 t) =
      ((Nat.factorial b : ℚ) /
        Nat.factorial (104 + b + 2 * c.1) * smallKG104 c.1 : ℝ) := by
  rw [simplexQuadratic_moment_compact, compositionMoment_104_eq_smallKG]
  push_cast
  field_simp


end
end BoundedGaps.Maynard
