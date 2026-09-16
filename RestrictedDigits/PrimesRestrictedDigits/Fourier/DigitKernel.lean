import PrimesRestrictedDigits.Fourier.DigitFactorization

/-!
# Continuous single-digit kernel and window majorant

The finite digit sum is the total form of the local factor in
`MAYNARD-PRD-PUBLISHED`, Eq. (10.2). The one-sided window records the decimal
tail used by the Markov argument without relying on the source's singular
quotient spelling or any numerical approximation.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable def digitKernel (a : Fin 10) (x : ℝ) : ℝ :=
  (1 / 9 : ℝ) *
    ‖∑ d ∈ allowedDecimalDigits a,
      Complex.exp (((2 * Real.pi * (d : ℝ) * x : ℝ) : ℂ) * Complex.I)‖

noncomputable def digitWindowArgument (J : ℕ) (t : Fin (J + 1) → Fin 10) : ℝ :=
  ∑ j : Fin (J + 1), (t j : ℝ) / (10 : ℝ) ^ (j.val + 1)

private theorem card_allowedDecimalDigits (a : Fin 10) :
    (allowedDecimalDigits a).card = 9 := by
  rw [allowedDecimalDigits]
  have heq :
      (Finset.range 10).filter (fun d => d ≠ a.val) =
        (Finset.range 10).erase a.val := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    constructor <;> intro h <;> exact ⟨h.2, h.1⟩
  rw [heq, Finset.card_erase_of_mem (Finset.mem_range.mpr a.isLt)]
  norm_num

theorem allowedDecimalDigits_card (a : Fin 10) :
    (allowedDecimalDigits a).card = 9 :=
  card_allowedDecimalDigits a

private theorem norm_digitKernel_phase (d : ℕ) (x : ℝ) :
    ‖Complex.exp (((2 * Real.pi * (d : ℝ) * x : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

theorem digitKernel_nonneg (a : Fin 10) (x : ℝ) : 0 ≤ digitKernel a x := by
  rw [digitKernel]
  positivity

theorem digitKernel_le_one (a : Fin 10) (x : ℝ) : digitKernel a x ≤ 1 := by
  rw [digitKernel]
  have hsum := norm_sum_le (allowedDecimalDigits a)
    (fun d => Complex.exp
      (((2 * Real.pi * (d : ℝ) * x : ℝ) : ℂ) * Complex.I))
  have hsum' :
      ‖∑ d ∈ allowedDecimalDigits a,
          Complex.exp (((2 * Real.pi * (d : ℝ) * x : ℝ) : ℂ) * Complex.I)‖ ≤
        (9 : ℝ) := by
    calc
      _ ≤ ∑ d ∈ allowedDecimalDigits a,
          ‖Complex.exp
            (((2 * Real.pi * (d : ℝ) * x : ℝ) : ℂ) * Complex.I)‖ := hsum
      _ = (allowedDecimalDigits a).card := by
        simp_rw [norm_digitKernel_phase]
        simp
      _ = 9 := by exact_mod_cast allowedDecimalDigits_card a
  nlinarith

private noncomputable def oneSidedWindowValues (a : Fin 10) (J : ℕ)
    (t : Fin (J + 1) → Fin 10) : Set ℝ :=
  Set.range fun gamma : Set.Icc (0 : ℝ) (1 / (10 : ℝ) ^ (J + 1)) =>
    digitKernel a (digitWindowArgument J t + gamma)

noncomputable def oneSidedWindowMajorant (a : Fin 10) (J : ℕ)
    (t : Fin (J + 1) → Fin 10) : ℝ :=
  sSup (oneSidedWindowValues a J t)

private theorem oneSidedWindowValues_bddAbove (a : Fin 10) (J : ℕ)
    (t : Fin (J + 1) → Fin 10) : BddAbove (oneSidedWindowValues a J t) := by
  refine ⟨1, ?_⟩
  rintro y ⟨gamma, rfl⟩
  exact digitKernel_le_one _ _

private theorem oneSidedWindowValues_nonempty (a : Fin 10) (J : ℕ)
    (t : Fin (J + 1) → Fin 10) : (oneSidedWindowValues a J t).Nonempty := by
  refine ⟨digitKernel a (digitWindowArgument J t), ?_⟩
  exact ⟨⟨0, le_rfl, by positivity⟩, by simp⟩

theorem digitKernel_le_oneSidedWindowMajorant (a : Fin 10) (J : ℕ)
    (t : Fin (J + 1) → Fin 10)
    (gamma : Set.Icc (0 : ℝ) (1 / (10 : ℝ) ^ (J + 1))) :
    digitKernel a (digitWindowArgument J t + gamma) ≤
      oneSidedWindowMajorant a J t := by
  rw [oneSidedWindowMajorant]
  exact le_csSup (oneSidedWindowValues_bddAbove a J t) ⟨gamma, rfl⟩

theorem oneSidedWindowMajorant_nonneg (a : Fin 10) (J : ℕ)
    (t : Fin (J + 1) → Fin 10) :
    0 ≤ oneSidedWindowMajorant a J t := by
  have hzero :
      digitKernel a (digitWindowArgument J t) ≤ oneSidedWindowMajorant a J t := by
    rw [oneSidedWindowMajorant]
    exact le_csSup (oneSidedWindowValues_bddAbove a J t)
      ⟨⟨0, le_rfl, by positivity⟩, by simp⟩
  exact (digitKernel_nonneg a _).trans hzero

theorem oneSidedWindowMajorant_le_one (a : Fin 10) (J : ℕ)
    (t : Fin (J + 1) → Fin 10) :
    oneSidedWindowMajorant a J t ≤ 1 := by
  rw [oneSidedWindowMajorant]
  apply csSup_le (oneSidedWindowValues_nonempty a J t)
  intro y hy
  rcases hy with ⟨gamma, rfl⟩
  exact digitKernel_le_one _ _

end PrimesRestrictedDigits
