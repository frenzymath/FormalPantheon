import PrimesRestrictedDigits.MajorArcs.ProjectedBox

/-!
# The major-arc logarithmic region and its projection

This formalizes the region in Proposition 9.1 and the statement after
Eq. (11.2) of `MAYNARD-PRD-PUBLISHED` that its first-coordinate projection is
the box `C`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The first `ell - 1` normalized-log coordinate box `C`, with `ell = k + 1`.
The intervals retain the source's strict lower and weak upper endpoints. -/
def projectedLogBox {k : ℕ} (a : Fin k → ℝ) (delta : ℝ) :
    Set (Fin k → ℝ) :=
  {x | ∀ i, x i ∈ Set.Ioc (a i) (a i + delta)}

/-- The region `R_X` from Proposition 9.1, parameterized by its width instead
of `X`. The first coordinates are represented by `Fin.init`. -/
def majorArcLogRegion {k : ℕ} (a : Fin k → ℝ) (delta eta : ℝ) :
    Set (Fin (k + 1) → ℝ) :=
  {e | Fin.init e ∈ projectedLogBox a delta ∧
    (∑ i, e i) ≤ 1 ∧
    max (eta / 4) (1 - (∑ i, a i) - ((k + 1 : ℕ) : ℝ) * delta) ≤
      e (Fin.last k)}

/-- Complete a projected point by choosing its last coordinate so that the
total coordinate sum is exactly one. -/
def completeProjectedLogTuple {k : ℕ} (x : Fin k → ℝ) :
    Fin (k + 1) → ℝ :=
  Fin.snoc x (1 - ∑ i, x i)

@[simp] theorem init_completeProjectedLogTuple {k : ℕ} (x : Fin k → ℝ) :
    Fin.init (completeProjectedLogTuple x) = x := by
  simp [completeProjectedLogTuple]

@[simp] theorem last_completeProjectedLogTuple {k : ℕ} (x : Fin k → ℝ) :
    completeProjectedLogTuple x (Fin.last k) = 1 - ∑ i, x i := by
  simp [completeProjectedLogTuple]

@[simp] theorem sum_completeProjectedLogTuple {k : ℕ} (x : Fin k → ℝ) :
    (∑ i, completeProjectedLogTuple x i) = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp [completeProjectedLogTuple]

/-- Every point of the full region projects into the displayed box. -/
theorem init_mem_projectedLogBox_of_mem_majorArcLogRegion
    {k : ℕ} {a : Fin k → ℝ} {delta eta : ℝ} {e : Fin (k + 1) → ℝ}
    (he : e ∈ majorArcLogRegion a delta eta) :
    Fin.init e ∈ projectedLogBox a delta :=
  he.1

/-- The canonical completion lies in the full region whenever the last
coordinate has the two source-required margins. -/
theorem completeProjectedLogTuple_mem_majorArcLogRegion
    {k : ℕ} {a x : Fin k → ℝ} {delta eta : ℝ}
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hdelta0 : 0 ≤ delta) (hkdelta : (k : ℝ) * delta ≤ eta / 4)
    (hx : x ∈ projectedLogBox a delta) :
    completeProjectedLogTuple x ∈ majorArcLogRegion a delta eta := by
  have hsumx : (∑ i, x i) ≤ (∑ i, a i) + (k : ℝ) * delta := by
    calc
      (∑ i, x i) ≤ ∑ i, (a i + delta) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (hx i).2
      _ = (∑ i, a i) + (k : ℝ) * delta := by
        rw [Finset.sum_add_distrib, Fin.sum_const]
        simp
  have hroom : eta / 4 ≤ 1 - ∑ i, x i := by
    linarith
  have hlower : 1 - (∑ i, a i) - ((k + 1 : ℕ) : ℝ) * delta ≤
      1 - ∑ i, x i := by
    have hkcast : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ k
    have hmul := mul_le_mul_of_nonneg_right hkcast hdelta0
    linarith
  exact ⟨by simpa using hx, by simp, by simpa using max_le hroom hlower⟩

/-- Under the direct room hypotheses, the full region projects onto exactly
the box `C`. -/
theorem image_init_majorArcLogRegion_eq_projectedLogBox
    {k : ℕ} {a : Fin k → ℝ} {delta eta : ℝ}
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hdelta0 : 0 ≤ delta) (hkdelta : (k : ℝ) * delta ≤ eta / 4) :
    Fin.init '' majorArcLogRegion a delta eta = projectedLogBox a delta := by
  apply Set.Subset.antisymm
  · rintro x ⟨e, he, rfl⟩
    exact init_mem_projectedLogBox_of_mem_majorArcLogRegion he
  · intro x hx
    exact ⟨completeProjectedLogTuple x,
      completeProjectedLogTuple_mem_majorArcLogRegion
        hsum hdelta0 hkdelta hx, by simp⟩

/--
The source arity and the explicit small-width condition imply the exact projection identity.
-/
theorem image_init_majorArcLogRegion_eq_projectedLogBox_of_small_delta
    {k : ℕ} {a : Fin k → ℝ} {delta eta : ℝ}
    (heta : 0 < eta) (hsum : (∑ i, a i) < 1 - eta / 2)
    (hell : ((k + 1 : ℕ) : ℝ) ≤ 2 / eta)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ eta ^ 2 / 12) :
    Fin.init '' majorArcLogRegion a delta eta = projectedLogBox a delta := by
  have hk : (k : ℝ) ≤ 2 / eta := by
    calc
      (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
      _ ≤ 2 / eta := hell
  apply image_init_majorArcLogRegion_eq_projectedLogBox hsum hdelta0
  exact (natCast_mul_delta_le_eta_div_six heta hk hdelta0 hdelta).trans (by linarith)

/--
The literal projection statement for Maynard's `delta = (log (log X))⁻¹`, with the explicit
sufficient threshold.
-/
theorem image_init_majorArcLogRegion_logLog_eq_projectedLogBox
    {X k : ℕ} {a : Fin k → ℝ} {eta : ℝ}
    (heta : 0 < eta) (hsum : (∑ i, a i) < 1 - eta / 2)
    (hell : ((k + 1 : ℕ) : ℝ) ≤ 2 / eta)
    (hlarge : Real.exp (Real.exp (12 / eta ^ 2)) ≤ (X : ℝ)) :
    Fin.init '' majorArcLogRegion a
        (Real.log (Real.log (X : ℝ)))⁻¹ eta =
      projectedLogBox a (Real.log (Real.log (X : ℝ)))⁻¹ := by
  have hloglog := twelve_div_eta_sq_le_log_log_of_exp_exp_le hlarge
  apply image_init_majorArcLogRegion_eq_projectedLogBox_of_small_delta
    heta hsum hell
  · exact inv_nonneg.mpr
      ((show (0 : ℝ) ≤ 12 / eta ^ 2 by positivity).trans hloglog)
  · exact inv_log_log_le_eta_sq_div_twelve heta hloglog

end PrimesRestrictedDigits
