import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelPartialSums

/-!
# Positive interiors of dimension-one Rosser model terms

This proves the finite-rank positivity needed for Iwaniec's Lemma 18. See
`IWANIEC-ROSSER-SIEVE-1980`, printed p. 195.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

private theorem integral_Ioi_shiftedRosserKernel_pos
    (f : Real -> Real) {s upper : Real}
    (hs : 1 <= s) (hsupper : s < upper)
    (hnonneg : forall x, 0 <= f x)
    (hpos : forall {x}, s - 1 < x -> x < upper - 1 -> 0 < f x)
    (hint : Integrable (shiftedRosserKernel f)) :
    0 < ∫ t in Ioi s, shiftedRosserKernel f t := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun (t : Real) ht => by
      change s < t at ht
      exact div_nonneg (hnonneg (t - 1)) (by linarith)))
    hint.integrableOn).2
  let midpoint := (s + upper) / 2
  have hmidLower : s < midpoint := by
    dsimp [midpoint]
    linarith
  have hmidUpper : midpoint < upper := by
    dsimp [midpoint]
    linarith
  have hsub : Ioo s midpoint ⊆
      Function.support (shiftedRosserKernel f) ∩ Ioi s := by
    intro t ht
    change s < t ∧ t < midpoint at ht
    have htpos : 0 < t - 1 := by linarith
    constructor
    · exact (div_pos (hpos (by linarith) (by linarith)) htpos).ne'
    · exact ht.1
  have hm : volume (Ioo s midpoint) <=
      volume (Function.support (shiftedRosserKernel f) ∩ Ioi s) :=
    measure_mono hsub
  have hvol : 0 < volume (Ioo s midpoint) := by
    rw [Real.volume_Ioo]
    simp [hmidLower]
  exact hvol.trans_le hm

private theorem dimensionOneRosserModelTerm_pos_data (r : Nat) :
    (forall {s : Real}, 1 < s -> s < 3 + 2 * (r : Real) ->
      0 < dimensionOneRosserModelPlusTerm r s) /\
    (forall {s : Real}, 2 <= s -> s < 2 + 2 * (r : Real) ->
      0 < dimensionOneRosserModelMinusTerm r s) := by
  induction r with
  | zero =>
      constructor
      · intro s hs1 hs3
        norm_num at hs3
        rw [dimensionOneRosserModelPlusTerm_zero,
          if_pos ⟨hs1.le, hs3.le⟩]
        linarith
      · intro s hs2 hupper
        norm_num at hupper
        linarith
  | succ r ih =>
      have hminus : forall {s : Real}, 2 <= s ->
          s < 2 + 2 * ((r + 1 : Nat) : Real) ->
          0 < dimensionOneRosserModelMinusTerm (r + 1) s := by
        intro s hs2 hupper
        rw [dimensionOneRosserModelMinusTerm_succ_integral r hs2]
        simpa only [shiftedRosserKernel] using
          integral_Ioi_shiftedRosserKernel_pos
            (dimensionOneRosserModelPlusTerm r)
            (s := s) (upper := 4 + 2 * (r : Real))
            (by linarith)
            (by push_cast at hupper; linarith)
            (dimensionOneRosserModelPlusTerm_nonneg r)
            (fun hxLower hxUpper => ih.1 (by linarith) (by linarith))
            (integrable_shiftedRosserKernel_plusTerm r)
      refine ⟨?_, hminus⟩
      intro s hs1 hupper
      rw [dimensionOneRosserModelPlusTerm_succ_eq, if_pos hs1.le]
      simpa only [shiftedRosserKernel] using
        integral_Ioi_shiftedRosserKernel_pos
          (dimensionOneRosserModelMinusTerm (r + 1))
          (s := max 3 s) (upper := 5 + 2 * (r : Real))
          (by linarith [le_max_left (3 : Real) s])
          (by
            push_cast at hupper
            exact max_lt (by
              have hr : 0 <= (r : Real) := Nat.cast_nonneg r
              linarith) (by linarith))
          (dimensionOneRosserModelMinusTerm_nonneg (r + 1))
          (fun hxLower hxUpper => hminus (by
            have hm : (3 : Real) <= max 3 s := le_max_left 3 s
            linarith) (by
              push_cast
              linarith))
          (integrable_shiftedRosserKernel_minusTerm (r + 1))

/-- An upper rank term is positive in the interior of its support. -/
theorem dimensionOneRosserModelPlusTerm_pos (r : Nat) {s : Real}
    (hs1 : 1 < s) (hupper : s < 3 + 2 * (r : Real)) :
    0 < dimensionOneRosserModelPlusTerm r s :=
  (dimensionOneRosserModelTerm_pos_data r).1 hs1 hupper

/-- A lower rank term is positive from its weak left endpoint up to the strict
upper support endpoint. For rank zero the hypotheses describe an empty
interval. -/
theorem dimensionOneRosserModelMinusTerm_pos (r : Nat) {s : Real}
    (hs2 : 2 <= s) (hupper : s < 2 + 2 * (r : Real)) :
    0 < dimensionOneRosserModelMinusTerm r s :=
  (dimensionOneRosserModelTerm_pos_data r).2 hs2 hupper

end PrimesRestrictedDigits
