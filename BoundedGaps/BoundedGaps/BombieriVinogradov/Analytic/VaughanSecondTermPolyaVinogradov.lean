import BoundedGaps.BombieriVinogradov.Analytic.PrimitivePolyaVinogradov
import BoundedGaps.BombieriVinogradov.Analytic.VaughanSecondTermReduction

/-!
# Polya--Vinogradov bound for Vaughan's second term

This file transfers the primitive interval theorem to SEM-433's natural
interval convention and proves AkbaryHambrook2013v2, equation (6.9). The raw
modulus-one estimate and the aggregate equation (6.10) remain separate.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

/-- Primitive Polya--Vinogradov on an inclusive natural interval. -/
theorem norm_dirichletCharacterIntervalSum_lt_sqrt_mul_log
    {q : ℕ} (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (a b : ℕ) :
    ‖dirichletCharacterIntervalSum a b q chi‖ <
      Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  letI : NeZero q := ⟨Nat.ne_zero_of_lt hq⟩
  have hboundPos :
      0 < Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
    exact mul_pos (Real.sqrt_pos.2 (by exact_mod_cast Nat.zero_lt_of_lt hq))
      (Real.log_pos (by exact_mod_cast hq))
  by_cases hab : a ≤ b
  · have hendpoint :
        (a : ℤ) - 1 + (((b - a) + 1 : ℕ) : ℤ) = (b : ℤ) := by
      rw [Nat.cast_add, Nat.cast_sub hab]
      push_cast
      ring
    have hfinset :
        (Finset.Icc a b).map (Nat.castEmbedding : ℕ ↪ ℤ) =
          Finset.Ioc ((a : ℤ) - 1) (b : ℤ) := by
      ext n
      simp only [Finset.mem_map, Nat.castEmbedding_apply, Finset.mem_Icc,
        Finset.mem_Ioc]
      constructor
      · rintro ⟨m, hm, rfl⟩
        constructor <;> omega
      · intro hn
        have hnnonneg : 0 ≤ n := by
          have : (a : ℤ) ≤ n := by omega
          exact (Int.natCast_nonneg a).trans this
        lift n to ℕ using hnnonneg with m
        refine ⟨m, ?_, rfl⟩
        constructor <;> omega
    rw [dirichletCharacterIntervalSum]
    calc
      ‖∑ n ∈ Finset.Icc a b, chi n‖ =
          ‖∑ n ∈ Finset.Ioc ((a : ℤ) - 1) (b : ℤ),
            chi (n : ZMod q)‖ := by
        rw [← hfinset, Finset.sum_map]
        simp
      _ = ‖∑ n ∈ Finset.Ioc ((a : ℤ) - 1)
            ((a : ℤ) - 1 + (((b - a) + 1 : ℕ) : ℤ)),
            chi (n : ZMod q)‖ := by rw [hendpoint]
      _ < Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
        norm_sum_dirichletCharacter_Ioc_lt_sqrt_mul_log hq chi hchi
          ((a : ℤ) - 1) ((b - a) + 1)
  · rw [dirichletCharacterIntervalSum, Finset.Icc_eq_empty (by omega),
      Finset.sum_empty, norm_zero]
    exact hboundPos

/-- Natural-endpoint form of Akbary--Hambrook equation (6.9). -/
theorem norm_vaughanTwistedSumTwo_lt_sqrt_mul_cutoff_mul_log_sq
    {Q V : ℝ} {x y q : ℕ}
    (hx : 4 ≤ x) (hV : 1 ≤ V) (hyx : y ≤ x)
    (hq : 1 < q) (hqQ : (q : ℝ) ≤ Q)
    (hQsqrt : Q ≤ Real.sqrt (x : ℝ))
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive) :
    ‖vaughanTwistedSumTwo V y q chi‖ <
      Real.sqrt (q : ℝ) * V *
        (Real.log ((x : ℝ) * V)) ^ 2 := by
  letI : NeZero q := ⟨Nat.ne_zero_of_lt hq⟩
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast Nat.zero_lt_of_lt hq
  have hsqrtq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqpos
  have hlogq : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast hq)
  have hC : 0 ≤ Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
    (mul_pos hsqrtq hlogq).le
  have hxReal : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hsqrtxlt : Real.sqrt (x : ℝ) < (x : ℝ) :=
    Real.sqrt_lt_self_iff.mpr hxReal
  have hxle : (x : ℝ) ≤ (x : ℝ) * V := by
    nlinarith [show (0 : ℝ) < x by positivity]
  have hq_lt_xV : (q : ℝ) < (x : ℝ) * V :=
    (hqQ.trans hQsqrt).trans_lt (hsqrtxlt.trans_le hxle)
  have hxVpos : 0 < (x : ℝ) * V := by positivity
  have hlogq_lt : Real.log (q : ℝ) < Real.log ((x : ℝ) * V) :=
    Real.strictMonoOn_log hqpos hxVpos hq_lt_xV
  have hlogxVpos : 0 < Real.log ((x : ℝ) * V) := by
    exact Real.log_pos (hxReal.trans_le hxle)
  by_cases hyzero : y = 0
  · subst y
    rw [vaughanTwistedSumTwo_eq_divisorLogSums]
    simp [vaughanSecondTermIndices]
    positivity
  have hy : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hyzero
  have hbase := norm_vaughanTwistedSumTwo_le_cutoff_mul_of_intervalBound
    hV hy hC chi (fun _d _hd a _ha ↦
      (norm_dirichletCharacterIntervalSum_lt_sqrt_mul_log
        hq chi hchi a (y / _d)).le)
  have hy_le_xV : (y : ℝ) ≤ (x : ℝ) * V := by
    exact (by exact_mod_cast hyx : (y : ℝ) ≤ x) |>.trans hxle
  have hlogy_le : Real.log (y : ℝ) ≤ Real.log ((x : ℝ) * V) :=
    Real.log_le_log (by exact_mod_cast (show 0 < y by omega)) hy_le_xV
  have hlogs :
      Real.log (y : ℝ) * Real.log (q : ℝ) <
        (Real.log ((x : ℝ) * V)) ^ 2 := by
    calc
      Real.log (y : ℝ) * Real.log (q : ℝ) ≤
          Real.log ((x : ℝ) * V) * Real.log (q : ℝ) := by
        exact mul_le_mul_of_nonneg_right hlogy_le hlogq.le
      _ < Real.log ((x : ℝ) * V) * Real.log ((x : ℝ) * V) := by
        exact mul_lt_mul_of_pos_left hlogq_lt hlogxVpos
      _ = (Real.log ((x : ℝ) * V)) ^ 2 := by ring
  calc
    ‖vaughanTwistedSumTwo V y q chi‖ ≤
        V * Real.log (y : ℝ) *
          (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) := hbase
    _ = Real.sqrt (q : ℝ) * V *
        (Real.log (y : ℝ) * Real.log (q : ℝ)) := by ring
    _ < Real.sqrt (q : ℝ) * V *
        (Real.log ((x : ℝ) * V)) ^ 2 := by
      gcongr

end BoundedGaps.Maynard
