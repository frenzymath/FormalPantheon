import PrimesRestrictedDigits.ExceptionalMinorArcs.LineZeroCoefficientCases
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Divisor fibers for the first zero coefficient

This is the nonzero-product case represented by the worked `v1=0`
argument in `MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 210--211.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The `v1=0` witness case is controlled by two bounded free coefficients
and one signed factor-pair fiber. -/
theorem zeroFirstCoefficientPlaneWitnesses_card_real_le
    {X : Nat} (C : Finset (Fin X)) (V Q : Real)
    (hV : 1 <= V) (hVX : V < (X : Real))
    (hQ : 0 <= Q)
    (hfactor : forall z : Int,
      (z.natAbs : Real) <= 3 * ((X : Real) ^ 2) ->
      (z.divisorsAntidiag.card : Real) <= Q) :
    ((zeroFirstCoefficientPlaneWitnesses C V).card : Real) <=
      (C.card : Real) * ((lineCoefficientBox V).card : Real) ^ 2 * Q := by
  classical
  let Cpos := C.filter fun a => 0 < a.val
  let coeff := lineCoefficientBox V
  let S := zeroFirstCoefficientPlaneWitnesses C V
  let outer := Cpos.product (coeff.product coeff)
  let key : LowHeightPlaneWitness X -> Prod (Fin X) (Prod Int Int) :=
    fun w => (w.a1, (w.v 2, w.v4))
  have hVNonneg : 0 <= V := zero_le_one.trans hV
  have hmaps :
      Set.MapsTo key (S : Set (LowHeightPlaneWitness X))
        (outer : Set (Prod (Fin X) (Prod Int Int))) := by
    intro w hw
    have hwCase := Finset.mem_filter.mp hw
    have hwZero := mem_positiveZeroCoefficientPlaneWitnesses.mp hwCase.1
    have hwData := mem_positivePlaneWitnessCandidates.mp hwZero.1
    change key w ∈ outer
    dsimp only [outer]
    rw [Finset.product_eq_sprod, Finset.mem_product]
    exact ⟨Finset.mem_filter.mpr ⟨hwData.1, hwData.2.1⟩,
      Finset.mem_product.mpr
        ⟨hwData.2.2.2.2.1 2, hwData.2.2.2.2.2⟩⟩
  have hfiber : forall k : Prod (Fin X) (Prod Int Int), k ∈ outer ->
      ((S.filter fun w => key w = k).card : Real) <= Q := by
    intro k _hk
    let z : Int := -(k.2.1 * (X : Int) + k.2.2)
    let embedding : LowHeightPlaneWitness X -> Prod Int Int := fun w =>
      (w.v 1, (w.a2.val : Int))
    have hcard :
        (S.filter fun w => key w = k).card <=
          z.divisorsAntidiag.card := by
      apply Finset.card_le_card_of_injOn embedding
      · intro w hw
        have hwData := Finset.mem_filter.mp hw
        have hwCase := Finset.mem_filter.mp hwData.1
        have hwZero :=
          mem_positiveZeroCoefficientPlaneWitnesses.mp hwCase.1
        have hwCandidate :=
          mem_positivePlaneWitnessCandidates.mp hwZero.1
        have hwRelation := hwZero.2.1
        have htarget : Not (z = 0) := by
          intro hz
          have hkey := hwData.2
          have hv3 : w.v 2 = k.2.1 :=
            congrArg (fun q => q.2.1) hkey
          have hv4 : w.v4 = k.2.2 :=
            congrArg (fun q => q.2.2) hkey
          have hsmall : w.v 2 * (X : Int) + w.v4 = 0 := by
            dsimp only [z] at hz
            rw [← hv3, ← hv4] at hz
            omega
          have hsmallZero := eq_zero_of_mul_scale_add_eq_zero
            hVNonneg hVX (hwRelation.2.1 2) hwRelation.2.2.1 hsmall
          have hproduct : w.v 1 * (w.a2.val : Int) = 0 := by
            have hrelation := LowHeightPlaneWitness.relation_eq hwRelation
            rw [hwCase.2, hsmallZero.1, hsmallZero.2] at hrelation
            norm_num at hrelation ⊢
            exact hrelation
          have ha2 : Not ((w.a2.val : Int) = 0) := by
            exact_mod_cast hwCandidate.2.2.2.1.ne'
          have hv2 : w.v 1 = 0 :=
            (Int.mul_eq_zero.mp hproduct).resolve_right ha2
          have hvAll : w.v = 0 := by
            funext i
            fin_cases i
            · exact hwCase.2
            · exact hv2
            · exact hsmallZero.1
          exact hwRelation.1.elim (fun h => h hvAll)
            (fun h => h hsmallZero.2)
        change (w.v 1, (w.a2.val : Int)) ∈ z.divisorsAntidiag
        rw [Int.prodMk_mem_divisorsAntidiag htarget]
        have hkey := hwData.2
        have hv3 : w.v 2 = k.2.1 :=
          congrArg (fun q => q.2.1) hkey
        have hv4 : w.v4 = k.2.2 :=
          congrArg (fun q => q.2.2) hkey
        dsimp only [z]
        rw [← hv3, ← hv4]
        have hrelation := LowHeightPlaneWitness.relation_eq hwRelation
        rw [hwCase.2] at hrelation
        linear_combination hrelation
      · intro w hw w' hw' hembedding
        have hwData := Finset.mem_filter.mp hw
        have hw'Data := Finset.mem_filter.mp hw'
        have hwCase := Finset.mem_filter.mp hwData.1
        have hw'Case := Finset.mem_filter.mp hw'Data.1
        have hkey : key w = key w' := hwData.2.trans hw'Data.2.symm
        apply LowHeightPlaneWitness.ext
        · exact congrArg (fun q => q.1) hkey
        · apply Fin.ext
          have hval : (w.a2.val : Int) = (w'.a2.val : Int) :=
            congrArg (fun q => q.2) hembedding
          exact_mod_cast hval
        · funext i
          fin_cases i
          · exact hwCase.2.trans hw'Case.2.symm
          · exact congrArg (fun q => q.1) hembedding
          · exact congrArg (fun q => q.2.1) hkey
        · exact congrArg (fun q => q.2.2) hkey
    by_cases hnonempty : (S.filter fun w => key w = k).Nonempty
    · let w := hnonempty.choose
      have hw := Finset.mem_filter.mp hnonempty.choose_spec
      have hwCase := Finset.mem_filter.mp hw.1
      have hwZero :=
        mem_positiveZeroCoefficientPlaneWitnesses.mp hwCase.1
      have hwRelation := hwZero.2.1
      have hkey := hw.2
      have hv3 : w.v 2 = k.2.1 :=
        congrArg (fun q => q.2.1) hkey
      have hv4 : w.v4 = k.2.2 :=
        congrArg (fun q => q.2.2) hkey
      have hbound := lineZeroTermTarget_natAbs_le_three_mul_sq
        w.a2 0 (w.v 2) w.v4 hVNonneg hVX (by simpa using hVNonneg)
          (hwRelation.2.1 2) hwRelation.2.2.1
      have htargetBound :
          (z.natAbs : Real) <= 3 * ((X : Real) ^ 2) := by
        dsimp only [z]
        rw [← hv3, ← hv4, Int.natAbs_neg]
        simpa only [zero_mul, zero_add] using hbound
      calc
        ((S.filter fun w => key w = k).card : Real) <=
            (z.divisorsAntidiag.card : Real) := by exact_mod_cast hcard
        _ <= Q := hfactor z htargetBound
    · have hempty : S.filter (fun w => key w = k) = Finset.empty :=
        Finset.not_nonempty_iff_eq_empty.mp hnonempty
      rw [hempty]
      simpa using hQ
  have hdecomp := Finset.card_eq_sum_card_fiberwise hmaps
  have houter :
      (outer.card : Real) <=
        (C.card : Real) * ((lineCoefficientBox V).card : Real) ^ 2 := by
    dsimp only [outer, Cpos, coeff]
    rw [Finset.product_eq_sprod,
      Finset.card_product, Finset.product_eq_sprod, Finset.card_product]
    push_cast
    have hpos : ((C.filter fun a => 0 < a.val).card : Real) <= C.card := by
      exact_mod_cast Finset.card_filter_le C fun a => 0 < a.val
    nlinarith [sq_nonneg ((lineCoefficientBox V).card : Real)]
  calc
    (S.card : Real) =
        ∑ k ∈ outer, ((S.filter fun w => key w = k).card : Real) := by
      simpa only [Nat.cast_sum] using
        congrArg (fun n : Nat => (n : Real)) hdecomp
    _ <= ∑ _k ∈ outer, Q :=
      Finset.sum_le_sum fun k hk => hfiber k hk
    _ = (outer.card : Real) * Q := by simp
    _ <= ((C.card : Real) *
        ((lineCoefficientBox V).card : Real) ^ 2) * Q := by
      gcongr

end PrimesRestrictedDigits
