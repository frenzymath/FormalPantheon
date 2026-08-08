import Waring.Analytic.FiniteFiberCharacterBound
import Waring.Analytic.StepanovTraceFiberBound
import Waring.Analytic.Basic

/-!
# Stepanov bound for even extension-field character sums

The trace-fiber estimate and character orthogonality give a square-root-size
bound for every chosen even extension of degree at least six.  The constant
may depend on the fixed prime and phase degree, but not on the extension
parameter `h`.
 -/

namespace Waring.Analytic

open scoped BigOperators

namespace Stepanov

/-- The standard additive-character sum over the degree-`2 * (h + 3)`
extension is bounded by a fixed coefficient times `p ^ (h + 3)`. -/
theorem norm_extension_pointPhase_sum_le
    {p d : Nat} [Fact p.Prime] (hp : 1 < p)
    (hdpos : 0 < d) (hdp : d < p)
    (b : Fin 5 → ZMod p) (hd5 : d ≤ 5)
    (hbtop : b ⟨d - 1, by omega⟩ ≠ 0)
    (hb : ∀ i : Fin 5, d < i.val + 1 → b i = 0)
    (h : Nat) :
    let E := FiniteField.Extension (ZMod p) p (2 * (h + 3))
    letI : Fintype E := Fintype.ofFinite E
    ‖∑ x : E, ZMod.stdAddChar
      (Algebra.trace (ZMod p) E
        (Weil.pointPhase ((algebraMap (ZMod p) E) ∘ b) x))‖ ≤
      (p * (d * (p - 1) * p + 1) * p ^ (h + 3) : Nat) := by
  classical
  letI : NeZero p := ⟨by omega⟩
  letI : NeZero (2 * (h + 3)) := ⟨by omega⟩
  let E := FiniteField.Extension (ZMod p) p (2 * (h + 3))
  letI : CharP E p :=
    (Algebra.charP_iff (ZMod p) E p).mp (ZMod.charP p)
  letI : Fintype E := Fintype.ofFinite E
  let phaseTrace : E → ZMod p := fun x ↦
    Algebra.trace (ZMod p) E
      (Weil.pointPhase ((algebraMap (ZMod p) E) ∘ b) x)
  let error : Nat := (d * (p - 1) * p + 1) * p ^ (h + 3)
  have hfiber (c : ZMod p) :
      (Finset.univ.filter fun x : E ↦ phaseTrace x = c).card ≤
        degreeBase p h + error := by
    have hbound := card_trace_pointPhase_fiber_le
      hp hdpos hdp b hd5 hbtop hb h c
    rw [traceFiberBound_eq_average_add_error] at hbound
    exact hbound
  have hcardE : Fintype.card E = p ^ (2 * (h + 3)) := by
    rw [Fintype.card_eq_nat_card]
    change Nat.card
      (FiniteField.Extension (ZMod p) p (2 * (h + 3))) = _
    rw [FiniteField.natCard_extension, Nat.card_zmod]
  have hcard :
      Fintype.card E = Fintype.card (ZMod p) * degreeBase p h := by
    rw [hcardE, ZMod.card, degreeBase,
      show 2 * (h + 3) = (2 * h + 5) + 1 by omega, pow_succ]
    ring
  have hcharNe : (ZMod.stdAddChar : AddChar (ZMod p) Complex) ≠ 1 := by
    intro htrivial
    have hprimitive := ZMod.isPrimitive_stdAddChar p
    have hshift := hprimitive (a := 1) one_ne_zero
    rw [AddChar.mulShift_one, htrivial] at hshift
    exact hshift rfl
  have hmean : ∑ c : ZMod p, ZMod.stdAddChar c = 0 :=
    AddChar.sum_eq_zero_of_ne_one hcharNe
  have hweight (c : ZMod p) : ‖ZMod.stdAddChar c‖ ≤ 1 := by
    rw [norm_stdAddChar]
  have hcore := norm_fintype_sum_comp_le_of_card_fiber_le
    phaseTrace (fun c : ZMod p ↦ ZMod.stdAddChar c)
      (degreeBase p h) error hfiber hcard hmean hweight
  simpa only [phaseTrace, error, ZMod.card, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, mul_assoc] using hcore

end Stepanov

end Waring.Analytic
