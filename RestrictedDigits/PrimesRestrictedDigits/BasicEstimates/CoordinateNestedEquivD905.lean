import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FinCases
/-! # CoordinateNestedEquivD905 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

private def coordE0 : (Fin 3 → Real) ≃ᵐ Real × (Fin 2 → Real) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Real) (2 : Fin 3)

private def coordE1 : (Fin 2 → Real) ≃ᵐ Real × Real :=
  MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Real)

def coordinateNestedEquiv : (Fin 3 → Real) ≃ᵐ ((Real × Real) × Real) :=
  coordE0.trans ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl Real) coordE1).trans
    MeasurableEquiv.prodComm)

private theorem coordE0_preserving :
    MeasurePreserving (coordE0 : (Fin 3 → Real) → Real × (Fin 2 → Real)) volume volume := by
  exact volume_preserving_piFinSuccAbove (fun _ : Fin 3 => Real) (2 : Fin 3)

private theorem coordE1_preserving :
    MeasurePreserving (coordE1 : (Fin 2 → Real) → Real × Real) volume volume := by
  exact volume_preserving_piFinTwo (fun _ : Fin 2 => Real)

private theorem coordProduct_preserving :
    MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Real) coordE1 :
        (Real × (Fin 2 → Real)) → (Real × (Real × Real))) volume volume := by
  have h := (MeasurePreserving.id (volume : Measure Real)).prod coordE1_preserving
  change MeasurePreserving (fun p => (p.1, coordE1 p.2))
    (volume.prod volume) (volume.prod volume)
  convert h using 1
  rfl

private theorem coordSwap_preserving :
    MeasurePreserving
      (MeasurableEquiv.prodComm : Real × (Real × Real) → (Real × Real) × Real)
      volume volume := by
  exact Measure.measurePreserving_swap

theorem coordinateNestedEquiv_preserving :
    MeasurePreserving (coordinateNestedEquiv : (Fin 3 → Real) → ((Real × Real) × Real))
      volume volume := by
  exact coordE0_preserving.trans (coordProduct_preserving.trans coordSwap_preserving)

theorem coordinateNestedEquiv_apply (x : Fin 3 → Real) :
    coordinateNestedEquiv x = ((x 0, x 1), x 2) := by
  have hrem : Fin.removeNth (2 : Fin 3) x = (fun i => ![x 0, x 1] i) := by
    funext i
    fin_cases i <;> rfl
  simp [coordinateNestedEquiv, coordE0, coordE1, MeasurableEquiv.trans_apply,
    MeasurableEquiv.piFinSuccAbove_apply, MeasurableEquiv.prodCongr,
    MeasurableEquiv.prodComm, Equiv.prodCongr, Equiv.prodComm_apply, hrem]

end

end PrimesRestrictedDigits
