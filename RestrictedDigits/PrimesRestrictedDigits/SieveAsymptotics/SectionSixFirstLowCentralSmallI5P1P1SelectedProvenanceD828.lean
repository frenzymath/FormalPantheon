import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1D814P0RowPolynomial
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1TransformedGeometryD807
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1P1SelectedProvenanceD828 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/- The selected P1 row formula is expressed in terms of the Q4 primitive
and the affine walls. -/
def sectionSixFirstLowCentralSmallI5P1D828P1SelectedCoeff : Fin 11 -> Real := ![
  (-2181038248834433473326343247640104190282940720630039533800320772023073644544 /
    7687576268145503189170485244083885101802313524728674538361500622221421182175 : Real),
  (5122629324211039498700647015649538222843264923910150593634869282381824000000 /
    307503050725820127566819409763355404072092540989146981534460024888856847287 : Real),
  (-37636847489284285367196142501205199748046831227739051392625649664000000000000 /
    102501016908606709188939803254451801357364180329715660511486674962952282429 : Real),
  (1529244406964969564578892782910965176053921186888399335849984000000000000000000 /
    307503050725820127566819409763355404072092540989146981534460024888856847287 : Real),
  (-699718520697466520102039447056450734796996778232119296000000000000000000000000 /
    14643002415515244169848543322064543051052025761387951501640953566136040347 : Real),
  (1657417146363773305524798408729081542244022584606720000000000000000000000000000 /
    4881000805171748056616181107354847683684008587129317167213651188712013449 : Real),
  (-77767871391497645583394611535063840666419200000000000000000000000000000000000000 /
    43929007246545732509545629966193629153156077284163854504922860698408121041 : Real),
  (668895398125868843474115216102467305472000000000000000000000000000000000000000000 /
    102501016908606709188939803254451801357364180329715660511486674962952282429 : Real),
  (-1647038305921804011901867010293760000000000000000000000000000000000000000000000000 /
    102501016908606709188939803254451801357364180329715660511486674962952282429 : Real),
  (2444939691438546459973124096000000000000000000000000000000000000000000000000000000 /
    102501016908606709188939803254451801357364180329715660511486674962952282429 : Real),
  (-5100132743069124693852160000000000000000000000000000000000000000000000000000000000 /
    307503050725820127566819409763355404072092540989146981534460024888856847287 : Real)]

def sectionSixFirstLowCentralSmallI5P1D828FinPoly
    {n : Nat} (c : Fin n -> Real) (x : Real) : Real :=
  ∑ i : Fin n, c i * x ^ (i : Nat)

def sectionSixFirstLowCentralSmallI5P1D828QCoeff
    (a : Real) (i : Nat) : Real :=
  (-1 : Real) ^ i / a ^ (i + 1)

def sectionSixFirstLowCentralSmallI5P1D828P1SelectedFormula
    (a d : Real) : Real :=
  let l := sectionSixFirstLowCentralSmallI5P1D807A - 2 * d
  let m := l / 2
  let h := (sectionSixFirstLowCentralSmallI5P1D807Square -
      sectionSixFirstLowCentralSmallI5P1D807Beta - d) / 2
  (sectionSixFirstLowCentralSmallI5P1D814Q4Primitive a m) ^ 2 / 2 +
    ∑ i ∈ Finset.range 5,
      (∑ j ∈ Finset.range 5,
        (∑ k ∈ Finset.range (j + 2),
          (sectionSixFirstLowCentralSmallI5P1D828QCoeff a i *
              sectionSixFirstLowCentralSmallI5P1D828QCoeff a j *
            (j + 1 : Nat).choose k * (-1 : Real) ^ k /
              ((j + 1 : Real) * (i + k + 1 : Real))) *
            l ^ (j + 1 - k) *
              (h ^ (i + k + 1) - m ^ (i + k + 1))))

def sectionSixFirstLowCentralSmallI5P1D828P1SelectedCrossPoly
    (d : Real) : Real :=
  sectionSixFirstLowCentralSmallI5P1D828FinPoly
    sectionSixFirstLowCentralSmallI5P1D828P1SelectedCoeff d

def sectionSixFirstLowCentralSmallI5P1D828P1SelectedAnchor : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Ds +
    (sectionSixFirstLowCentralSmallI5P1D807Dr -
      sectionSixFirstLowCentralSmallI5P1D807Ds) / 256

theorem sectionSixFirstLowCentralSmallI5P1D828_p1SelectedAnchor_value :
    sectionSixFirstLowCentralSmallI5P1D828P1SelectedAnchor =
      18571667 / 128000000 := by
  norm_num [sectionSixFirstLowCentralSmallI5P1D828P1SelectedAnchor,
    sectionSixFirstLowCentralSmallI5P1D807Ds,
    sectionSixFirstLowCentralSmallI5P1D807Dr,
    sectionSixFirstLowCentralSmallI5P1D807A,
    sectionSixFirstLowCentralSmallI5P1D807Beta,
    sectionSixFirstLowCentralSmallI5P1D807Square,
    sectionSixFirstLowCentralSmallI5P1D807Delta,
    sectionSixThetaOne, sectionSixThetaTwo]

theorem sectionSixFirstLowCentralSmallI5P1D828_p1SelectedVector_eq_formula
    (d : Real) :
    sectionSixFirstLowCentralSmallI5P1D828P1SelectedCrossPoly d =
      sectionSixFirstLowCentralSmallI5P1D828P1SelectedFormula
        sectionSixFirstLowCentralSmallI5P1D828P1SelectedAnchor d := by
  norm_num [sectionSixFirstLowCentralSmallI5P1D828P1SelectedCrossPoly,
    sectionSixFirstLowCentralSmallI5P1D828FinPoly,
    sectionSixFirstLowCentralSmallI5P1D828P1SelectedCoeff,
    sectionSixFirstLowCentralSmallI5P1D828P1SelectedFormula,
    sectionSixFirstLowCentralSmallI5P1D828QCoeff,
    sectionSixFirstLowCentralSmallI5P1D828P1SelectedAnchor,
    sectionSixFirstLowCentralSmallI5P1D807Ds,
    sectionSixFirstLowCentralSmallI5P1D807Dr,
    sectionSixFirstLowCentralSmallI5P1D807A,
    sectionSixFirstLowCentralSmallI5P1D807Beta,
    sectionSixFirstLowCentralSmallI5P1D807Square,
    sectionSixFirstLowCentralSmallI5P1D807Delta,
    sectionSixThetaOne, sectionSixThetaTwo,
    sectionSixFirstLowCentralSmallI5P1D814Q4Primitive,
    Fin.sum_univ_succ, Finset.sum_range_succ, Nat.choose]
  field_simp
  ring


end
end PrimesRestrictedDigits
