import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
/-! # SectionSixFirstLowCentralLargeAboveCertificateNodes -/

namespace PrimesRestrictedDigits

noncomputable section

noncomputable def
    sectionSixFirstLowCentralLargeAboveTransformedIntegrand
    (logFunction : Real -> Real) (cell : Fin 5)
    (x y : Real) : Real :=
  let alpha : Real := 180001 / 500000
  let beta : Real := 212499 / 500000
  let gamma : Real := 287501 / 500000
  let sigma : Real := 319999 / 500000
  let d : Real := 37501 / 250000
  let h : Real := 43 / 200
  let u0 : Real := 470003 / 1500000
  let uLower : Real :=
    match cell.val with
    | 0 => h
    | 1 => u0
    | 2 => sigma / 3
    | 3 => h
    | _ => 1 / 4
  let uUpper : Real :=
    match cell.val with
    | 0 => u0
    | 1 => alpha
    | 2 => h
    | 3 => 1 / 4
    | _ => alpha
  let vLower : Real -> Real := fun u =>
    match cell.val with
    | 0 => (sigma - u) / 2
    | 1 => u - d
    | 2 => (sigma - u) / 2
    | _ => beta / 2
  let vUpper : Real -> Real := fun u =>
    match cell.val with
    | 0 => beta / 2
    | 1 => beta / 2
    | 2 => u
    | 3 => u
    | _ => (1 - u) / 3
  let isA := cell.val < 2
  let u := uLower + (uUpper - uLower) * x
  let rLower :=
    if isA then (gamma - u) / (beta - vLower u)
    else (1 - u) / vUpper u - 2
  let rUpper :=
    if isA then (gamma - u) / (beta - vUpper u)
    else (1 - u) / vLower u - 2
  let r := rLower + (rUpper - rLower) * y
  let reduced :=
    if isA then
      logFunction r / (u * (r + 1) * (u + beta * r - gamma))
    else
      logFunction r / (u * (1 - u) * (r + 1))
  (uUpper - uLower) * (rUpper - rLower) * reduced

noncomputable def sectionSixFirstLowCentralLargeAboveCertificateNode
    (index :
      ((Fin 2 × Fin 15 × Fin 5) ⊕ (Fin 2 × Fin 2)) ⊕
        (Fin 2 × Fin 16 × Fin 5)) : Real :=
  let tightLog : Real -> Real := fun r =>
    let z := (r - 1) / (r + 1)
    2 * (z + z ^ 3 / (3 * (1 - z ^ 2)))
  match index with
  | Sum.inl (Sum.inl (branch, i, j)) =>
      let cell : Fin 5 := if branch = 0 then 0 else 3
      sectionSixFirstLowCentralLargeAboveTransformedIntegrand
          tightLog cell
          ((2 * (i.val : Real) + 1) / (2 * 15))
          ((2 * (j.val : Real) + 1) / (2 * 5)) /
        ((15 : Real) * 5)
  | Sum.inl (Sum.inr (i, j)) =>
      sectionSixFirstLowCentralLargeAboveTransformedIntegrand
          tightLog (2 : Fin 5)
          ((2 * (i.val : Real) + 1) / (2 * 2))
          ((2 * (j.val : Real) + 1) / (2 * 2)) /
        ((2 : Real) * 2)
  | Sum.inr (branch, i, j) =>
      let cell : Fin 5 := if branch = 0 then 1 else 4
      let xWeight : Real :=
        if i.val = 0 ∨ i.val = 15 then 1 / 2 else 1
      xWeight *
          sectionSixFirstLowCentralLargeAboveTransformedIntegrand
            tightLog cell ((i.val : Real) / 15)
              ((2 * (j.val : Real) + 1) / (2 * 5)) /
        ((15 : Real) * 5)

noncomputable def sectionSixFirstLowCentralLargeAboveReducedCellIntegral
    (logFunction : Real -> Real) (cell : Fin 5) : Real :=
  let alpha : Real := 180001 / 500000
  let beta : Real := 212499 / 500000
  let gamma : Real := 287501 / 500000
  let sigma : Real := 319999 / 500000
  let d : Real := 37501 / 250000
  let h : Real := 43 / 200
  let u0 : Real := 470003 / 1500000
  let uLower : Real :=
    match cell.val with
    | 0 => h
    | 1 => u0
    | 2 => sigma / 3
    | 3 => h
    | _ => 1 / 4
  let uUpper : Real :=
    match cell.val with
    | 0 => u0
    | 1 => alpha
    | 2 => h
    | 3 => 1 / 4
    | _ => alpha
  let vLower : Real -> Real := fun u =>
    match cell.val with
    | 0 => (sigma - u) / 2
    | 1 => u - d
    | 2 => (sigma - u) / 2
    | _ => beta / 2
  let vUpper : Real -> Real := fun u =>
    match cell.val with
    | 0 => beta / 2
    | 1 => beta / 2
    | 2 => u
    | 3 => u
    | _ => (1 - u) / 3
  ∫ u in uLower..uUpper,
    ∫ v in vLower u..vUpper u,
      logFunction
          (if cell.val < 2 then (gamma - u) / (beta - v)
           else (1 - u - 2 * v) / v) /
        (u * v * (1 - u - v))

end

end PrimesRestrictedDigits
