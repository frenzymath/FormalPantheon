import PrimesRestrictedDigits.BasicEstimates.CayleyLogUpper
/-! # SectionSixFirstLowCentralLargeBelowCertificateNodes -/

namespace PrimesRestrictedDigits

noncomputable section

noncomputable def
    sectionSixFirstLowCentralLargeBelowTransformedIntegrand
    (logFunction : Real -> Real) (branch : Fin 2)
    (x y : Real) : Real :=
  let theta : Real := 180001 / 500000
  let complement : Real := 319999 / 500000
  let start : Real := 69999 / 250000
  let span : Real := 40003 / 500000
  let u := start + span * x
  let v :=
    if branch = 0 then
      theta / 2 - span * x * (2 - y) / 4
    else
      theta / 2 - span * x * (1 - y) / 4
  let rest := 1 - u - v
  let ratio :=
    if branch = 0 then
      2 * (theta - v) / (complement - u)
    else
      (theta - v) * (1 - u - 2 * v) /
        (v * (complement - u))
  let middle :=
    if branch = 0 then
      (564663 / 1000000 : Real) / (u * v) *
        (1 / v - 3 / rest)
    else 0
  x * (middle + logFunction ratio / (u * v * rest))

noncomputable def sectionSixFirstLowCentralLargeBelowCertificateNode
    (index : Fin 2 × Fin 29 × Fin 7) : Real :=
  let i := index.2.1.val
  let j := index.2.2.val
  let x : Real := (i : Real) / 28
  let y : Real := (j : Real) / 6
  let xWeight : Real :=
    if i = 0 ∨ i = 28 then 1 / 2 else 1
  let yWeight : Real :=
    if j = 0 ∨ j = 6 then 1 / 2 else 1
  (40003 / 500000 : Real) ^ 2 / (4 * 28 * 6) *
    xWeight * yWeight *
      sectionSixFirstLowCentralLargeBelowTransformedIntegrand
        (fun ratio =>
          cayleyLogSeriesUpper ((ratio - 1) / (ratio + 1)) 5)
        index.1 x y

end

end PrimesRestrictedDigits
