import Waring.Certificate.Reachability

/-!
# Finite fifth-power coverage certificates

The closed equalities in this file are recomputed by ordinary kernel reduction,
without a generated-code evaluator or an external witness table.
-/

namespace Waring.Certificate

open Waring

set_option exponentiation.threshold 5000000
set_option maxRecDepth 5000000

/-- The cap used by the finite fifth-power reachability certificate. -/
def fifthPowerCertificateCap : Nat := 4219059

/-- Kernel-checked packed coverage by fifteen fifth-power slots. -/
theorem fifthPowerReachability_fifteen_coverage :
    powerReachability 5 fifthPowerCertificateCap 22 15 &&&
        intervalMask 470348 fifthPowerCertificateCap =
      intervalMask 470348 fifthPowerCertificateCap := by
  decide

/-- Kernel-checked packed coverage by twelve fifth-power slots. -/
theorem fifthPowerReachability_twelve_coverage :
    powerReachability 5 fifthPowerCertificateCap 22 12 &&&
        intervalMask 2103307 fifthPowerCertificateCap =
      intervalMask 2103307 fifthPowerCertificateCap := by
  decide

/-- Kernel-checked 37-slot coverage below Dickson's recurrence threshold. -/
theorem fifthPowerReachability_thirtySeven_small_coverage :
    powerReachability 5 fifthPowerCertificateCap 22 37 &&&
        intervalMask 0 470347 = intervalMask 0 470347 := by
  decide

/-- Every target from 470348 through the certificate cap is represented by
fifteen fifth-power slots. -/
theorem fifteenPowerBaseCoverage :
    RepresentsOn 5 15 470348 fifthPowerCertificateCap :=
  representsOn_of_reachabilityMask fifthPowerReachability_fifteen_coverage

/-- Every target from 2103307 through the certificate cap is represented by
twelve fifth-power slots. -/
theorem twelvePowerBaseCoverage :
    RepresentsOn 5 12 2103307 fifthPowerCertificateCap :=
  representsOn_of_reachabilityMask fifthPowerReachability_twelve_coverage

/-- Every target below 470348 is represented by 37 fifth-power slots. -/
theorem thirtySevenSmallCoverage : RepresentsOn 5 37 0 470347 :=
  representsOn_of_reachabilityMask
    fifthPowerReachability_thirtySeven_small_coverage

end Waring.Certificate
