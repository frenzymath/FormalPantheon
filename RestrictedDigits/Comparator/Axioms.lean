import Comparator.Solution

/-!
Axiom dependencies of the quantitative theorem, its comparison equivalence,
and the infinitude corollary.
-/

set_option autoImplicit false
set_option warningAsError true

set_option linter.hashCommand false in
/-- info: 'PrimesRestrictedDigits.mainTheorem' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrimesRestrictedDigits.mainTheorem

set_option linter.hashCommand false in
/-- info: 'PrimesRestrictedDigits.infinitude' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrimesRestrictedDigits.infinitude

set_option linter.hashCommand false in
/-- info: 'PrimesRestrictedDigits.quantitativeTheorem_iff_paperStrictComparableOn'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrimesRestrictedDigits.quantitativeTheorem_iff_paperStrictComparableOn

set_option linter.hashCommand false in
/-- info: 'PrimesRestrictedDigits.Comparator.mainTheorem' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrimesRestrictedDigits.Comparator.mainTheorem

set_option linter.hashCommand false in
/-- info: 'PrimesRestrictedDigits.Comparator.infinitude' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrimesRestrictedDigits.Comparator.infinitude
