import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option maxRecDepth 100000

noncomputable section

/-!
# Exact small-k certificate for Maynard's `M_105 > 4`

Maynard2013v3, source lines 665--790, reduces the `k = 105` choice to two
rational quadratic forms in the 42 monomials `(1-P₁)^b P₂^c` with
`b + 2c ≤ 11`. The archived ancillary notebook is
`references/primary/arXiv-1311.4600v3-source/anc/Computations.nb`.

This file records the exact formula data and a reduced rational candidate. The
notebook's decimal eigenvalue is provenance, not a proof input. The formula-
to-candidate bridge remains a separate proof obligation.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def smallKExponentB : Fin 42 → ℕ := fun i => match i.1 with
  | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 3 | 6 => 0
  | 7 => 2 | 8 => 4 | 9 => 1 | 10 => 3 | 11 => 5 | 12 => 0 | 13 => 2
  | 14 => 4 | 15 => 6 | 16 => 1 | 17 => 3 | 18 => 5 | 19 => 7 | 20 => 0
  | 21 => 2 | 22 => 4 | 23 => 6 | 24 => 8 | 25 => 1 | 26 => 3 | 27 => 5
  | 28 => 7 | 29 => 9 | 30 => 0 | 31 => 2 | 32 => 4 | 33 => 6 | 34 => 8
  | 35 => 10 | 36 => 1 | 37 => 3 | 38 => 5 | 39 => 7 | 40 => 9 | 41 => 11
  | _ => 0

def smallKExponentC : Fin 42 → ℕ := fun i => match i.1 with
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 0 | 4 => 1 | 5 => 0 | 6 => 2
  | 7 => 1 | 8 => 0 | 9 => 2 | 10 => 1 | 11 => 0 | 12 => 3 | 13 => 2
  | 14 => 1 | 15 => 0 | 16 => 3 | 17 => 2 | 18 => 1 | 19 => 0 | 20 => 4
  | 21 => 3 | 22 => 2 | 23 => 1 | 24 => 0 | 25 => 4 | 26 => 3 | 27 => 2
  | 28 => 1 | 29 => 0 | 30 => 5 | 31 => 4 | 32 => 3 | 33 => 2 | 34 => 1
  | 35 => 0 | 36 => 5 | 37 => 4 | 38 => 3 | 39 => 2 | 40 => 1 | 41 => 0
  | _ => 0

def smallKCoefficient : Fin 42 → ℚ := fun i => match i.1 with
  | 0 => -149 | 1 => -78365 | 2 => 35758 | 3 => -831891
  | 4 => 18186528 | 5 => -5576809 | 6 => -3506164 | 7 => 253091917
  | 8 => 2476996720 | 9 => -1697864367 | 10 => -3262477720
  | 11 => -6562118242 | 12 => 177457913 | 13 => -26629971689
  | 14 => -468868448020 | 15 => -325069016539 | 16 => 80537615942
  | 17 => 690191211846 | 18 => 2221700399033 | 19 => 870938285189
  | 20 => -4687324321 | 21 => 1194767370240 | 22 => 30262960788018
  | 23 => 44860090002074 | 24 => 6699008013029 | 25 => -1967874113811
  | 26 => -43513693791234 | 27 => -209219127709955
  | 28 => -110727707057853 | 29 => 29792838249425 | 30 => 51991283212
  | 31 => -19832587096191 | 32 => -687944325912208
  | 33 => -1947235482160893 | 34 => -1432457536147492
  | 35 => -371139909644199 | 36 => 20143295340893 | 37 => 923345761873697
  | 38 => 7007345831825894 | 39 => 10000000000000000
  | 40 => 4377898334267940 | 41 => 683828398233656 | _ => 0

theorem smallK_exponent_bound (i : Fin 42) :
    smallKExponentB i + 2 * smallKExponentC i ≤ 11 := by
  fin_cases i <;> decide

theorem smallK_exponents_injective : Function.Injective (fun i : Fin 42 =>
    (smallKExponentB i, smallKExponentC i)) := by
  decide

def smallKAllowedExponentPairs : Finset (ℕ × ℕ) :=
  (((List.range 12).flatMap fun b =>
    (List.range 6).filter (fun c => b + 2 * c ≤ 11) |>.map (fun c => (b, c)))).toFinset

def smallKExponentPairs : Finset (ℕ × ℕ) :=
  Finset.univ.image (fun i : Fin 42 => (smallKExponentB i, smallKExponentC i))

theorem smallK_allowedExponentPairs_card :
    smallKAllowedExponentPairs.card = 42 := by
  decide

theorem smallK_allowedExponentPairs_eq_exponentPairs :
    smallKAllowedExponentPairs = smallKExponentPairs := by
  decide

def smallKG105 (c : ℕ) : ℚ :=
  if h : c < 11 then
    (![1, 210, 46200, 10646160, 2569472640, 649565763840,
      172039896806400, 47758733442201600, 13906217329385472000,
      4251952625998204108800, 1367542144912926611865600] : Fin 11 → ℚ)
      ⟨c, h⟩
  else 0

def smallKG104 (c : ℕ) : ℚ :=
  if h : c < 11 then
    (![1, 208, 45344, 10358400, 2479436544, 621913344000,
      163502746767360, 45074911052021760, 13040192296300216320,
      3963497946537236889600, 1267924969103825829888000] : Fin 11 → ℚ)
      ⟨c, h⟩
  else 0

def smallKPositiveCompositions : ℕ → ℕ → List (List ℕ)
  | total, 0 => if total = 0 then [[]] else []
  | total, parts + 1 =>
      (List.range total).flatMap fun offset =>
        (smallKPositiveCompositions (total - (offset + 1)) parts).map
          fun tail => (offset + 1) :: tail

def smallKCompositionWeight (composition : List ℕ) : ℕ :=
  (composition.map fun q => Nat.factorial (2 * q) / Nat.factorial q).prod

def smallKGFormula (b k : ℕ) : ℕ :=
  if b = 0 then 1 else
    Nat.factorial b * ∑ r ∈ Finset.range (b + 1),
      Nat.choose k r * ((smallKPositiveCompositions b r).map
        smallKCompositionWeight).sum

theorem smallKG105_eq_formula (b : Fin 11) :
    (smallKGFormula b.1 105 : ℚ) = smallKG105 b.1 := by
  fin_cases b <;> decide

theorem smallKG104_eq_formula (b : Fin 11) :
    (smallKGFormula b.1 104 : ℚ) = smallKG104 b.1 := by
  fin_cases b <;> decide

def smallKSimplexMoment (b c : ℕ) : ℚ :=
  (Nat.factorial b : ℚ) / Nat.factorial (105 + b + 2 * c) * smallKG105 c

def smallKFaceMoment (b c : ℕ) : ℚ :=
  ∑ cp ∈ Finset.range (c + 1),
    ∑ dp ∈ Finset.range (c + 1),
      ((Nat.choose c cp : ℚ) * Nat.factorial b *
          Nat.factorial (2 * c - 2 * cp) /
        Nat.factorial (b + 2 * c - 2 * cp + 1)) *
      ((Nat.choose c dp : ℚ) * Nat.factorial b *
          Nat.factorial (2 * c - 2 * dp) /
        Nat.factorial (b + 2 * c - 2 * dp + 1)) *
      ((Nat.factorial (b + 2 * c - 2 * cp + 1 +
            b + 2 * c - 2 * dp + 1) : ℚ) /
        Nat.factorial (104 + b + 2 * c - 2 * cp + 1 +
          b + 2 * c - 2 * dp + 1 + 2 * (cp + dp))) *
      smallKG104 (cp + dp)

def smallKDenominator : ℚ :=
  ∑ i : Fin 42, ∑ j : Fin 42,
    smallKCoefficient i * smallKCoefficient j *
      smallKSimplexMoment (smallKExponentB i + smallKExponentB j)
        (smallKExponentC i + smallKExponentC j)

def smallKNumerator : ℚ :=
  105 * ∑ i : Fin 42, ∑ j : Fin 42,
    smallKCoefficient i * smallKCoefficient j *
      (∑ cp ∈ Finset.range (smallKExponentC i + 1),
        ∑ dp ∈ Finset.range (smallKExponentC j + 1),
          ((Nat.choose (smallKExponentC i) cp : ℚ) *
              Nat.factorial (smallKExponentB i) *
              Nat.factorial (2 * smallKExponentC i - 2 * cp) /
            Nat.factorial (smallKExponentB i + 2 * smallKExponentC i -
              2 * cp + 1)) *
          ((Nat.choose (smallKExponentC j) dp : ℚ) *
              Nat.factorial (smallKExponentB j) *
              Nat.factorial (2 * smallKExponentC j - 2 * dp) /
            Nat.factorial (smallKExponentB j + 2 * smallKExponentC j -
              2 * dp + 1)) *
          ((Nat.factorial (smallKExponentB i + 2 * smallKExponentC i -
                2 * cp + 1 + smallKExponentB j +
                2 * smallKExponentC j - 2 * dp + 1) : ℚ) /
            Nat.factorial (104 + smallKExponentB i +
              2 * smallKExponentC i - 2 * cp + 1 +
              smallKExponentB j + 2 * smallKExponentC j - 2 * dp + 1 +
              2 * (cp + dp))) *
          smallKG104 (cp + dp))

def smallKRatio : ℚ := smallKNumerator / smallKDenominator

/-!
The following rationals are obtained by exact external evaluation of the two
finite forms for the displayed vector. The generated denominator and numerator
certificate modules later identify them with the source definitions.
-/
def smallKCertifiedDenominator : ℚ :=
  717925066638124529331257006089092719 /
    2451248164740910499849772609226564764811979767297255439425749694569031705322668225961296532190842784629902485189695782477370044660526975491024494920875993463050130382284390400000000000000000000000000000

def smallKCertifiedNumerator : ℚ :=
  677977864881105590962037843453625145051 /
    578461774261266370800668746846242173261315359132088106374183606852143401764439699076351449201959421015003074765835901042151272077748439433600964420123779594491027423993266176000000000000000000000000000000

def smallKCertifiedRatio : ℚ :=
  202715381599450571697649315192633918370249 /
    50656792701986066789613494349646382252640

theorem smallK_certified_denominator_pos : 0 < smallKCertifiedDenominator := by
  norm_num [smallKCertifiedDenominator]

theorem smallK_certified_numerator_pos : 0 < smallKCertifiedNumerator := by
  norm_num [smallKCertifiedNumerator]

theorem smallK_certified_quotient_eq_ratio :
    smallKCertifiedNumerator / smallKCertifiedDenominator =
      smallKCertifiedRatio := by
  norm_num [smallKCertifiedNumerator, smallKCertifiedDenominator,
    smallKCertifiedRatio]

theorem smallK_certified_ratio_gt_four : 4 < smallKCertifiedRatio := by
  norm_num [smallKCertifiedRatio]

end BoundedGaps.Maynard
