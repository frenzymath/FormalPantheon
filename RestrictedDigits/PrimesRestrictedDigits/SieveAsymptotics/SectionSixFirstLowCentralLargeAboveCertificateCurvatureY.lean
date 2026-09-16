import PrimesRestrictedDigits.BasicEstimates.TensorBernsteinNonnegative
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateNodes
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! Exact vertical-curvature certificates for the five upper `I_4` charts. -/
open Set
open scoped Polynomial
namespace PrimesRestrictedDigits
noncomputable section
open Polynomial (C X)
private def ratioSpan : Rat := 147503 / 212499
private def uSpan : Rat := 72501 / 500000
private def aCoefficientScale : Rat := 1 / 543495226107951381618080214544312152750000000000
private def aCoefficientNumerator : Nat -> Nat -> Nat
  | 0, 0 => 239280248459070027584131537201297601626104211190784 | 0, 1 => 343888885658834221124235796409052480835904387844096
  | 0, 2 => 487320124154323216934179638337755536578043775279936 | 0, 3 => 677082637910405155987759322079646117090912093094784
  | 0, 4 => 915972561643297446461728357380415377193559671299744 | 0, 5 => 1194776264064961729429498392252025702052771161102080
  | 0, 6 => 1479077286273917205344504483172962249872611528917196 | 0, 7 => 1686642788567176987632034778246898806419252859574840
  | 0, 8 => 1650341099028723360761174521799137924862274861213264 | 0, 9 => 1059753785281198381764106151161570987098142052907560
  | 1, 0 => 541594494881686697708247541583278330114943364474624 | 1, 1 => 772447962780666703320950584699508173090454364162816
  | 1, 2 => 1087680237879436178608839776617211739303466053559728 | 1, 3 => 1508615346185980678230586915766969564645078454769728
  | 1, 4 => 2055020267209101926392220260743125087407660359891000 | 1, 5 => 2738135137577345864993405440305439943380041356675784
  | 1, 6 => 3547696605330744897097634002592808749684722218432405 | 1, 7 => 4429375066717833714589449147775182109416779751000474
  | 1, 8 => 5247522767411109309934688066478224349712526556160596 | 1, 9 => 5726341578085366333555312168586618168560496259392408
  | 2, 0 => 1001879769105785421207512895926144730750446979836928 | 2, 1 => 1401620988271088234751347542705547372694696199041792
  | 2, 2 => 1941340059022156502016558101925968612818201881039744 | 2, 3 => 2658037062816966594954954356006452897685012679033072
  | 2, 4 => 3590510631217182306433167574887910868627609348053536 | 2, 5 => 4772702952691204089398461163553819529210559434683984
  | 2, 6 => 6220919246263118853532031335698786340302636272598588 | 2, 7 => 7911287822397764430797256871626292513963945943620686
  | 2, 8 => 9742303101592834032343206896565308557922990230527168 | 2, 9 => 11475505789180206580819307477866860785103103676380832
  | _, _ => 0
private def bCoefficientScale : Rat := 8 / 7307533226817892677385106545635
private def bCoefficientNumerator : Nat -> Nat -> Nat
  | 0, 0 => 12627417415941318546521464110857280 | 0, 1 => 17740411538943131169550626854057040
  | 0, 2 => 24780064472490955233219677146320048 | 0, 3 => 34371064752944768379297643704240042
  | 0, 4 => 47272461484653403554593589231728412 | 0, 5 => 64356467890623600155091063958371690
  | 0, 6 => 86535768670125462768219138883760395
  | _, _ => 0
private def aCoefficient (i j : Nat) : Rat := aCoefficientScale * aCoefficientNumerator i j
private def bCoefficient (i j : Nat) : Rat := bCoefficientScale * bCoefficientNumerator i j
private theorem aCoefficient_nonneg :
    ∀ i ≤ 2, ∀ j ≤ 9, 0 ≤ aCoefficient i j := by
  intro i hi j hj; interval_cases i
  all_goals interval_cases j <;> norm_num [aCoefficient, aCoefficientScale, aCoefficientNumerator]
private theorem bCoefficient_nonneg :
    ∀ i ≤ 0, ∀ j ≤ 6, 0 ≤ bCoefficient i j := by
  intro i hi j hj; interval_cases i
  interval_cases j <;> norm_num [bCoefficient, bCoefficientScale, bCoefficientNumerator]
private noncomputable def ratioNumerator : Polynomial Real := (X - 1) * (X ^ 2 + 10 * X + 1)
private noncomputable def aDenominator (u : Real) : Polynomial Real :=
  6 * X * (X + 1) ^ 2 * (C u + C (212499 / 500000 : Real) * X - C (287501 / 500000 : Real))
private noncomputable def bDenominator : Polynomial Real := 6 * X * (X + 1) ^ 2
private noncomputable def quotientNegativeSecondNumerator
    (p q : Polynomial Real) (r : Real) : Real :=
  -(p.derivative.derivative.eval r * q.eval r ^ 2
      - 2 * p.derivative.eval r * q.eval r * q.derivative.eval r
      + 2 * p.eval r * q.derivative.eval r ^ 2
      - p.eval r * q.eval r * q.derivative.derivative.eval r)
private theorem ratioNumerator_eval (r : Real) : ratioNumerator.eval r =
    (r - 1) * (r ^ 2 + 10 * r + 1) := by simp [ratioNumerator]
private theorem aDenominator_eval (u r : Real) :
    (aDenominator u).eval r =
      6 * r * (r + 1) ^ 2 *
        (u + (212499 / 500000) * r - 287501 / 500000) := by simp [aDenominator]
private theorem bDenominator_eval (r : Real) : bDenominator.eval r =
    6 * r * (r + 1) ^ 2 := by simp [bDenominator]
private theorem aCertificate_eval (x y : Real) :
    Polynomial.eval₂
        (Polynomial.eval₂RingHom (algebraMap Rat Real) x) y
        (tensorBernsteinPolynomial 2 9 aCoefficient) =
      quotientNegativeSecondNumerator ratioNumerator
        (aDenominator (43 / 200 + (uSpan : Real) * x))
        (1 + (ratioSpan : Real) * y) := by
  rw [tensorBernsteinPolynomial]
  repeat rw [Finset.sum_range_succ]
  norm_num [Nat.choose, aCoefficient, aCoefficientScale, aCoefficientNumerator,
    quotientNegativeSecondNumerator, ratioNumerator, aDenominator, ratioSpan, uSpan,
    bernsteinPolynomial, Polynomial.derivative_pow, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
    Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_one]
  ring
private theorem bCertificate_eval (y : Real) :
    Polynomial.eval₂
        (Polynomial.eval₂RingHom (algebraMap Rat Real) 0) y
        (tensorBernsteinPolynomial 0 6 bCoefficient) =
      quotientNegativeSecondNumerator ratioNumerator bDenominator
        (1 + (ratioSpan : Real) * y) := by
  rw [tensorBernsteinPolynomial]
  repeat rw [Finset.sum_range_succ]
  norm_num [Nat.choose, bCoefficient, bCoefficientScale, bCoefficientNumerator,
    quotientNegativeSecondNumerator, ratioNumerator, bDenominator, ratioSpan,
    bernsteinPolynomial, Polynomial.derivative_pow, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
    Polynomial.eval₂_sub,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_one]
  ring
private theorem aNegativeSecondNumerator_nonneg
    {u r : Real} (hu : u ∈ Icc (43 / 200 : Real) (180001 / 500000))
    (hr : r ∈ Icc (1 : Real) (360002 / 212499)) :
    0 <= quotientNegativeSecondNumerator ratioNumerator (aDenominator u) r := by
  let x : Real := (u - 43 / 200) / (uSpan : Real)
  let y : Real := (r - 1) / (ratioSpan : Real)
  have huspan : (0 : Real) < uSpan := by norm_num [uSpan]
  have hrspan : (0 : Real) < ratioSpan := by norm_num [ratioSpan]
  have hx0 : 0 <= x := div_nonneg (sub_nonneg.mpr hu.1) huspan.le
  have hx1 : x <= 1 := by
    rw [div_le_one huspan]
    norm_num [uSpan] at hu ⊢
    linarith
  have hy0 : 0 <= y := div_nonneg (sub_nonneg.mpr hr.1) hrspan.le
  have hy1 : y <= 1 := by
    rw [div_le_one hrspan]
    norm_num [ratioSpan] at hr ⊢
    linarith
  have h := tensorBernsteinPolynomial_eval₂_nonneg
    (coefficient := aCoefficient) aCoefficient_nonneg hx0 hx1 hy0 hy1
  rw [aCertificate_eval] at h
  have hux : u = 43 / 200 + (uSpan : Real) * x := by
    dsimp [x]
    field_simp [huspan.ne']; ring
  have hry : r = 1 + (ratioSpan : Real) * y := by
    dsimp [y]
    field_simp [hrspan.ne']; ring
  rw [← hux, ← hry] at h
  exact h
private theorem bNegativeSecondNumerator_nonneg
    {r : Real} (hr : r ∈ Icc (1 : Real) (360002 / 212499)) :
    0 <= quotientNegativeSecondNumerator ratioNumerator bDenominator r := by
  let y : Real := (r - 1) / (ratioSpan : Real)
  have hrspan : (0 : Real) < ratioSpan := by norm_num [ratioSpan]
  have hy0 : 0 <= y := div_nonneg (sub_nonneg.mpr hr.1) hrspan.le
  have hy1 : y <= 1 := by
    rw [div_le_one hrspan]
    norm_num [ratioSpan] at hr ⊢
    linarith
  have h := tensorBernsteinPolynomial_eval₂_nonneg
    (coefficient := bCoefficient) bCoefficient_nonneg
    (x := (0 : Real)) (y := y) (by norm_num) (by norm_num) hy0 hy1
  rw [bCertificate_eval] at h
  have hry : r = 1 + (ratioSpan : Real) * y := by
    dsimp [y]
    field_simp [hrspan.ne']; ring
  rw [← hry] at h
  exact h
private theorem polynomialQuotient_concaveOn
    (p q : Polynomial Real) {a b : Real}
    (hq : ∀ r ∈ Icc a b, 0 < q.eval r)
    (hn : ∀ r ∈ Icc a b, 0 <= quotientNegativeSecondNumerator p q r) :
    ConcaveOn Real (Icc a b) (fun r => p.eval r / q.eval r) := by
  let f1 : Real -> Real := fun r => (p.derivative.eval r * q.eval r -
    p.eval r * q.derivative.eval r) / q.eval r ^ 2
  let f2 : Real -> Real := fun r => -quotientNegativeSecondNumerator p q r / q.eval r ^ 3
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := f1) (f'' := f2)
    (convex_Icc a b)
  · intro r hr
    have hp := Polynomial.hasDerivAt p r
    have hq0 := Polynomial.hasDerivAt q r
    exact (hp.continuousAt.div hq0.continuousAt (hq r hr).ne').continuousWithinAt
  · intro r hr
    have hmem := interior_subset hr
    have hp := Polynomial.hasDerivAt p r
    have hq0 := Polynomial.hasDerivAt q r
    exact ((hp.div hq0 (hq r hmem).ne').congr_deriv (by dsimp [f1])).hasDerivWithinAt
  · intro r hr
    have hmem := interior_subset hr
    have hqr := hq r hmem
    have hp := Polynomial.hasDerivAt p r
    have hpd := Polynomial.hasDerivAt p.derivative r
    have hq0 := Polynomial.hasDerivAt q r
    have hqd := Polynomial.hasDerivAt q.derivative r
    have hnum := (hpd.mul hq0).sub (hp.mul hqd)
    have hden := hq0.pow 2
    exact (hnum.div hden (pow_ne_zero 2 hqr.ne')).congr_deriv (by
      dsimp [f1, f2, quotientNegativeSecondNumerator]
      field_simp [hqr.ne']; ring) |>.hasDerivWithinAt
  · intro r hr
    have hmem := interior_subset hr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hn r hmem))
      (pow_nonneg (hq r hmem).le 3)
private noncomputable def aCore (u r : Real) : Real := ratioNumerator.eval r / (aDenominator u).eval r
private noncomputable def bCore (r : Real) : Real := ratioNumerator.eval r / bDenominator.eval r
private theorem aCore_concaveOn {u : Real}
    (hu : u ∈ Icc (43 / 200 : Real) (180001 / 500000)) :
    ConcaveOn Real (Icc (1 : Real) (360002 / 212499)) (aCore u) := by
  apply polynomialQuotient_concaveOn ratioNumerator (aDenominator u)
  · intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr.1
    have hr1 : 0 < r + 1 := by linarith
    have hlast : 0 < u + (212499 / 500000) * r - 287501 / 500000 := by
      norm_num at hu hr ⊢
      nlinarith [hu.1]
    rw [aDenominator_eval]
    exact mul_pos (mul_pos (mul_pos (by norm_num) hr0) (sq_pos_of_pos hr1)) hlast
  · exact fun r hr => aNegativeSecondNumerator_nonneg hu hr
private theorem bCore_concaveOn :
    ConcaveOn Real (Icc (1 : Real) (360002 / 212499)) bCore := by
  apply polynomialQuotient_concaveOn ratioNumerator bDenominator
  · intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr.1
    have hr1 : 0 < r + 1 := by linarith
    rw [bDenominator_eval]
    exact mul_pos (mul_pos (by norm_num) hr0) (sq_pos_of_pos hr1)
  · exact fun r hr => bNegativeSecondNumerator_nonneg hr
private theorem affineCore_concaveOn {f : Real -> Real} {r0 r1 c : Real}
    (hf : ConcaveOn Real (Icc (1 : Real) (360002 / 212499)) f)
    (hr0 : r0 ∈ Icc (1 : Real) (360002 / 212499))
    (hr1 : r1 ∈ Icc (1 : Real) (360002 / 212499)) (hc : 0 <= c) :
    ConcaveOn Real (Icc (0 : Real) 1)
      (fun y => c * f (r0 + (r1 - r0) * y)) := by
  have hcomp := hf.comp_affineMap (AffineMap.lineMap r0 r1)
  have hsubset : Icc (0 : Real) 1 ⊆
      (AffineMap.lineMap r0 r1) ⁻¹' Icc (1 : Real) (360002 / 212499) := by
    intro y hy
    exact (convex_Icc (1 : Real) (360002 / 212499)).lineMap_mem hr0 hr1 hy
  have h := hcomp.subset hsubset (convex_Icc (0 : Real) 1)
  refine (ConcaveOn.smul hc h).congr ?_
  intro y hy
  have harg : AffineMap.lineMap r0 r1 y = r0 + (r1 - r0) * y := by
    rw [AffineMap.lineMap_apply_ring']
    ring
  simp only [smul_eq_mul, Function.comp_apply, harg]
private def cellULower (cell : Fin 5) : Real := match cell.val with
  | 0 => 43 / 200 | 1 => 470003 / 1500000 | 2 => (319999 / 500000) / 3 | 3 => 43 / 200 | _ => 1 / 4
private def cellUUpper (cell : Fin 5) : Real := match cell.val with
  | 0 => 470003 / 1500000 | 1 => 180001 / 500000 | 2 => 43 / 200 | 3 => 1 / 4 | _ => 180001 / 500000
private def physicalU (cell : Fin 5) (x : Real) : Real := cellULower cell + (cellUUpper cell - cellULower cell) * x
private def chartRLower (cell : Fin 5) (u : Real) : Real :=
  match cell.val with
  | 0 => (287501 / 500000 - u) / (212499 / 500000 - (319999 / 500000 - u) / 2)
  | 1 => (287501 / 500000 - u) / (212499 / 500000 - (u - 37501 / 250000))
  | 2 => (1 - u) / u - 2 | 3 => (1 - u) / u - 2
  | _ => (1 - u) / ((1 - u) / 3) - 2
private def chartRUpper (cell : Fin 5) (u : Real) : Real :=
  match cell.val with
  | 0 => (287501 / 500000 - u) / (212499 / 500000 - (212499 / 500000) / 2)
  | 1 => (287501 / 500000 - u) / (212499 / 500000 - (212499 / 500000) / 2)
  | 2 => (1 - u) / ((319999 / 500000 - u) / 2) - 2
  | 3 => (1 - u) / ((212499 / 500000) / 2) - 2
  | _ => (1 - u) / ((212499 / 500000) / 2) - 2
private def chartScale (cell : Fin 5) (u : Real) : Real :=
  let base := (cellUUpper cell - cellULower cell) *
    (chartRUpper cell u - chartRLower cell u)
  if cell.val < 2 then base / u else base / (u * (1 - u))
private theorem div_mem_ratioIcc {n d : Real} (hd : 0 < d)
    (hlo : d <= n) (hhi : n <= (360002 / 212499) * d) :
    n / d ∈ Icc (1 : Real) (360002 / 212499) := by
  constructor
  · rw [le_div_iff₀ hd]
    simpa using hlo
  · exact (div_le_iff₀ hd).2 hhi
private theorem div_sub_two_mem_ratioIcc {n d : Real} (hd : 0 < d)
    (hlo : 3 * d <= n)
    (hhi : n <= (360002 / 212499 + 2) * d) :
    n / d - 2 ∈ Icc (1 : Real) (360002 / 212499) := by
  have hlo' := (le_div_iff₀ hd).2 hlo
  have hhi' := (div_le_iff₀ hd).2 hhi
  exact ⟨by linarith, by linarith⟩
private theorem physicalU_mem (cell : Fin 5) {x : Real}
    (hx : x ∈ Icc (0 : Real) 1) :
    physicalU cell x ∈ Icc (cellULower cell) (cellUUpper cell) := by
  rcases hx with ⟨hx0, hx1⟩
  fin_cases cell <;> norm_num [physicalU, cellULower, cellUUpper] at hx0 hx1 ⊢ <;>
    constructor <;> nlinarith
private theorem physicalU_mem_a (cell : Fin 5) {x : Real} (hx : x ∈ Icc (0 : Real) 1) (hcell : cell.val < 2) :
    physicalU cell x ∈ Icc (43 / 200 : Real) (180001 / 500000) := by
  rcases physicalU_mem cell hx with ⟨hu0, hu1⟩
  fin_cases cell <;> norm_num at hcell
  all_goals (norm_num [cellULower, cellUUpper] at hu0 hu1 ⊢; constructor <;> nlinarith)
private theorem chartFacts (cell : Fin 5) {x : Real} (hx : x ∈ Icc (0 : Real) 1) :
    let u := physicalU cell x
    u ∈ Icc (319999 / 1500000 : Real) (180001 / 500000) ∧
      chartRLower cell u ∈ Icc (1 : Real) (360002 / 212499) ∧
      chartRUpper cell u ∈ Icc (1 : Real) (360002 / 212499) ∧
      0 <= chartScale cell u := by
  let u := physicalU cell x
  have hu : u ∈ Icc (cellULower cell) (cellUUpper cell) := by
    simpa only [u] using physicalU_mem cell hx
  rcases hu with ⟨hu0, hu1⟩
  change u ∈ _ ∧ chartRLower cell u ∈ _ ∧
    chartRUpper cell u ∈ _ ∧ _
  fin_cases cell
  all_goals norm_num [cellULower, cellUUpper] at hu0 hu1
  · have hubroad : u ∈ Icc (319999 / 1500000 : Real) (180001 / 500000) :=
      ⟨by norm_num; nlinarith, by norm_num; nlinarith⟩
    have hl : chartRLower 0 u ∈ Icc (1 : Real) (360002 / 212499) := by
      apply div_mem_ratioIcc <;>
        norm_num [chartRLower] at hu0 hu1 ⊢ <;> nlinarith
    have hh : chartRUpper 0 u ∈ Icc (1 : Real) (360002 / 212499) := by
      apply div_mem_ratioIcc <;>
        norm_num [chartRUpper] at hu0 hu1 ⊢ <;> nlinarith
    have ho : chartRLower 0 u <= chartRUpper 0 u := by
      apply div_le_div_of_nonneg_left
      all_goals norm_num [chartRLower, chartRUpper] at hu0 hu1 ⊢ <;> nlinarith
    refine ⟨hubroad, hl, hh, ?_⟩
    change 0 <= ((cellUUpper 0 - cellULower 0) * (chartRUpper 0 u - chartRLower 0 u)) / u
    exact div_nonneg (mul_nonneg (by norm_num [cellULower, cellUUpper])
      (sub_nonneg.mpr ho)) (by nlinarith)
  · have hubroad : u ∈ Icc (319999 / 1500000 : Real) (180001 / 500000) := by
      exact ⟨by norm_num; nlinarith, hu1⟩
    have hd : 0 < 287501 / 500000 - u := by norm_num; nlinarith
    have hden : (212499 / 500000 - (u - 37501 / 250000) : Real) = 287501 / 500000 - u := by ring
    have hl : chartRLower 1 u = 1 := by
      change (287501 / 500000 - u) / (212499 / 500000 - (u - 37501 / 250000)) = 1
      rw [hden, div_self hd.ne']
    have hh : chartRUpper 1 u ∈ Icc (1 : Real) (360002 / 212499) := by
      apply div_mem_ratioIcc <;>
        norm_num [chartRUpper] at hu0 hu1 ⊢ <;> nlinarith
    have hlmem : chartRLower 1 u ∈ Icc (1 : Real) (360002 / 212499) := by
      rw [hl]; norm_num
    refine ⟨hubroad, hlmem, hh, ?_⟩
    change 0 <= ((cellUUpper 1 - cellULower 1) * (chartRUpper 1 u - chartRLower 1 u)) / u
    exact div_nonneg (mul_nonneg (by norm_num [cellULower, cellUUpper])
      (sub_nonneg.mpr (hl.trans_le hh.1))) (by nlinarith)
  · have hubroad : u ∈ Icc (319999 / 1500000 : Real) (180001 / 500000) :=
      ⟨hu0, by norm_num; nlinarith⟩
    have hl : chartRLower 2 u ∈ Icc (1 : Real) (360002 / 212499) := by
      apply div_sub_two_mem_ratioIcc <;>
        norm_num [chartRLower] at hu0 hu1 ⊢ <;> nlinarith
    have hh : chartRUpper 2 u ∈ Icc (1 : Real) (360002 / 212499) := by
      apply div_sub_two_mem_ratioIcc <;>
        norm_num [chartRUpper] at hu0 hu1 ⊢ <;> nlinarith
    have ho : chartRLower 2 u <= chartRUpper 2 u := by
      have hn : 0 <= 1 - u := by nlinarith
      exact sub_le_sub_right (div_le_div_of_nonneg_left hn
        (by norm_num; nlinarith) (by norm_num; nlinarith)) 2
    refine ⟨hubroad, hl, hh, ?_⟩
    change 0 <= ((cellUUpper 2 - cellULower 2) * (chartRUpper 2 u - chartRLower 2 u)) / (u * (1 - u))
    exact div_nonneg (mul_nonneg (by norm_num [cellULower, cellUUpper])
      (sub_nonneg.mpr ho)) (mul_nonneg (by nlinarith) (by nlinarith))
  · have hubroad : u ∈ Icc (319999 / 1500000 : Real) (180001 / 500000) := by
      constructor <;> norm_num <;> nlinarith
    have hl : chartRLower 3 u ∈ Icc (1 : Real) (360002 / 212499) := by
      apply div_sub_two_mem_ratioIcc <;>
        norm_num [chartRLower] at hu0 hu1 ⊢ <;> nlinarith
    have hh : chartRUpper 3 u ∈ Icc (1 : Real) (360002 / 212499) := by
      apply div_sub_two_mem_ratioIcc <;>
        norm_num [chartRUpper] at hu0 hu1 ⊢ <;> nlinarith
    have ho : chartRLower 3 u <= chartRUpper 3 u := by
      have hn : 0 <= 1 - u := by nlinarith
      exact sub_le_sub_right (div_le_div_of_nonneg_left hn (by norm_num)
        (by norm_num; nlinarith)) 2
    refine ⟨hubroad, hl, hh, ?_⟩
    change 0 <= ((cellUUpper 3 - cellULower 3) * (chartRUpper 3 u - chartRLower 3 u)) / (u * (1 - u))
    exact div_nonneg (mul_nonneg (by norm_num [cellULower, cellUUpper])
      (sub_nonneg.mpr ho)) (mul_nonneg (by nlinarith) (by nlinarith))
  · have hubroad : u ∈ Icc (319999 / 1500000 : Real) (180001 / 500000) :=
      ⟨by norm_num; nlinarith, hu1⟩
    have huOne : 0 < 1 - u := by norm_num; nlinarith
    have hl : chartRLower 4 u = 1 := by
      norm_num [chartRLower]
      field_simp [huOne.ne']
      norm_num
    have hh : chartRUpper 4 u ∈ Icc (1 : Real) (360002 / 212499) := by
      apply div_sub_two_mem_ratioIcc <;>
        norm_num [chartRUpper] at hu0 hu1 ⊢ <;> nlinarith
    have hlmem : chartRLower 4 u ∈ Icc (1 : Real) (360002 / 212499) := by
      rw [hl]; norm_num
    refine ⟨hubroad, hlmem, hh, ?_⟩
    change 0 <= ((cellUUpper 4 - cellULower 4) * (chartRUpper 4 u - chartRLower 4 u)) / (u * (1 - u))
    exact div_nonneg (mul_nonneg (by norm_num [cellULower, cellUUpper])
      (sub_nonneg.mpr (hl.trans_le hh.1))) (mul_nonneg (by nlinarith) huOne.le)
private noncomputable def tightLog (r : Real) : Real := let z := (r - 1) / (r + 1)
  2 * (z + z ^ 3 / (3 * (1 - z ^ 2)))
private theorem tightLog_eq_ratio {r : Real} (hr : 1 <= r) :
    tightLog r = ratioNumerator.eval r / (6 * r * (r + 1)) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr1 : 0 < r + 1 := by linarith
  have hz : 1 - ((r - 1) / (r + 1)) ^ 2 = 4 * r / (r + 1) ^ 2 := by
    field_simp [hr1.ne']
    ring
  rw [ratioNumerator_eval]
  dsimp only [tightLog]
  rw [hz]
  field_simp [hr0.ne', hr1.ne']
  ring
private theorem transformed_expansion (cell : Fin 5) (x y : Real) :
    let u := physicalU cell x
    let r0 := chartRLower cell u
    let r1 := chartRUpper cell u
    let r := r0 + (r1 - r0) * y
    sectionSixFirstLowCentralLargeAboveTransformedIntegrand tightLog cell x y =
      (cellUUpper cell - cellULower cell) * (r1 - r0) *
        (if cell.val < 2 then
          tightLog r / (u * (r + 1) * (u + (212499 / 500000) * r - 287501 / 500000))
        else tightLog r / (u * (1 - u) * (r + 1))) := by
  fin_cases cell <;> rfl
private theorem transformed_eq_core (cell : Fin 5) (x y : Real)
    (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) :
    let u := physicalU cell x
    let r0 := chartRLower cell u
    let r1 := chartRUpper cell u
    sectionSixFirstLowCentralLargeAboveTransformedIntegrand tightLog cell x y =
      chartScale cell u *
        (if cell.val < 2 then aCore u (r0 + (r1 - r0) * y)
         else bCore (r0 + (r1 - r0) * y)) := by
  let u := physicalU cell x
  let r0 := chartRLower cell u
  let r1 := chartRUpper cell u
  let r := r0 + (r1 - r0) * y
  change sectionSixFirstLowCentralLargeAboveTransformedIntegrand tightLog cell x y =
    chartScale cell u * (if cell.val < 2 then aCore u r else bCore r)
  obtain ⟨hu, hr0, hr1, _⟩ :
      u ∈ Icc (319999 / 1500000 : Real) (180001 / 500000) ∧
        r0 ∈ Icc (1 : Real) (360002 / 212499) ∧
        r1 ∈ Icc (1 : Real) (360002 / 212499) ∧
        0 <= chartScale cell u := by
    simpa only [u, r0, r1] using chartFacts cell hx
  have hr : r ∈ Icc (1 : Real) (360002 / 212499) := by
    have h := (convex_Icc (1 : Real) (360002 / 212499)).lineMap_mem hr0 hr1 hy
    rw [AffineMap.lineMap_apply_ring'] at h
    constructor <;> nlinarith [h.1, h.2]
  rw [transformed_expansion, tightLog_eq_ratio hr.1]
  change (cellUUpper cell - cellULower cell) * (r1 - r0) *
      (if cell.val < 2 then
        ratioNumerator.eval r / (6 * r * (r + 1)) /
          (u * (r + 1) * (u + (212499 / 500000) * r - 287501 / 500000))
      else ratioNumerator.eval r / (6 * r * (r + 1)) /
        (u * (1 - u) * (r + 1))) =
    chartScale cell u * (if cell.val < 2 then aCore u r else bCore r)
  by_cases hcell : cell.val < 2
  · have hua : u ∈ Icc (43 / 200 : Real) (180001 / 500000) := by
      simpa only [u] using physicalU_mem_a cell hx hcell
    have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hua.1
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr.1
    have hrplus : 0 < r + 1 := by linarith
    have hlast : 0 < u + (212499 / 500000) * r - 287501 / 500000 := by
      norm_num at hu hr ⊢
      nlinarith [hua.1, hr.1]
    simp only [hcell, if_pos, chartScale, aCore]
    rw [aDenominator_eval]
    field_simp [hu0.ne', hrpos.ne', hrplus.ne', hlast.ne']
    ring
  · have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu.1
    have hu1 : 0 < 1 - u := by norm_num at hu ⊢; nlinarith [hu.2]
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr.1
    have hrplus : 0 < r + 1 := by linarith
    simp only [hcell, if_false, chartScale, bCore]
    rw [bDenominator_eval]
    field_simp [hu0.ne', hu1.ne', hrpos.ne', hrplus.ne']
    ring
theorem sectionSixFirstLowCentralLargeAbove_tight_concaveOn_y
    (cell : Fin 5) (x : Real) (hx : x ∈ Icc (0 : Real) 1) :
    let tightLog : Real -> Real := fun r =>
      let z := (r - 1) / (r + 1)
      2 * (z + z ^ 3 / (3 * (1 - z ^ 2)))
    ConcaveOn Real (Icc (0 : Real) 1)
      (sectionSixFirstLowCentralLargeAboveTransformedIntegrand
        tightLog cell x) := by
  dsimp only
  obtain ⟨hu, hr0, hr1, hscale⟩ := chartFacts cell hx
  have hcore : ConcaveOn Real (Icc (0 : Real) 1)
      (fun y => chartScale cell (physicalU cell x) *
        (if cell.val < 2 then
          aCore (physicalU cell x)
            (chartRLower cell (physicalU cell x) +
              (chartRUpper cell (physicalU cell x) -
                chartRLower cell (physicalU cell x)) * y)
        else
          bCore (chartRLower cell (physicalU cell x) +
            (chartRUpper cell (physicalU cell x) -
              chartRLower cell (physicalU cell x)) * y))) := by
    by_cases hcell : cell.val < 2
    · have hua := physicalU_mem_a cell hx hcell
      simpa [hcell] using affineCore_concaveOn (aCore_concaveOn hua)
        hr0 hr1 hscale
    · simpa [hcell] using affineCore_concaveOn bCore_concaveOn hr0 hr1 hscale
  refine hcore.congr ?_
  intro y hy
  change _ = sectionSixFirstLowCentralLargeAboveTransformedIntegrand tightLog cell x y
  exact (transformed_eq_core cell x y hx hy).symm
end
end PrimesRestrictedDigits
