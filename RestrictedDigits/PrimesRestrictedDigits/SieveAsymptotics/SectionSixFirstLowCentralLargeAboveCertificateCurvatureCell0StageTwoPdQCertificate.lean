import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0SignedKernel
/-!
# Cached TwoPdQ product stage for the Cell0 signed replay

The integer table is the exact convolution
`2 * (a + 1) * cell0PNumerator (a + 1) u * cell0QNumerator (k - a) v`.
The rational scale remains factored as `cell0PScale * cell0QScale`; all table
entries are checked coordinatewise against `cell0StageProductRow 1`.
-/
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
open Polynomial (C X)
namespace SectionSixFirstLowCentralLargeAboveCell0Certificate

def cell0TwoPdQValue (i j : Nat) : Rat :=
  let row : List Int := match i with
  | 0 => [1115520792758961843577903046915286579208350484260537610787545420104374487525000, 0, 0, 0, 0, 0, 0, 0]
  | 1 => [-2669599845455238112231277245997802666975010958220666244775271306428411075580930, 2921426353936410926937412674853426843049073649977299179440273805376837325585000, 0, 0, 0, 0, 0, 0]
  | 2 => [523707451361480782765241141606496669489130418967971570383189841337301249507440, -4637975700683984992959311885453331569712230173814104188375053026850483914764762, 2665037298183082240105211659877408024653552181167741138938365050505045242650000, 0, 0, 0, 0, 0]
  | 3 => [569446193826136608210145181145606346742252176880649169549064335282780787875470, 607442186117968266022719728981463839989484385058687182189019075434286472414328, -3252320030342505386017977898625728601137496515205877524762206065472703635316580, 1165406905843722003231147585552418661902235142285370898601349974722722760280000, 0, 0, 0, 0]
  | 4 => [-208376747649525206143741775511372747371900788234236714385268426755343761676400, 945379943407096010100434294956711460239176175094667270139930998638045980829370, 320786532323593832900443173667133481088153318303468145554944829684783757055264, -1220553662172171754717078571115444919254412118878456592776041749551012811086416, 269953075623385197954520939120448936335000392945117996792784974525165619680000, 0, 0, 0]
  | 5 => [-1595874313950806784960315576496490252227831260095878232104575442676478265350, -319003537519628916882064605100653799496646163816375230950342386959893813225100, 635928591465944968724375359388190784035633183816409507767453241729852682923728, 113962748940556190929634206924173161372921954694777412584819926507168199582264, -267211327831298098130060591147246325000275204266826889838510158916134118716096, 33258291858379279724589602541860685470309629624732865755880552077426866000000, 0, 0]
  | 6 => [8348353819959489252663656459354057102963317513713062800486090680912319987680, 5187785778272498636394268705109432733898121582945513219506878632769580326810, -214723794587877476189114674650032332213911943062129195580039156963795156857300, 226347395252828809933844936728570705299096018463434369957497445614940952923864, 30680770956891207153309279265200893770752351128181005186524672427170282962432, -33920862339068409019950304442119918465562192211097397796919522560248831335200, 1989197915608254548423484244894004647407713500054519842594074641020435360000, 0]
  | 7 => [-1033040818468033450761444365461013276658261772898537433154988286249966029190, 10011183027411287556672361407543055670119602609159559209188624528014337541552, 9646886351926346092363099197566101682168150620718131979610369717036304766940, -81584870851218368404619666037686083930557880790275274266087259808756832788720, 45777520949678730981382054727170948193265898863746042704998836882420897557344, 5619875503155093379757551418894127062094033713023793212613536854845828844864, -2259479756825477624527937692607781871397865972524844083677336162574574883392, 42167886603912055838607566961158842842275608330200585235397004391537920000]
  | 8 => [36709405077622332255953037573371103891432281272326134813609507312436656280, -1424300348946835805570013331953373954036817796743579982191477972022103122618, 4810848249851018130451332601208130377099856359399130835009869665388389224920, 6379682265239052659928135581035216817639383299650785211287653144230822615520, -18651799320380200297495402260308870200037291325098394707147259730648565559840, 5105831652771172808828571378937554701049309725925098354639334903654205780320, 573792238490798256351568639984185138218599523771739507325766824846288413696, -58461710356353068892599449086585322327469144258316047763005934473048346624]
  | 9 => [0, 58040702535004243644739629349519363863467950219109213167509172446134415420, -763551933547963497925900759583211996570981695305672451203538116107516255624, 1075623223090675600083537598167444730175036924714531653005274404947750887896, 2184645480470409175733558804441367640480962073342907615217138763868080400640, -2533936813233316155516077773324734092062975048415463239151729038479666282560, 265806472344619361452796549048108179161900901241776654317212051539691119104, 23431938465851320688583176782397329341737433559367857456904075917053539712]
  | 10 => [0, 0, 34523285731027449394206048845417928062416443572254425715399250499931808652, -199573954753204722483109774227582222912646833354695112912157049967005215464, 61342920253123645832277701783464764211152644479830172623372757203074145216, 416915811612389294654278026488533668229102423187179084404949380665031161760, -186398315376001567588309955696709284089718103466211289357536844850379442240, 3347816758372597577546963082455242311816265715588526585781991836692700800]
  | 11 => [0, 0, 0, 9256108357270581921627446867268200459906074594019931255892015726162801056, -24217210402025599448271485014881649020603367922248488472988146928439241632, -20744497175576534518264538643440053214532572245121478231806882073376226880, 42308719940637020649116335676533437445697863056663678045977284178179062720, -5527539477025326619903586475701247004148613033680661182706924432166467840]
  | 12 => [0, 0, 0, 0, 944576266989750280826852099453180052750313124549228387661437883168771936, -372209955586760480609515075409440783125066234343471404607568948786525664, -4293806271986806532245100260830993282083255772602539796639552029615459968, 1790575484361425375918812218296863337825475993884714190784567979236680960]
  | 13 => [0, 0, 0, 0, 0, -21639058633005741137139913890900145462277141340752080707166841271416640, 201219182540517036373109865288965159337689425873759456686934008566726784, -255292766376595033013668316119809329531894290630404764565133496487820416]
  | 14 => [0, 0, 0, 0, 0, 0, -7009533365273788220073456355260058978428402409515551955176138590896704, 14019066730547576440146912710520117956856804819031103910352277181793408]
  | _ => []
  cell0PScale * cell0QScale * (row.getD j 0 : Rat)

def cell0TwoPdQRow (i : Nat) : Polynomial Rat :=
  ∑ j ∈ Finset.range 8, C (cell0TwoPdQValue i j) * X ^ j

@[simp] theorem cell0TwoPdQRow_coeff (i l : Nat) :
    (cell0TwoPdQRow i).coeff l = if l < 8 then cell0TwoPdQValue i l else 0 := by
  simpa only [cell0TwoPdQRow] using
    cell0FinitePolynomial_coeff 8 l (cell0TwoPdQValue i)

theorem cell0TwoPdQRow_natDegree (i : Nat) :
    (cell0TwoPdQRow i).natDegree ≤ 7 := by
  rw [cell0TwoPdQRow]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact (Polynomial.natDegree_mul_le_of_le (m := 0) (n := j)
    (Polynomial.natDegree_C _).le (Polynomial.natDegree_X_pow_le j)).trans
    (by simpa using (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))

theorem cell0StageTwoPdQ_natDegree (k : Nat) :
    (cell0StageProductRow 1 k).natDegree ≤ 7 := by
  simpa [cell0StageProductRow] using
    cell0OuterConv_natDegree cell0TwoPdCoeff cell0QCoeff 3 4
      cell0TwoPdCoeff_natDegree cell0QCoeff_natDegree k

attribute [local simp] cell0TwoPdCoeff_coeff cell0PDerivCoeff_coeff
  cell0PCoeff_coeff cell0QCoeff_coeff

local macro "cell0_twoPdQ_coeff" : tactic => `(tactic|
  (rw [cell0StageProductRow, cell0OuterConv_coeff, cell0ScalarConv]
   simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
   repeat rw [Finset.sum_range_succ]
   all_goals simp
   all_goals norm_num [Finset.sum_range_succ, cell0PScale, cell0QScale,
     cell0PNumerator, cell0QNumerator, cell0TwoPdQValue]
   all_goals (repeat rw [Finset.sum_range_succ])
   all_goals norm_num [Finset.sum_range_succ]
   all_goals ring_nf))

local syntax "cell0_twoPdQ_row_commands" num ident ident ident ident ident ident ident ident ident : command
local macro_rules
  | `(cell0_twoPdQ_row_commands $k:num $n0:ident $n1:ident $n2:ident $n3:ident
      $n4:ident $n5:ident $n6:ident $n7:ident $row:ident) => `(
    @[simp] private theorem $n0 :
        (cell0StageProductRow 1 $k).coeff 0 = cell0TwoPdQValue $k 0 := by
      cell0_twoPdQ_coeff
    @[simp] private theorem $n1 :
        (cell0StageProductRow 1 $k).coeff 1 = cell0TwoPdQValue $k 1 := by
      cell0_twoPdQ_coeff
    @[simp] private theorem $n2 :
        (cell0StageProductRow 1 $k).coeff 2 = cell0TwoPdQValue $k 2 := by
      cell0_twoPdQ_coeff
    @[simp] private theorem $n3 :
        (cell0StageProductRow 1 $k).coeff 3 = cell0TwoPdQValue $k 3 := by
      cell0_twoPdQ_coeff
    @[simp] private theorem $n4 :
        (cell0StageProductRow 1 $k).coeff 4 = cell0TwoPdQValue $k 4 := by
      cell0_twoPdQ_coeff
    @[simp] private theorem $n5 :
        (cell0StageProductRow 1 $k).coeff 5 = cell0TwoPdQValue $k 5 := by
      cell0_twoPdQ_coeff
    @[simp] private theorem $n6 :
        (cell0StageProductRow 1 $k).coeff 6 = cell0TwoPdQValue $k 6 := by
      cell0_twoPdQ_coeff
    @[simp] private theorem $n7 :
        (cell0StageProductRow 1 $k).coeff 7 = cell0TwoPdQValue $k 7 := by
      cell0_twoPdQ_coeff
    @[simp] theorem $row : cell0StageProductRow 1 $k = cell0TwoPdQRow $k := by
      apply (Polynomial.ext_iff_natDegree_le
        (cell0StageTwoPdQ_natDegree $k)
        (cell0TwoPdQRow_natDegree $k)).2
      intro l hl
      interval_cases l <;> simp)

cell0_twoPdQ_row_commands 0 cell0TwoPdQ_coeff_0_0 cell0TwoPdQ_coeff_0_1 cell0TwoPdQ_coeff_0_2 cell0TwoPdQ_coeff_0_3 cell0TwoPdQ_coeff_0_4 cell0TwoPdQ_coeff_0_5 cell0TwoPdQ_coeff_0_6 cell0TwoPdQ_coeff_0_7 cell0TwoPdQ_row0
cell0_twoPdQ_row_commands 1 cell0TwoPdQ_coeff_1_0 cell0TwoPdQ_coeff_1_1 cell0TwoPdQ_coeff_1_2 cell0TwoPdQ_coeff_1_3 cell0TwoPdQ_coeff_1_4 cell0TwoPdQ_coeff_1_5 cell0TwoPdQ_coeff_1_6 cell0TwoPdQ_coeff_1_7 cell0TwoPdQ_row1
cell0_twoPdQ_row_commands 2 cell0TwoPdQ_coeff_2_0 cell0TwoPdQ_coeff_2_1 cell0TwoPdQ_coeff_2_2 cell0TwoPdQ_coeff_2_3 cell0TwoPdQ_coeff_2_4 cell0TwoPdQ_coeff_2_5 cell0TwoPdQ_coeff_2_6 cell0TwoPdQ_coeff_2_7 cell0TwoPdQ_row2
cell0_twoPdQ_row_commands 3 cell0TwoPdQ_coeff_3_0 cell0TwoPdQ_coeff_3_1 cell0TwoPdQ_coeff_3_2 cell0TwoPdQ_coeff_3_3 cell0TwoPdQ_coeff_3_4 cell0TwoPdQ_coeff_3_5 cell0TwoPdQ_coeff_3_6 cell0TwoPdQ_coeff_3_7 cell0TwoPdQ_row3
cell0_twoPdQ_row_commands 4 cell0TwoPdQ_coeff_4_0 cell0TwoPdQ_coeff_4_1 cell0TwoPdQ_coeff_4_2 cell0TwoPdQ_coeff_4_3 cell0TwoPdQ_coeff_4_4 cell0TwoPdQ_coeff_4_5 cell0TwoPdQ_coeff_4_6 cell0TwoPdQ_coeff_4_7 cell0TwoPdQ_row4
cell0_twoPdQ_row_commands 5 cell0TwoPdQ_coeff_5_0 cell0TwoPdQ_coeff_5_1 cell0TwoPdQ_coeff_5_2 cell0TwoPdQ_coeff_5_3 cell0TwoPdQ_coeff_5_4 cell0TwoPdQ_coeff_5_5 cell0TwoPdQ_coeff_5_6 cell0TwoPdQ_coeff_5_7 cell0TwoPdQ_row5
cell0_twoPdQ_row_commands 6 cell0TwoPdQ_coeff_6_0 cell0TwoPdQ_coeff_6_1 cell0TwoPdQ_coeff_6_2 cell0TwoPdQ_coeff_6_3 cell0TwoPdQ_coeff_6_4 cell0TwoPdQ_coeff_6_5 cell0TwoPdQ_coeff_6_6 cell0TwoPdQ_coeff_6_7 cell0TwoPdQ_row6
cell0_twoPdQ_row_commands 7 cell0TwoPdQ_coeff_7_0 cell0TwoPdQ_coeff_7_1 cell0TwoPdQ_coeff_7_2 cell0TwoPdQ_coeff_7_3 cell0TwoPdQ_coeff_7_4 cell0TwoPdQ_coeff_7_5 cell0TwoPdQ_coeff_7_6 cell0TwoPdQ_coeff_7_7 cell0TwoPdQ_row7
cell0_twoPdQ_row_commands 8 cell0TwoPdQ_coeff_8_0 cell0TwoPdQ_coeff_8_1 cell0TwoPdQ_coeff_8_2 cell0TwoPdQ_coeff_8_3 cell0TwoPdQ_coeff_8_4 cell0TwoPdQ_coeff_8_5 cell0TwoPdQ_coeff_8_6 cell0TwoPdQ_coeff_8_7 cell0TwoPdQ_row8
cell0_twoPdQ_row_commands 9 cell0TwoPdQ_coeff_9_0 cell0TwoPdQ_coeff_9_1 cell0TwoPdQ_coeff_9_2 cell0TwoPdQ_coeff_9_3 cell0TwoPdQ_coeff_9_4 cell0TwoPdQ_coeff_9_5 cell0TwoPdQ_coeff_9_6 cell0TwoPdQ_coeff_9_7 cell0TwoPdQ_row9
cell0_twoPdQ_row_commands 10 cell0TwoPdQ_coeff_10_0 cell0TwoPdQ_coeff_10_1 cell0TwoPdQ_coeff_10_2 cell0TwoPdQ_coeff_10_3 cell0TwoPdQ_coeff_10_4 cell0TwoPdQ_coeff_10_5 cell0TwoPdQ_coeff_10_6 cell0TwoPdQ_coeff_10_7 cell0TwoPdQ_row10
cell0_twoPdQ_row_commands 11 cell0TwoPdQ_coeff_11_0 cell0TwoPdQ_coeff_11_1 cell0TwoPdQ_coeff_11_2 cell0TwoPdQ_coeff_11_3 cell0TwoPdQ_coeff_11_4 cell0TwoPdQ_coeff_11_5 cell0TwoPdQ_coeff_11_6 cell0TwoPdQ_coeff_11_7 cell0TwoPdQ_row11
cell0_twoPdQ_row_commands 12 cell0TwoPdQ_coeff_12_0 cell0TwoPdQ_coeff_12_1 cell0TwoPdQ_coeff_12_2 cell0TwoPdQ_coeff_12_3 cell0TwoPdQ_coeff_12_4 cell0TwoPdQ_coeff_12_5 cell0TwoPdQ_coeff_12_6 cell0TwoPdQ_coeff_12_7 cell0TwoPdQ_row12
cell0_twoPdQ_row_commands 13 cell0TwoPdQ_coeff_13_0 cell0TwoPdQ_coeff_13_1 cell0TwoPdQ_coeff_13_2 cell0TwoPdQ_coeff_13_3 cell0TwoPdQ_coeff_13_4 cell0TwoPdQ_coeff_13_5 cell0TwoPdQ_coeff_13_6 cell0TwoPdQ_coeff_13_7 cell0TwoPdQ_row13
cell0_twoPdQ_row_commands 14 cell0TwoPdQ_coeff_14_0 cell0TwoPdQ_coeff_14_1 cell0TwoPdQ_coeff_14_2 cell0TwoPdQ_coeff_14_3 cell0TwoPdQ_coeff_14_4 cell0TwoPdQ_coeff_14_5 cell0TwoPdQ_coeff_14_6 cell0TwoPdQ_coeff_14_7 cell0TwoPdQ_row14

local macro "cell0_twoPdQ_zero_command" n:ident k:num : command => `(
  @[simp] theorem $n : cell0StageProductRow 1 $k = 0 := by
    rw [cell0StageProductRow, cell0OuterConv]
    simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    repeat rw [Finset.sum_range_succ]
    simp [cell0TwoPdCoeff, cell0PDerivCoeff, cell0PCoeff, cell0QCoeff])

cell0_twoPdQ_zero_command cell0TwoPdQ_row15_zero 15
cell0_twoPdQ_zero_command cell0TwoPdQ_row16_zero 16
cell0_twoPdQ_zero_command cell0TwoPdQ_row17_zero 17
cell0_twoPdQ_zero_command cell0TwoPdQ_row18_zero 18
cell0_twoPdQ_zero_command cell0TwoPdQ_row19_zero 19
cell0_twoPdQ_zero_command cell0TwoPdQ_row20_zero 20
cell0_twoPdQ_zero_command cell0TwoPdQ_row21_zero 21

end SectionSixFirstLowCentralLargeAboveCell0Certificate
end
end PrimesRestrictedDigits
