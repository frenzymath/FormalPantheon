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
import PrimesRestrictedDigits.BasicEstimates.TensorBernsteinNonnegative
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateNodes
/-! Exact x-curvature certificate for the upper `I_4` cell 4. -/
open Set Polynomial
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
private abbrev BivariateRat := Polynomial (Polynomial Rat)
private noncomputable def cell4Constant (a : Rat) : BivariateRat := C (C a)
private def cell4PScale : Rat := 55001 / 46875000000000000000000000000
private def cell4PNumerator (i j : Nat) : Int :=
  let row := match i with
    | 0 => [0, 6858406689086212200108, 3631035100128782399676, 160197750683449650081]
    | 1 => [0, -13411881507388452120144, -10650945923691803459352, -626545886622786180216]
    | 2 => [0, 6556864215068684880048, 10414169875451728079568, 918926170239189960216]
    | 3 => [0, 0, -3394219160494804559904, -598998643465219440096]
    | 4 => [0, 0, 0, 146420648290403520016]
    | _ => []
  row.getD j 0
private def cell4PRow (i : Nat) : Polynomial Rat := ∑ j ∈ Finset.range 4, C (cell4PScale * (cell4PNumerator i j : Rat)) * X ^ j
private noncomputable def cell4PFull : BivariateRat := ∑ i ∈ Finset.range 5, C (cell4PRow i) * X ^ i
private def cell4QScale : Rat := 212499 / 3906250000000000000000000000000000
private def cell4QNumerator (i j : Nat) : Int :=
  let row := match i with
    | 0 => [1799168935666406062500000000, 1905062167532813625000000000, 630371228317380703125000000, 66747282857227828125000000]
    | 1 => [527765816696469332499000000, -1303883252018815244994000000, -1047803242764722821886250000, -176210809536165463118250000]
    | 2 => [-116110590736490039027109996, -669349833720369115847340024, 200371240410340248482512545, 129697380195191082149242473]
    | 3 => [0, 120211362897664245695840016, 256336380903510028620599940, 6397559210320369259460054]
    | 4 => [0, 0, -38892801676328071999849980, -30657152682261890411270036]
    | 5 => [0, 0, 0, 4026641038310242002200008]
    | _ => []
  row.getD j 0
private def cell4QRow (i : Nat) : Polynomial Rat := ∑ j ∈ Finset.range 4, C (cell4QScale * (cell4QNumerator i j : Rat)) * X ^ j
private noncomputable def cell4QFull : BivariateRat := ∑ i ∈ Finset.range 6, C (cell4QRow i) * X ^ i
private noncomputable def cell4RationalPolynomials : BivariateRat × BivariateRat := (cell4PFull, cell4QFull)
private noncomputable def cell4SignedCurvature : BivariateRat :=
  let p := cell4RationalPolynomials.1; let q := cell4RationalPolynomials.2
  p.derivative.derivative * q ^ 2 - cell4Constant 2 * p.derivative * q * q.derivative + cell4Constant 2 * p * q.derivative ^ 2 - p * q * q.derivative.derivative
private def cell4BernsteinScale : Rat :=
  2504403393701338451996667 /
    262260437011718750000000000000000000000000000000000000000000000000000000000000000000000000000000000
private def cell4BernsteinNumerator (i j : Nat) : Nat :=
  let row := match j with
    | 0 => [27128323183434476616595176958923180592654222006727475415800000000000000, 33755427634931192840501032194606834226699731664164065261175000000000000, 41845365529823817931331711942652007125066794395364001833512500000000000, 51678366300831375832043887399467216339950605940549282660287500000000000, 63580227271422097101116650479388511439516763489727526127533750000000000, 77929829190879525720378063635062260333619819645989762362695312500000000, 95168880536232294142119477247890116464289472454182621274183593750000000, 115814823799378467954077324106308429942734102060970711265998437500000000, 140478064008508356412209878894876295526866603809695513932562500000000000]
    | 1 => [26542516455089647373320323342654187724438768170151866104431762400000000, 32364634243311862265682937931294257691466885766058082592084707900000000, 39308784103671628884470612846588963757136782480476370324854630850000000, 47551464578535211463226006433743510367637407732265610773914265550000000, 57289088009243640712423963177978504917052955296243812062592580695000000, 68739534449717619715983094651680556249686495402210454258949632031250000, 82144182932002720562088410892631265185854323517548394323944416984375000, 97770692703587228275662664264319590152752842304844790464292986393750000, 115916856954722113989814445070176731683561210162275703528277574250000000]
    | 2 => [26005045441563604883530756988095151125854198423430249992992983008172800, 31086846964941610220341420322850359968462440482234297554460494067848800, 37013545729436359212678633618026192622656672099841324508750807653541200, 43890862085360510246107430111771128933920324152230247262174007763079600, 51831030166210642969633998206050257620663523153060558636327205829414040, 60952231715523971740195098938702756098254630659660281685037945436631250, 71377991814352433567694078873058591371932565941971096316199632249685375, 83236602624911592315543956098694296312924795934004435263707814357305350, 96660649551722509233870393006276022325495502743779863710002271609946000]
    | 3 => [25516640644714175897653103008369140449244316929408514340505170246895360, 29917935823610675656226896014448659603547219473440702634322317257640000, 34941849411740627787941413921994206781659799827974415618401893912088240, 40647844639089209741670588273710246710490828889459371179953101257911360, 47095880155417332686598777501364365088393420299832534592398629983917848, 54345474424467539787242990708693904703454325845043545248118853756129180, 62454663576312664867224567785608546314279706338774083987337950623644165, 71478865056104205430310480866030504705288657299482289960426957443829390, 81469660317367846542662066229056821325432262624451189346594034448865520]
    | 4 => [25078032566399187166113986516599225346952927850932546405989832538544640, 28853644792844959562400655873896250033291927159830631377700012396251840, 33076340413475689484922889623527705716981591757325021240413402674147680, 37776950470252162184321918610272378998164935707242577859850765377153760, 42984824286293343145635561633067885829591246093047085528153159999619024, 48727139389897723990697702117942084776392903105065637492607955941912260, 55028147270474832486313640249977302387151330901251632825330422754222930, 61908356539152421242124521946389680612661400967679523176718036686866460, 69383655125302795586983016798175138750222324649847972542834775743176480]
    | 5 => [24689951708476465439340032625908475471323835350848233448468478305497600, 27889591795906024965234864991633799584977148720962758390633290583347200, 31400132014783426969322882158796002474870248126201907934310637595253600, 35235893098656700665285261256501486130211685953578488734621821706093600, 39409627905032230914326067499719893352588423637397550746213183923056720, 43932158586916192669670861478268485725444959361305746011878961966324400, 48811989781157925620675985773291121282354354746473293355633675670980050, 54054897934372812459210728910472689926302667768987350848228972463527600, 59663496890076149751900303792665506314132103510167573381091457432958000]
    | 6 => [24353128572803837467757866449419960474700843592001462726962615970131200, 27021268705791096928412562680735551476593350095801099339171739091373600, 29896827826916336672113262993219738265963110452693951406065146717409200, 32985483508376697520890455544352872559913487009111544663213951677800400, 36291890292960834268014493429260781619137116373828630045739514309727080, 39819539748273547892377969840622675353069953164783821091851818230904150, 43570614958695081939554771812900825194468306700691467087485775334482425, 47545839462003531647319621269964596455039365764923073731395661490146050, 51744320637707155432377046601970244622032143831119274682014002116796400]
    | 7 => [24068293661239130001794113100256750009427756737238121500493753954822400, 26244041345233062552927662476909323816840877982715010949374821365563200, 28550544660975508949652693166573884526628711174586014235632488967984400, 30989551018006289780633954639747659136013348544548643485210676502508000, 33562331425592853945524526914707027832197602586780543070167279247244840, 36269644609725258339415531770910822449070042974213164837635106243012700, 39111700489679430738547440248011810835592274358941756166367268964445375, 42088123014480032874932729068475219751802700682078471391486171554980550, 45197912359598649014350448838618695590069739902437263545429990272364800]
    | 8 => [23836177475640169791875397691541913727848378949404097028083400681948160, 25553149486700470977084952138496509605129959839479191007311877023932800, 27345935951526602429679937925077032440674505795269981158501313378069440, 29214862242978446529888273789780607069704063459534282528491281658938560, 31160107277979028335349809977071758042574041561755662452581332393121568, 33181698860722370363781895401331751310665055724832260377172814885969160, 35279508975261695656240677317292484817491888327788547915221284587735860, 37453249027491981063233360445352244821147203084243501217375776262683960, 39702465036541014925033152566780032894112048981274706006154463196768320]
    | 9 => [23657510517864783588428345336398521282306514391345276568753064573885440, 24943706852397533376500093646472076731580703883273678359062121857283840, 26268215735093812543185756440466969921420287535650951901253751020284480, 27631037546749553042137087905759072096814380374962866794918908185284160, 29032150944835264559306636904730102638805779892928140624261141256011104, 30471512451740986033729055941821294479477037700673250021766015961522160, 31949056039849594574822326518700972679446388693388116391650154868266060, 33464692713439013000492956528272481752502939662210536835159655807041600, 35018310087413862188867930201870047041192539923894821819735663307967520]
    | 10 => [23533023289770798141879581147949642325145967225907547381524254053011200, 24410701114264122964099623204444567977023099090683852910714647829202400, 25303183183531834242163366616062546054137284492048591571137119666045200, 26210464377651186535612794207750867338847214550706843548868033007561200, 27132537426799076290371958876166970363629561209113888776289100883142840, 28069392882670369607967375776029447484483824772149790192397992030031450, 29021019089726624062345637058254420118716776576603942325086068236403075, 29987402156275224120073770028013328111214104082520350027721754901271550, 30968525925378949874955827164680937926817309772156633955108315934002000]
    | 11 => [23463446293216040202655730239318346508710541615936796725418477541702400, 23948993893975774990120951238656101012997015197700435628368423076059200, 24437247692275818903237484979811822998852939300093638599646941162284400, 24928206888210258409213355656318813366524944100739324033402560543052800, 25421870517033668511164069730763511079236217355015105088480208050533560, 25918237447482811330557073044577319118219466012933858492986974913891900, 26417306380090253525398568235559121253660694774299654811223912740191225, 26919075845489903214446182911050933150741524940597480447916706070743950, 27423544202714467082416412691658190736048247381678717478524863037995600]
    | 12 => [23449510030058336521183417723627703485344041724278911859457243462336000, 23553320762943686742112362397982368401752202699719488538132291907009600, 23657454523469325417171941664326515353521371304619570240121271527629600, 23761911233738697812575240897119753969496838377629853038915747816554400, 23866690805267998789257646909997179082453633833250387964255018986438640, 23971793138899039645009429235161812750969143565239464527023852563505100, 24077218124711762367376825724845032473396389572639667415159947008781350, 24182965641936401319352026349295909288001076119436616443586651935516500, 24289035558865292380009913265999327898499148569120125280449834332008800]
    | _ => []
  row.getD i 0
private def cell4BernsteinCoefficient (i j : Nat) : Rat := cell4BernsteinScale * cell4BernsteinNumerator i j
private theorem cell4BernsteinCoefficient_nonneg : ∀ i ≤ 8, ∀ j ≤ 12, 0 ≤ cell4BernsteinCoefficient i j := by
  intro i hi j hj; exact mul_nonneg (by norm_num [cell4BernsteinScale]) (Nat.cast_nonneg _)
private noncomputable def cell4Tensor : BivariateRat := tensorBernsteinPolynomial 8 12 cell4BernsteinCoefficient
private theorem cell4_one_sub_pow_coeff {R : Type*} [CommRing R] (a b : Nat) : ((1 - X : Polynomial R) ^ a).coeff b = (-1 : R) ^ a * ((-1 : R) ^ (a - b) * (a.choose b : R)) := by
  have hsub : (1 - X : Polynomial R) = -(X + C (-1 : R)) := by simp [sub_eq_add_neg]
  have hnegpow : ((-1 : Polynomial R) ^ a) = C ((-1 : R) ^ a) := by rw [show (-1 : Polynomial R) = C (-1 : R) by simp, ← Polynomial.C_pow]
  have hneg : (-(X + C (-1 : R)) : Polynomial R) ^ a = C ((-1 : R) ^ a) * (X + C (-1 : R)) ^ a := by rw [neg_pow, hnegpow]
  rw [hsub, hneg, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
private theorem cell4_bernstein_coeff_formula {R : Type*} [CommRing R] (n i k : Nat) : (bernsteinPolynomial R n i).coeff k = if i ≤ k then (n.choose i : R) * ((-1 : R) ^ (n - i) * ((-1 : R) ^ ((n - i) - (k - i)) * ((n - i).choose (k - i) : R))) else 0 := by
  rw [bernsteinPolynomial, ← Polynomial.C_eq_natCast, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', cell4_one_sub_pow_coeff]
  split_ifs <;> simp_all
private theorem cell4BernsteinPolynomial_natDegree_le (R : Type*) [CommRing R] {n i : Nat} (hi : i ≤ n) : (bernsteinPolynomial R n i).natDegree ≤ n := by
  rw [bernsteinPolynomial]
  have hc : ((Nat.choose n i : Polynomial R)).natDegree ≤ 0 := by simp
  have hx : (Polynomial.X ^ i : Polynomial R).natDegree ≤ i := Polynomial.natDegree_X_pow_le i
  have hs : (1 - Polynomial.X : Polynomial R).natDegree ≤ 1 := Polynomial.natDegree_sub_le_of_le (m := 1) (n := 1) (by simp) (Polynomial.natDegree_X_le (R := R))
  have h := Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_mul_le_of_le hc hx) (Polynomial.natDegree_pow_le_of_le (n - i) hs)
  simpa only [zero_add, mul_one, Nat.add_sub_of_le hi] using h
private theorem cell4_bernstein_outer_coeff (n i k : Nat) : (bernsteinPolynomial (Polynomial Rat) n i).coeff k = C ((bernsteinPolynomial Rat n i).coeff k) := by
  simpa only [Polynomial.coeff_map] using (congrArg (fun p : Polynomial (Polynomial Rat) => p.coeff k) (bernsteinPolynomial.map (C : Rat →+* Polynomial Rat) n i)).symm
private theorem cell4_tensor_coeff_formula (n m : Nat) (a : Nat → Nat → Rat) (k l : Nat) : ((tensorBernsteinPolynomial n m a).coeff k).coeff l = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1), a i j * (bernsteinPolynomial Rat n i).coeff l * (bernsteinPolynomial Rat m j).coeff k := by
  rw [tensorBernsteinPolynomial]
  simp_rw [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, cell4_bernstein_outer_coeff, Polynomial.coeff_mul_C, Polynomial.coeff_C_mul]
private def cell4PowerScale : Rat :=
  2504403393701338451996667 /
    119209289550781250000000000000000000000000000000000000000000000000000000000000000000000000000000
private def cell4PowerNumerator (i j : Nat) : Int :=
  let row := match i with
    | 0 => [12331055992470216643906898617692354814842828184876125189000000000000, 24098561641806240814203109947940558669256398754314872165000000000000, 18617880188675203760861402884601154273183402756988049252250000000000, 7133112832847882184351630454034979510423164296559937063000000000000, 1449887432929301402986113752239670962694591584087936408687500000000, 191304528955446017403086337016366472835919065761949745312500000000, 28366123719413954571587255336853733406277195674145630796875000000, 3393521203277740289852791899136660908038421875612794031250000000, 103195805906759703535638728150141934199653359332630359375000000]
    | 1 => [-3195309427335432236044656088739961099357020926776050789281296000000, -35126690761069149012795955507356378197122562684961746518780560000000, -52049663974003636003600348362505792576547294983831164500043444000000, -31685071962297511239189380003920941470998876343642722652328432000000, -9795198677513507461725929748267653265059981279206878808233231000000, -1821004373603187456208674005468127873357951269590653029976825000000, -267488824661291669171344862978735761711323765029727442631289750000, -28826116300137217834798549844923642817195981512746295040230500000, -966176595651825585824642006016167420849024101821259784286750000]
    | 2 => [1450071444563602604558617851298688088926522695619795997883746245184, 15520895623270026237909454358093410223403965862769063568788814322240, 53479893799541218465053208357211538044146892255434248823132005853776, 55360533142578487213131410166267848905222667851693665618553868353728, 25733559565549342708327563598004535523877588650682336019948154752924, 6453778317854211611913068873635323772753007684970912604039997907300, 1038209424387467818300185390279444833868207384858546345651616770159, 108982613671199727567146242116175889030784645760935689498083370922, 4065592183573606780797987058669275960949835929612912792405722147]
    | 3 => [73050185782675042662511312306965234380416284588725902150842237696, -3888382454070238940966774359640885186384401678315818401239734626688, -24669515080090387047991834141672262164618435576730143489127636167680, -47217108808962120839240262189719729751267604741352895795949056578112, -34106965206560783172306301876205237342887846239059332163476354568784, -11708931447534589731879428302044566296690719747462449992941922048632, -2209073306045617885849354984426467803808891277228823689709136043608, -241093799362378342393146524164694326107073782155975534639196579192, -10128297326119253601056346167735086337336217963799949323568722248]
    | 4 => [0, -226890475808332840426399259565196722214633070386091982222888987648, 4399660423065146756250854843330840708666394475808670324852369277632, 19347138089908994253948172337776013883713863468301008859409975297408, 24128937140389855128928734082731003261373263097963565751476300718144, 12035381204910306944136308419758295134546252886233870718922466674688, 2852401519011593437487455203728296477995771828272916462909464897796, 344973750883827884043854304751973380715780252587656491357562754272, 16553399570794750202940166493917545015406507115281456300636030548]
    | 5 => [0, 0, 219330538477226644500860994705577355701049489671204712621884654848, -2870792435129102656170155341168693031898086556133207829739732098304, -8613657102838703046376147970829097660748998954297371453000195339264, -7111281038885602777458324508121010704574542181207798248599333630080, -2314112544939030923850789322247302621723891126417007023504717724592, -333029445137001211204731743648140901116639513728091107687063766272, -18571329154746994293257290831769237729506201258262052282633838848]
    | 6 => [0, 0, 6525365211625932043022958740533900426270503052835173037580802560, -55652353453096457103362828312230269423572990481006495583450053120, 1231664749775500849809086906803889547649133561940731226345678884544, 2292199591421890943938525869067957622708754405092226572229489092160, 1173850305141118036368520673437778033437424545959676502786927887440, 219546785121649662579045255346117725284721587897851384881171959232, 14527445181069652832179443038705181547357437068973631982603628768]
    | 7 => [0, 0, 0, -12160488314925683394970335985366314255060910199787805759687661568, -37408425180638074609257021134722342606839772567117561220861710080, -356984626064098702583928329007567646634732141977516165538590250880, -359350379634760057915250595001315957205863493962086691117452873216, -97994445969545490614020669167074261603513847091022533868737168128, -7878391470772615884879208393133933397568041355075225091882959104]
    | 8 => [0, 0, 0, 0, 9180186582573315221184068604867804382605400208333732809958453760, 29022791316951710885975347456586630901238967663364132536093572608, 63849496801694295406905214064581949151344382074867179869391837632, 28933728284097877330881984967390702698074249218692335194008043008, 2886287314407039549925934400202012126859259522546670335849639552]
    | 9 => [0, 0, 0, 0, 0, -3484950589263487680904408667460192093342855439598429496035761152, -7319533886157615753228710499390084371817834322542865166475704064, -5525594442918009869030329902732403562427703292726626189683990528, -682019370910837546458255026989091668462104423421404783460503552]
    | 10 => [0, 0, 0, 0, 0, 0, 667720101083111095369746444263282243930447974966857511296058368, 693578562263511088111328418186848981075552811186738279359728128, 99140535895264910147456322097080602000855662139651347872145152]
    | 11 => [0, 0, 0, 0, 0, 0, 0, -54576514336050909004547277147694000340933224063943032765421568, -9631451743849359943244567928864007391965782594844811842578432]
    | 12 => [0, 0, 0, 0, 0, 0, 0, 0, 784778298302354376088333171345725996292706281164442275841024]
    | _ => []
  row.getD j 0
private def cell4PowerCoeff (i j : Nat) : Rat := cell4PowerScale * (cell4PowerNumerator i j : Rat)
private def cell4PowerRow (i : Nat) : Polynomial Rat := ∑ j ∈ Finset.range 9, C (cell4PowerCoeff i j) * X ^ j
private noncomputable def cell4Power : BivariateRat := ∑ i ∈ Finset.range 13, C (cell4PowerRow i) * X ^ i
private theorem cell4Power_outer_coeff (k : Nat) (hk : k < 13) : cell4Power.coeff k = cell4PowerRow k := by
  rw [cell4Power, Polynomial.finsetSum_coeff]; simp_rw [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b hb hbk; simp [Ne.symm hbk]
  · exact fun hnot => (hnot (Finset.mem_range.mpr hk)).elim
private theorem cell4FiniteRow_coeff (n l : Nat) (a : Nat → Rat) : (∑ j ∈ Finset.range n, C (a j) * X ^ j).coeff l = if l < n then a l else 0 := by
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  by_cases hl : l < n
  · rw [if_pos hl, Finset.sum_eq_single l]
    · simp
    · intro b hb hbl; simp [Ne.symm hbl]
    · exact fun hnot => (hnot (Finset.mem_range.mpr hl)).elim
  · rw [if_neg hl]; apply Finset.sum_eq_zero; intro b hb
    have hlb : l ≠ b := by rintro rfl; exact hl (Finset.mem_range.mp hb)
    simp [hlb]
private theorem cell4PRow_coeff (i l : Nat) : (cell4PRow i).coeff l = if l < 4 then cell4PScale * (cell4PNumerator i l : Rat) else 0 := by simpa only [cell4PRow] using cell4FiniteRow_coeff 4 l (fun j => cell4PScale * (cell4PNumerator i j : Rat))
private theorem cell4QRow_coeff (i l : Nat) : (cell4QRow i).coeff l = if l < 4 then cell4QScale * (cell4QNumerator i l : Rat) else 0 := by simpa only [cell4QRow] using cell4FiniteRow_coeff 4 l (fun j => cell4QScale * (cell4QNumerator i j : Rat))
private theorem cell4Power_row_coeff (i l : Nat) : (cell4PowerRow i).coeff l = if l < 9 then cell4PowerCoeff i l else 0 := by simpa only [cell4PowerRow] using cell4FiniteRow_coeff 9 l (cell4PowerCoeff i)
private theorem cell4PowerRow_natDegree (i : Nat) : (cell4PowerRow i).natDegree ≤ 8 := by rw [cell4PowerRow]; apply Polynomial.natDegree_sum_le_of_forall_le; intro j hj; exact (Polynomial.natDegree_mul_le_of_le (m := 0) (n := j) (Polynomial.natDegree_C _).le (Polynomial.natDegree_X_pow_le j)).trans (by simpa using (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
local macro "cell4_tensor_coeff" : tactic =>
  `(tactic|
    (rw [cell4Tensor, cell4_tensor_coeff_formula]
     repeat rw [Finset.sum_range_succ]
     simp_rw [cell4_bernstein_coeff_formula]
     norm_num [Nat.choose, cell4BernsteinCoefficient, cell4BernsteinScale,
       cell4BernsteinNumerator, cell4PowerCoeff, cell4PowerScale,
       cell4PowerNumerator] <;> ring))
local macro "cell4_tensor_row_coeffs" k:num n0:ident n1:ident n2:ident
    n3:ident n4:ident n5:ident n6:ident n7:ident n8:ident : command =>
  `(
  @[simp] private theorem $n0 : (cell4Tensor.coeff $k).coeff 0 = cell4PowerCoeff $k 0 := by cell4_tensor_coeff
  @[simp] private theorem $n1 : (cell4Tensor.coeff $k).coeff 1 = cell4PowerCoeff $k 1 := by cell4_tensor_coeff
  @[simp] private theorem $n2 : (cell4Tensor.coeff $k).coeff 2 = cell4PowerCoeff $k 2 := by cell4_tensor_coeff
  @[simp] private theorem $n3 : (cell4Tensor.coeff $k).coeff 3 = cell4PowerCoeff $k 3 := by cell4_tensor_coeff
  @[simp] private theorem $n4 : (cell4Tensor.coeff $k).coeff 4 = cell4PowerCoeff $k 4 := by cell4_tensor_coeff
  @[simp] private theorem $n5 : (cell4Tensor.coeff $k).coeff 5 = cell4PowerCoeff $k 5 := by cell4_tensor_coeff
  @[simp] private theorem $n6 : (cell4Tensor.coeff $k).coeff 6 = cell4PowerCoeff $k 6 := by cell4_tensor_coeff
  @[simp] private theorem $n7 : (cell4Tensor.coeff $k).coeff 7 = cell4PowerCoeff $k 7 := by cell4_tensor_coeff
  @[simp] private theorem $n8 : (cell4Tensor.coeff $k).coeff 8 = cell4PowerCoeff $k 8 := by cell4_tensor_coeff
  )
cell4_tensor_row_coeffs 0 cell4Tensor_power_coeff_0_0 cell4Tensor_power_coeff_0_1 cell4Tensor_power_coeff_0_2 cell4Tensor_power_coeff_0_3 cell4Tensor_power_coeff_0_4 cell4Tensor_power_coeff_0_5 cell4Tensor_power_coeff_0_6 cell4Tensor_power_coeff_0_7 cell4Tensor_power_coeff_0_8 cell4_tensor_row_coeffs 1 cell4Tensor_power_coeff_1_0 cell4Tensor_power_coeff_1_1 cell4Tensor_power_coeff_1_2 cell4Tensor_power_coeff_1_3 cell4Tensor_power_coeff_1_4 cell4Tensor_power_coeff_1_5 cell4Tensor_power_coeff_1_6 cell4Tensor_power_coeff_1_7 cell4Tensor_power_coeff_1_8 cell4_tensor_row_coeffs 2 cell4Tensor_power_coeff_2_0 cell4Tensor_power_coeff_2_1 cell4Tensor_power_coeff_2_2 cell4Tensor_power_coeff_2_3 cell4Tensor_power_coeff_2_4 cell4Tensor_power_coeff_2_5 cell4Tensor_power_coeff_2_6 cell4Tensor_power_coeff_2_7 cell4Tensor_power_coeff_2_8 cell4_tensor_row_coeffs 3 cell4Tensor_power_coeff_3_0 cell4Tensor_power_coeff_3_1 cell4Tensor_power_coeff_3_2 cell4Tensor_power_coeff_3_3 cell4Tensor_power_coeff_3_4 cell4Tensor_power_coeff_3_5 cell4Tensor_power_coeff_3_6 cell4Tensor_power_coeff_3_7 cell4Tensor_power_coeff_3_8 cell4_tensor_row_coeffs 4 cell4Tensor_power_coeff_4_0 cell4Tensor_power_coeff_4_1 cell4Tensor_power_coeff_4_2 cell4Tensor_power_coeff_4_3 cell4Tensor_power_coeff_4_4 cell4Tensor_power_coeff_4_5 cell4Tensor_power_coeff_4_6 cell4Tensor_power_coeff_4_7 cell4Tensor_power_coeff_4_8 cell4_tensor_row_coeffs 5 cell4Tensor_power_coeff_5_0 cell4Tensor_power_coeff_5_1 cell4Tensor_power_coeff_5_2 cell4Tensor_power_coeff_5_3 cell4Tensor_power_coeff_5_4 cell4Tensor_power_coeff_5_5 cell4Tensor_power_coeff_5_6 cell4Tensor_power_coeff_5_7 cell4Tensor_power_coeff_5_8 cell4_tensor_row_coeffs 6 cell4Tensor_power_coeff_6_0 cell4Tensor_power_coeff_6_1 cell4Tensor_power_coeff_6_2 cell4Tensor_power_coeff_6_3 cell4Tensor_power_coeff_6_4 cell4Tensor_power_coeff_6_5 cell4Tensor_power_coeff_6_6 cell4Tensor_power_coeff_6_7 cell4Tensor_power_coeff_6_8 cell4_tensor_row_coeffs 7 cell4Tensor_power_coeff_7_0 cell4Tensor_power_coeff_7_1 cell4Tensor_power_coeff_7_2 cell4Tensor_power_coeff_7_3 cell4Tensor_power_coeff_7_4 cell4Tensor_power_coeff_7_5 cell4Tensor_power_coeff_7_6 cell4Tensor_power_coeff_7_7 cell4Tensor_power_coeff_7_8 cell4_tensor_row_coeffs 8 cell4Tensor_power_coeff_8_0 cell4Tensor_power_coeff_8_1 cell4Tensor_power_coeff_8_2 cell4Tensor_power_coeff_8_3 cell4Tensor_power_coeff_8_4 cell4Tensor_power_coeff_8_5 cell4Tensor_power_coeff_8_6 cell4Tensor_power_coeff_8_7 cell4Tensor_power_coeff_8_8 cell4_tensor_row_coeffs 9 cell4Tensor_power_coeff_9_0 cell4Tensor_power_coeff_9_1 cell4Tensor_power_coeff_9_2 cell4Tensor_power_coeff_9_3 cell4Tensor_power_coeff_9_4 cell4Tensor_power_coeff_9_5 cell4Tensor_power_coeff_9_6 cell4Tensor_power_coeff_9_7 cell4Tensor_power_coeff_9_8 cell4_tensor_row_coeffs 10 cell4Tensor_power_coeff_10_0 cell4Tensor_power_coeff_10_1 cell4Tensor_power_coeff_10_2 cell4Tensor_power_coeff_10_3 cell4Tensor_power_coeff_10_4 cell4Tensor_power_coeff_10_5 cell4Tensor_power_coeff_10_6 cell4Tensor_power_coeff_10_7 cell4Tensor_power_coeff_10_8 cell4_tensor_row_coeffs 11 cell4Tensor_power_coeff_11_0 cell4Tensor_power_coeff_11_1 cell4Tensor_power_coeff_11_2 cell4Tensor_power_coeff_11_3 cell4Tensor_power_coeff_11_4 cell4Tensor_power_coeff_11_5 cell4Tensor_power_coeff_11_6 cell4Tensor_power_coeff_11_7 cell4Tensor_power_coeff_11_8 cell4_tensor_row_coeffs 12 cell4Tensor_power_coeff_12_0 cell4Tensor_power_coeff_12_1 cell4Tensor_power_coeff_12_2 cell4Tensor_power_coeff_12_3 cell4Tensor_power_coeff_12_4 cell4Tensor_power_coeff_12_5 cell4Tensor_power_coeff_12_6 cell4Tensor_power_coeff_12_7 cell4Tensor_power_coeff_12_8
private theorem cell4Tensor_natDegree : cell4Tensor.natDegree ≤ 12 := by rw [cell4Tensor, tensorBernsteinPolynomial]; apply Polynomial.natDegree_sum_le_of_forall_le; intro i hi; apply Polynomial.natDegree_sum_le_of_forall_le; intro j hj; exact (Polynomial.natDegree_mul_le_of_le (m := 0) (n := 12) (Polynomial.natDegree_C _).le (cell4BernsteinPolynomial_natDegree_le (Polynomial Rat) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))).trans (by simp)
private theorem cell4Tensor_eq_power : cell4Tensor = cell4Power := by
  ext k l
  by_cases hk : k < 13
  · by_cases hl : l < 9
    · rw [cell4Power_outer_coeff k hk, cell4Power_row_coeff k l, if_pos hl]
      interval_cases k <;> interval_cases l <;> simp
    · have hl' : 9 ≤ l := Nat.le_of_not_gt hl
      have hp : (cell4Power.coeff k).coeff l = 0 := by rw [cell4Power_outer_coeff k hk, cell4Power_row_coeff k l, if_neg hl]
      have ht : (cell4Tensor.coeff k).coeff l = 0 := by rw [cell4Tensor, cell4_tensor_coeff_formula]; apply Finset.sum_eq_zero; intro a ha; apply Finset.sum_eq_zero; intro b hb; rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((cell4BernsteinPolynomial_natDegree_le Rat (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))).trans_lt (Nat.lt_of_succ_le hl'))]; ring
      rw [hp, ht]
  · have hk' : 13 ≤ k := Nat.le_of_not_gt hk
    have hp : (cell4Power.coeff k).coeff l = 0 := by rw [cell4Power, Polynomial.finsetSum_coeff]; simp_rw [Polynomial.coeff_C_mul_X_pow]; rw [Polynomial.finsetSum_coeff]; apply Finset.sum_eq_zero; intro i hi; have hi' : i < 13 := Finset.mem_range.mp hi; have hik : k ≠ i := Nat.ne_of_gt (lt_of_lt_of_le hi' hk'); simp [hik]
    have htk : cell4Tensor.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (cell4Tensor_natDegree.trans_lt (Nat.lt_of_succ_le hk'))
    rw [hp, htk]; simp
private theorem cell4PFull_natDegree : cell4PFull.natDegree ≤ 4 := by rw [cell4PFull]; apply Polynomial.natDegree_sum_le_of_forall_le; intro i hi; exact (Polynomial.natDegree_mul_le_of_le (m := 0) (n := i) (Polynomial.natDegree_C _).le (Polynomial.natDegree_X_pow_le i)).trans (by simpa using (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
private theorem cell4QFull_natDegree : cell4QFull.natDegree ≤ 5 := by rw [cell4QFull]; apply Polynomial.natDegree_sum_le_of_forall_le; intro i hi; exact (Polynomial.natDegree_mul_le_of_le (m := 0) (n := i) (Polynomial.natDegree_C _).le (Polynomial.natDegree_X_pow_le i)).trans (by simpa using (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
private theorem cell4SignedCurvature_natDegree : cell4SignedCurvature.natDegree ≤ 12 := by
  let p := cell4RationalPolynomials.1; let q := cell4RationalPolynomials.2; have hc (a : Rat) : (cell4Constant a).natDegree ≤ 0 := (by simp [cell4Constant])
  have hp : p.natDegree ≤ 4 := (by simpa [p, cell4RationalPolynomials] using cell4PFull_natDegree); have hq : q.natDegree ≤ 5 := (by simpa [q, cell4RationalPolynomials] using cell4QFull_natDegree)
  have hp1 : p.derivative.natDegree ≤ 3 := (Polynomial.natDegree_derivative_le p).trans (by simpa using Nat.sub_le_sub_right hp 1); have hp2 : p.derivative.derivative.natDegree ≤ 2 := (Polynomial.natDegree_derivative_le p.derivative).trans (by simpa using Nat.sub_le_sub_right hp1 1); have hq1 : q.derivative.natDegree ≤ 4 := (Polynomial.natDegree_derivative_le q).trans (by simpa using Nat.sub_le_sub_right hq 1); have hq2 : q.derivative.derivative.natDegree ≤ 3 := (Polynomial.natDegree_derivative_le q.derivative).trans (by simpa using Nat.sub_le_sub_right hq1 1)
  have h1 : (p.derivative.derivative * q ^ 2).natDegree ≤ 12 := Polynomial.natDegree_mul_le_of_le (p := p.derivative.derivative) (q := q ^ 2) (m := 2) (n := 10) hp2 (Polynomial.natDegree_pow_le_of_le (p := q) (m := 5) 2 hq); have h2 : (cell4Constant 2 * p.derivative * q * q.derivative).natDegree ≤ 12 := Polynomial.natDegree_mul_le_of_le (p := cell4Constant 2 * p.derivative * q) (q := q.derivative) (m := 8) (n := 4) (Polynomial.natDegree_mul_le_of_le (p := cell4Constant 2 * p.derivative) (q := q) (m := 3) (n := 5) (Polynomial.natDegree_mul_le_of_le (p := cell4Constant 2) (q := p.derivative) (m := 0) (n := 3) (hc 2) hp1) hq) hq1; have h3 : (cell4Constant 2 * p * q.derivative ^ 2).natDegree ≤ 12 := Polynomial.natDegree_mul_le_of_le (p := cell4Constant 2 * p) (q := q.derivative ^ 2) (m := 4) (n := 8) (Polynomial.natDegree_mul_le_of_le (p := cell4Constant 2) (q := p) (m := 0) (n := 4) (hc 2) hp) (Polynomial.natDegree_pow_le_of_le (p := q.derivative) (m := 4) 2 hq1); have h4 : (p * q * q.derivative.derivative).natDegree ≤ 12 := Polynomial.natDegree_mul_le_of_le (p := p * q) (q := q.derivative.derivative) (m := 9) (n := 3) (Polynomial.natDegree_mul_le_of_le (p := p) (q := q) (m := 4) (n := 5) hp hq) hq2
  have h12 := Polynomial.natDegree_sub_le_of_le (m := 12) (n := 12) h1 h2; have h123 := Polynomial.natDegree_add_le_of_degree_le h12 h3; change (p.derivative.derivative * q ^ 2 - cell4Constant 2 * p.derivative * q * q.derivative + cell4Constant 2 * p * q.derivative ^ 2 - p * q * q.derivative.derivative).natDegree ≤ 12; exact Polynomial.natDegree_sub_le_of_le (m := 12) (n := 12) h123 h4
private theorem cell4FiniteOuter_coeff (n i : Nat) (a : Nat → Polynomial Rat) : (∑ j ∈ Finset.range n, C (a j) * X ^ j).coeff i = if i < n then a i else 0 := by
  rw [Polynomial.finsetSum_coeff]; simp_rw [Polynomial.coeff_C_mul_X_pow]; by_cases hi : i < n
  · rw [if_pos hi, Finset.sum_eq_single i]
    · simp
    · intro b hb hbi; simp [Ne.symm hbi]
    · exact fun hnot => (hnot (Finset.mem_range.mpr hi)).elim
  · rw [if_neg hi]; apply Finset.sum_eq_zero; intro b hb
    have hbi : i ≠ b := by rintro rfl; exact hi (Finset.mem_range.mp hb)
    rw [if_neg hbi]
private def cell4PCoeff (i : Nat) : Polynomial Rat := if i < 5 then cell4PRow i else 0
private def cell4QCoeff (i : Nat) : Polynomial Rat := if i < 6 then cell4QRow i else 0
private theorem cell4PFull_coeff (i : Nat) : cell4PFull.coeff i = cell4PCoeff i := by simpa only [cell4PFull, cell4PCoeff] using cell4FiniteOuter_coeff 5 i cell4PRow
private theorem cell4QFull_coeff (i : Nat) : cell4QFull.coeff i = cell4QCoeff i := by simpa only [cell4QFull, cell4QCoeff] using cell4FiniteOuter_coeff 6 i cell4QRow
private def cell4OuterConst (a : Rat) (i : Nat) : Polynomial Rat := if i = 0 then C a else 0
private def cell4OuterConv (p q : Nat → Polynomial Rat) (k : Nat) : Polynomial Rat := ∑ a ∈ Finset.antidiagonal k, p a.1 * q a.2
private theorem cell4_coeff_mul_outer (p q : BivariateRat) (k : Nat) : (p * q).coeff k = cell4OuterConv (fun i => p.coeff i) (fun i => q.coeff i) k := by simp only [cell4OuterConv, Polynomial.coeff_mul]
private theorem cell4PCoeff_coeff (i l : Nat) : (cell4PCoeff i).coeff l = if i < 5 then (if l < 4 then cell4PScale * (cell4PNumerator i l : Rat) else 0) else 0 := by by_cases hi : i < 5 <;> simp [cell4PCoeff, hi, cell4PRow_coeff]
private theorem cell4QCoeff_coeff (i l : Nat) : (cell4QCoeff i).coeff l = if i < 6 then (if l < 4 then cell4QScale * (cell4QNumerator i l : Rat) else 0) else 0 := by by_cases hi : i < 6 <;> simp [cell4QCoeff, hi, cell4QRow_coeff]
private theorem cell4OuterConst_coeff (a : Rat) (i l : Nat) : (cell4OuterConst a i).coeff l = if i = 0 then (if l = 0 then a else 0) else 0 := by by_cases hi : i = 0 <;> by_cases hl : l = 0 <;> simp [cell4OuterConst, Polynomial.coeff_C, hi, hl]
private def cell4ScalarConv (p q : Nat → Nat → Rat) (k l : Nat) : Rat := ∑ a ∈ Finset.antidiagonal k, ∑ b ∈ Finset.antidiagonal l, p a.1 b.1 * q a.2 b.2
private theorem cell4OuterConv_coeff (p q : Nat → Polynomial Rat) (k l : Nat) : (cell4OuterConv p q k).coeff l = cell4ScalarConv (fun i j => (p i).coeff j) (fun i j => (q i).coeff j) k l := by rw [cell4OuterConv, cell4ScalarConv, Polynomial.finsetSum_coeff]; simp_rw [Polynomial.coeff_mul]
private def cell4PDerivCoeff (i : Nat) : Polynomial Rat := cell4PCoeff (i + 1) * (i + 1 : Nat)
private def cell4QDerivCoeff (i : Nat) : Polynomial Rat := cell4QCoeff (i + 1) * (i + 1 : Nat)
private def cell4PDeriv2Coeff (i : Nat) : Polynomial Rat := cell4PDerivCoeff (i + 1) * (i + 1 : Nat)
private def cell4QDeriv2Coeff (i : Nat) : Polynomial Rat := cell4QDerivCoeff (i + 1) * (i + 1 : Nat)
private theorem cell4Constant_outer_coeff (a : Rat) (i : Nat) : (cell4Constant a).coeff i = cell4OuterConst a i := by by_cases hi : i = 0 <;> simp [cell4Constant, cell4OuterConst, hi, Polynomial.coeff_C_of_ne_zero]
private theorem cell4PFull_deriv_coeff (i : Nat) : cell4PFull.derivative.coeff i = cell4PDerivCoeff i := by simp [Polynomial.coeff_derivative, cell4PDerivCoeff, cell4PFull_coeff]
private theorem cell4QFull_deriv_coeff (i : Nat) : cell4QFull.derivative.coeff i = cell4QDerivCoeff i := by simp [Polynomial.coeff_derivative, cell4QDerivCoeff, cell4QFull_coeff]
private theorem cell4PFull_deriv2_coeff (i : Nat) : cell4PFull.derivative.derivative.coeff i = cell4PDeriv2Coeff i := by simp only [Polynomial.coeff_derivative, cell4PDeriv2Coeff, cell4PDerivCoeff, cell4PFull_coeff]; push_cast; ring
private theorem cell4QFull_deriv2_coeff (i : Nat) : cell4QFull.derivative.derivative.coeff i = cell4QDeriv2Coeff i := by simp only [Polynomial.coeff_derivative, cell4QDeriv2Coeff, cell4QDerivCoeff, cell4QFull_coeff]; push_cast; ring
private theorem cell4PDerivCoeff_coeff (i l : Nat) : (cell4PDerivCoeff i).coeff l = (cell4PCoeff (i + 1)).coeff l * (i + 1 : Nat) := by rw [cell4PDerivCoeff, ← Polynomial.C_eq_natCast, Polynomial.coeff_mul_C]
private theorem cell4QDerivCoeff_coeff (i l : Nat) : (cell4QDerivCoeff i).coeff l = (cell4QCoeff (i + 1)).coeff l * (i + 1 : Nat) := by rw [cell4QDerivCoeff, ← Polynomial.C_eq_natCast, Polynomial.coeff_mul_C]
private theorem cell4PDeriv2Coeff_coeff (i l : Nat) : (cell4PDeriv2Coeff i).coeff l = (cell4PDerivCoeff (i + 1)).coeff l * (i + 1 : Nat) := by rw [cell4PDeriv2Coeff, ← Polynomial.C_eq_natCast, Polynomial.coeff_mul_C]
private theorem cell4QDeriv2Coeff_coeff (i l : Nat) : (cell4QDeriv2Coeff i).coeff l = (cell4QDerivCoeff (i + 1)).coeff l * (i + 1 : Nat) := by rw [cell4QDeriv2Coeff, ← Polynomial.C_eq_natCast, Polynomial.coeff_mul_C]
private def cell4TwoPdCoeff (i : Nat) : Polynomial Rat := C 2 * cell4PDerivCoeff i
private def cell4TwoPCoeff (i : Nat) : Polynomial Rat := C 2 * cell4PCoeff i
private theorem cell4TwoPdCoeff_coeff (i l : Nat) : (cell4TwoPdCoeff i).coeff l = 2 * (cell4PDerivCoeff i).coeff l := by simp [cell4TwoPdCoeff, Polynomial.coeff_C_mul]
private theorem cell4TwoPCoeff_coeff (i l : Nat) : (cell4TwoPCoeff i).coeff l = 2 * (cell4PCoeff i).coeff l := by simp [cell4TwoPCoeff, Polynomial.coeff_C_mul]
private def cell4SignedOuterRaw (k : Nat) : Polynomial Rat := cell4OuterConv cell4PDeriv2Coeff (fun j => cell4OuterConv cell4QCoeff cell4QCoeff j) k - cell4OuterConv (fun j => cell4OuterConv (fun h => cell4OuterConv (cell4OuterConst 2) cell4PDerivCoeff h) cell4QCoeff j) cell4QDerivCoeff k + cell4OuterConv (fun j => cell4OuterConv (cell4OuterConst 2) cell4PCoeff j) (fun j => cell4OuterConv cell4QDerivCoeff cell4QDerivCoeff j) k - cell4OuterConv (fun j => cell4OuterConv cell4PCoeff cell4QCoeff j) cell4QDeriv2Coeff k
private theorem cell4SignedCurvature_coeff_raw (k : Nat) : cell4SignedCurvature.coeff k = cell4SignedOuterRaw k := by rw [cell4SignedCurvature, cell4RationalPolynomials]; simp only [cell4SignedOuterRaw, Polynomial.coeff_sub, Polynomial.coeff_add, cell4_coeff_mul_outer, pow_two, cell4PFull_coeff, cell4QFull_coeff, cell4PFull_deriv_coeff, cell4QFull_deriv_coeff, cell4PFull_deriv2_coeff, cell4QFull_deriv2_coeff, cell4Constant_outer_coeff]
private theorem cell4TwoPd_outer_eq (i : Nat) : cell4OuterConv (cell4OuterConst 2) cell4PDerivCoeff i = cell4TwoPdCoeff i := by have h := cell4_coeff_mul_outer (cell4Constant 2) cell4PFull.derivative i; simp_rw [cell4Constant_outer_coeff, cell4PFull_deriv_coeff] at h; rw [cell4Constant, Polynomial.coeff_C_mul, cell4PFull_deriv_coeff] at h; simpa only [cell4TwoPdCoeff] using h.symm
private theorem cell4TwoP_outer_eq (i : Nat) : cell4OuterConv (cell4OuterConst 2) cell4PCoeff i = cell4TwoPCoeff i := by have h := cell4_coeff_mul_outer (cell4Constant 2) cell4PFull i; simp_rw [cell4Constant_outer_coeff, cell4PFull_coeff] at h; rw [cell4Constant, Polynomial.coeff_C_mul, cell4PFull_coeff] at h; simpa only [cell4TwoPCoeff] using h.symm
private def cell4StageProductRow (s k : Nat) : Polynomial Rat := match s with | 0 => cell4OuterConv cell4QCoeff cell4QCoeff k | 1 => cell4OuterConv cell4TwoPdCoeff cell4QCoeff k | 2 => cell4OuterConv cell4QDerivCoeff cell4QDerivCoeff k | 3 => cell4OuterConv cell4PCoeff cell4QCoeff k | _ => 0
private def cell4SignedOuterRow (k : Nat) : Polynomial Rat := cell4OuterConv cell4PDeriv2Coeff (cell4StageProductRow 0) k - cell4OuterConv (cell4StageProductRow 1) cell4QDerivCoeff k + cell4OuterConv cell4TwoPCoeff (cell4StageProductRow 2) k - cell4OuterConv (cell4StageProductRow 3) cell4QDeriv2Coeff k
private theorem cell4SignedOuterRaw_eq (k : Nat) : cell4SignedOuterRaw k = cell4SignedOuterRow k := by have hpd : (fun i : Nat => cell4OuterConv (cell4OuterConst 2) cell4PDerivCoeff i) = cell4TwoPdCoeff := funext cell4TwoPd_outer_eq; have hp : (fun i : Nat => cell4OuterConv (cell4OuterConst 2) cell4PCoeff i) = cell4TwoPCoeff := funext cell4TwoP_outer_eq; have h0 : cell4StageProductRow 0 = (fun j : Nat => cell4OuterConv cell4QCoeff cell4QCoeff j) := (by funext j; rfl); have h1 : cell4StageProductRow 1 = (fun j : Nat => cell4OuterConv cell4TwoPdCoeff cell4QCoeff j) := (by funext j; rfl); have h2 : cell4StageProductRow 2 = (fun j : Nat => cell4OuterConv cell4QDerivCoeff cell4QDerivCoeff j) := (by funext j; rfl); have h3 : cell4StageProductRow 3 = (fun j : Nat => cell4OuterConv cell4PCoeff cell4QCoeff j) := (by funext j; rfl); unfold cell4SignedOuterRaw cell4SignedOuterRow; rw [hpd, hp, h0, h1, h2, h3]
private theorem cell4SignedCurvature_coeff_formula (k : Nat) : cell4SignedCurvature.coeff k = cell4SignedOuterRow k := (cell4SignedCurvature_coeff_raw k).trans (cell4SignedOuterRaw_eq k)
private def cell4InnerDegreeLe (n : Nat) (p : BivariateRat) : Prop := ∀ i, (p.coeff i).natDegree ≤ n
private theorem cell4InnerDegreeLe_add {n : Nat} {p q : BivariateRat} (hp : cell4InnerDegreeLe n p) (hq : cell4InnerDegreeLe n q) : cell4InnerDegreeLe n (p + q) := by intro i; rw [Polynomial.coeff_add]; exact Polynomial.natDegree_add_le_of_degree_le (hp i) (hq i)
private theorem cell4InnerDegreeLe_sub {n : Nat} {p q : BivariateRat} (hp : cell4InnerDegreeLe n p) (hq : cell4InnerDegreeLe n q) : cell4InnerDegreeLe n (p - q) := by intro i; rw [Polynomial.coeff_sub]; simpa using Polynomial.natDegree_sub_le_of_le (m := n) (n := n) (hp i) (hq i)
private theorem cell4InnerDegreeLe_mul {m n : Nat} {p q : BivariateRat} (hp : cell4InnerDegreeLe m p) (hq : cell4InnerDegreeLe n q) : cell4InnerDegreeLe (m + n) (p * q) := by intro i; rw [Polynomial.coeff_mul]; apply Polynomial.natDegree_sum_le_of_forall_le; intro j hj; exact Polynomial.natDegree_mul_le_of_le (hp j.1) (hq j.2)
private theorem cell4InnerDegreeLe_derivative {n : Nat} {p : BivariateRat} (hp : cell4InnerDegreeLe n p) : cell4InnerDegreeLe n p.derivative := by intro i; rw [Polynomial.coeff_derivative]; have hs : (C ((i + 1 : Nat) : Rat)).natDegree ≤ 0 := (Polynomial.natDegree_C _).le; simpa using Polynomial.natDegree_mul_le_of_le (hp (i + 1)) hs
private theorem cell4Row_natDegree (a : Nat → Rat) : (∑ j ∈ Finset.range 4, C (a j) * X ^ j).natDegree ≤ 3 := by apply Polynomial.natDegree_sum_le_of_forall_le; intro j hj; exact (Polynomial.natDegree_mul_le_of_le (m := 0) (n := j) (Polynomial.natDegree_C _).le (Polynomial.natDegree_X_pow_le j)).trans (by simpa using (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
private theorem cell4PFull_innerDegree : cell4InnerDegreeLe 3 cell4PFull := by
  intro i; rw [cell4PFull_coeff, cell4PCoeff]; split_ifs
  · simpa only [cell4PRow] using cell4Row_natDegree (fun j => cell4PScale * (cell4PNumerator i j : Rat))
  · simp
private theorem cell4QFull_innerDegree : cell4InnerDegreeLe 3 cell4QFull := by
  intro i; rw [cell4QFull_coeff, cell4QCoeff]; split_ifs
  · simpa only [cell4QRow] using cell4Row_natDegree (fun j => cell4QScale * (cell4QNumerator i j : Rat))
  · simp
private theorem cell4SignedCurvature_innerDegree : cell4InnerDegreeLe 9 cell4SignedCurvature := by
  have hp1 := cell4InnerDegreeLe_derivative cell4PFull_innerDegree; have hp2 := cell4InnerDegreeLe_derivative hp1; have hq1 := cell4InnerDegreeLe_derivative cell4QFull_innerDegree; have hq2 := cell4InnerDegreeLe_derivative hq1
  have hc : cell4InnerDegreeLe 0 (cell4Constant 2) := (by intro i; cases i <;> simp [cell4Constant])
  have h1 : cell4InnerDegreeLe 9 (cell4PFull.derivative.derivative * cell4QFull ^ 2) := (by simpa [pow_two] using cell4InnerDegreeLe_mul hp2 (cell4InnerDegreeLe_mul cell4QFull_innerDegree cell4QFull_innerDegree)); have h2 : cell4InnerDegreeLe 9 (cell4Constant 2 * cell4PFull.derivative * cell4QFull * cell4QFull.derivative) := (by simpa using cell4InnerDegreeLe_mul (cell4InnerDegreeLe_mul (cell4InnerDegreeLe_mul hc hp1) cell4QFull_innerDegree) hq1); have h3 : cell4InnerDegreeLe 9 (cell4Constant 2 * cell4PFull * cell4QFull.derivative ^ 2) := (by simpa [pow_two] using cell4InnerDegreeLe_mul (cell4InnerDegreeLe_mul hc cell4PFull_innerDegree) (cell4InnerDegreeLe_mul hq1 hq1)); have h4 : cell4InnerDegreeLe 9 (cell4PFull * cell4QFull * cell4QFull.derivative.derivative) := (by simpa using cell4InnerDegreeLe_mul (cell4InnerDegreeLe_mul cell4PFull_innerDegree cell4QFull_innerDegree) hq2)
  rw [cell4SignedCurvature, cell4RationalPolynomials]; exact cell4InnerDegreeLe_sub (cell4InnerDegreeLe_add (cell4InnerDegreeLe_sub h1 h2) h3) h4
private theorem cell4PCoeff_natDegree (i : Nat) : (cell4PCoeff i).natDegree ≤ 3 := by rw [← cell4PFull_coeff]; exact cell4PFull_innerDegree i
private theorem cell4QCoeff_natDegree (i : Nat) : (cell4QCoeff i).natDegree ≤ 3 := by rw [← cell4QFull_coeff]; exact cell4QFull_innerDegree i
private theorem cell4PDerivCoeff_natDegree (i : Nat) : (cell4PDerivCoeff i).natDegree ≤ 3 := by rw [← cell4PFull_deriv_coeff]; exact (cell4InnerDegreeLe_derivative cell4PFull_innerDegree) i
private theorem cell4QDerivCoeff_natDegree (i : Nat) : (cell4QDerivCoeff i).natDegree ≤ 3 := by rw [← cell4QFull_deriv_coeff]; exact (cell4InnerDegreeLe_derivative cell4QFull_innerDegree) i
private theorem cell4TwoPdCoeff_natDegree (i : Nat) : (cell4TwoPdCoeff i).natDegree ≤ 3 := by rw [cell4TwoPdCoeff]; simpa using Polynomial.natDegree_mul_le_of_le (m := 0) (n := 3) (Polynomial.natDegree_C _).le (cell4PDerivCoeff_natDegree i)
private theorem cell4OuterConv_natDegree (p q : Nat → Polynomial Rat) (m n : Nat) (hp : ∀ i, (p i).natDegree ≤ m) (hq : ∀ i, (q i).natDegree ≤ n) (k : Nat) : (cell4OuterConv p q k).natDegree ≤ m + n := by rw [cell4OuterConv]; apply Polynomial.natDegree_sum_le_of_forall_le; intro a ha; exact Polynomial.natDegree_mul_le_of_le (hp a.1) (hq a.2)
private theorem cell4StageProductRow_natDegree (s k : Nat) : (cell4StageProductRow s k).natDegree ≤ 6 := by
  rcases s with (_ | _ | _ | _ | s)
  · simpa [cell4StageProductRow] using cell4OuterConv_natDegree cell4QCoeff cell4QCoeff 3 3 cell4QCoeff_natDegree cell4QCoeff_natDegree k
  · simpa [cell4StageProductRow] using cell4OuterConv_natDegree cell4TwoPdCoeff cell4QCoeff 3 3 cell4TwoPdCoeff_natDegree cell4QCoeff_natDegree k
  · simpa [cell4StageProductRow] using cell4OuterConv_natDegree cell4QDerivCoeff cell4QDerivCoeff 3 3 cell4QDerivCoeff_natDegree cell4QDerivCoeff_natDegree k
  · simpa [cell4StageProductRow] using cell4OuterConv_natDegree cell4PCoeff cell4QCoeff 3 3 cell4PCoeff_natDegree cell4QCoeff_natDegree k
  · simp [cell4StageProductRow]
private def cell4StageValue (s i j : Nat) : Rat :=
  match s with
  | 0 => let row : List Int := match i with | 0 => [3237008859066988396935433915136753906250000000000000000, 6855057344676697690255994084765203125000000000000000000, 5897550526017835826997604302101666015625000000000000000, 2641972032850989135692521356586576171875000000000000000, 651683332204195830442701812574435791015625000000000000, 84151133363116708511678829157258300781250000000000000, 4455199768822779899053361811904541015625000000000000] | 1 => [1899079725413796574078355208175323750375000000000000000, -2680959104124885324940906179276603754500000000000000000, -8072930626477268686828976947887677790562500000000000000, -6199733768727037445922033110775885524437500000000000000, -2166456456339028142378617837264854297164062500000000000, -362032487747300311935332754314965486640625000000000000, -23523185493223069832499181371984475101562500000000000] | 2 => [-139268378636645633827844819739801308792500500000000000, -4227232661927387789764681346545420539989994000000000000, -1381566152256790943116616426411999733236279250000000000, 2917186563198478162889539993639797178998824250000000000, 2214833391292334875015506681015242719912864968750000000, 559531980731005246810116716152198081064138437500000000, 48364144840850456799979780873051437501070968750000000] | 3 => [-122558401494306344098644686888140988558341120008000000, 28830485667684956300044003069023344750113440096000000, 3580733511853764570508648430980573959599349479532000000, 2209241644869637946099704237615085021270648821188000000, -158629184225027090929033583365213559538937471660500000, -300124639693349080589354659981040198599114273785000000, -44854121329414675256425030857566886797685405364500000] | 4 => [13481669281176686463539112847069285023394639883120016, 282324105437049722036276004305020179791558681290559808, 218637305789898079578778221031320577468917924254520936, -1470484908900648572471346161464080307181710411801322376, -895547181619089050660759496233054379167976459010901679, -95612750717760560376940509409992167358414720586352430, 10474208971123426105018495699783074330691455976155729] | 5 => [0, -27915624718572753083303535384228923263515728100799872, -261506231242264164493920735314992995747922651537201248, -212916310880173174507871924792887646094627401782195248, 302135370811553438663812434905271128932733176904091144, 152084637293415360991402951186084394354745344621258100, 13001271419571953524581299739483955694780799721347084] | 6 => [0, 0, 23482504125785132989275373937858148872954897783680416, 125064359295997491330413456180158626357368326503356832, 82200641445588355051284612130786932273165387290888856, -27532613118132865419007449843838246450664031084010800, -9330451364561517135615180573157045345272096757195140] | 7 => [0, 0, 0, -10285784732123907982172935663782306673497696577759296, -32700419281697931760476105678797029239192217718163936, -14601079018847001345085530067679545240223892017992800, 652227688301360133222038743014199082303933770795680] | 8 => [0, 0, 0, 0, 2480746036464067807380830349596438381454513709840656, 4449034300380240423570037039714825536164244203997600, 991382359506108748904699954156924198612790900402160] | 9 => [0, 0, 0, 0, 0, -313214702649527977058493015710383733038811909599680, -246890698216277278046749798441016447017258738720576] | 10 => [0, 0, 0, 0, 0, 0, 16213838051404183799635927093385677768712035200064] | _ => []; (45155825001 / 15258789062500000000000000000000000000000000000000000000000000000000 : Rat) * (row.getD j 0 : Rat)
  | 1 => let row : List Int := match i with | 0 => [0, -54840458757413581522047952678121625000000000, -101619332140615017326727951051597937500000000, -67890675268413296577795700314709593750000000, -20006148474821491510175951579520890625000000, -2513313849778419027548807697496781250000000, -95044261734885971179805051987296875000000] | 1 => [0, 37534499884287106051762766475542790018000000, 168911684038524246248472928933964579811000000, 179229330946594415325913459061442278215500000, 72377028781635196440709267983133656305250000, 11549955767661571049451068780447078350500000, 529708114200387960697904976812219817750000] | 2 => [0, 19268374846770598033449140513622186503879928, -32300953336711757574017181912550995475739244, -131919118577905781842696764477882126355772862, -90515675951650976466769288177168995096280221, -20261602201179997224343137147578518361673402, -1193286041276719072396304529332496208034271] | 3 => [0, -3460488797433578814920861375012804443079952, -41322843842806094842878315084700947031321008, -6507150497606723590959078459884386021284276, 36092435455327692677101741595112206893727256, 15652618196081591906649327770982765442361340, 1341109931356977608952096949271965057107084] | 4 => [0, 0, 6269734965498707658841858434202301188320336, 31182314969398447487416328324976740338076184, 11063772795217510565050352926102762859292744, -3043480273085426094745618578129517334415120, -693858716635404995133558840397551871795140] | 5 => [0, 0, 0, -4095618090389199424138452181891885807399152, -10191492739718225678493871483665360598805664, -2639338362431735947517496532622202773989920, 12724575245492063482196764092942785995680] | 6 => [0, 0, 0, 0, 1180074129963078635939001666238065410320944, 1400114305524395844104566232905194367196640, 150538375057437891589444679229428518802160] | 7 => [0, 0, 0, 0, 0, -144953599559812888893983138828192722719552, -57251727788827315853731842711066659360576] | 8 => [0, 0, 0, 0, 0, 0, 5359751561445511812195396293420828160064] | _ => []; (214277616700833 / 3814697265625000000000000000000000000000000000000000000000000 : Rat) * (row.getD j 0 : Rat)
  | 2 => let row : List Int := match i with | 0 => [23018729664476361933763085618750250000000000, -113738840761341024259446090300003000000000000, 49099211796339529810849496728139625000000000, 210441117418117743108708138881212875000000000, 128706748001825441637704879218411265625000000, 30516949397072704335535791281212031250000000, 2566043002331039970943390016027015625000000] | 1 => [-20256850404413830123502455553870120004000000, -66729906330357008985516171451045559952000000, 363677414175537543320673183424096229766000000, 174868354061700547036641373005507945594000000, -86315274874927375821145187655284970830250000, -56594607789629941896495616268824743142500000, -7554793164995541070468943600769123932250000] | 2 => [4456588116372660282491034231673641881360016, 82840750021079650199591410347915357319679808, 122083080795744179783712366235110216073560936, -325137474853580685266527223353040720742962376, -191942990536969016253581209137565038554711679, -8539751220449317432880692365505726687802430, 5001613757263429964283980984407068713715729] | 3 => [0, -13841955189734315259683445500051217772319808, -122882492041675396357147320093480027479881872, -124174051230077192229268394468578494013372872, 115521319864468529010832720031810953458376716, 60009759593949426235117883868451295055387150, 4394380167234417974774514821457403506160626] | 4 => [0, 0, 16719293241329887090244955824539469835520896, 86723559181455651150734015439138203458073184, 62506256713279822042507053138417815960299044, -15839612882521602305666042188543494506423220, -5813462656478241279857214029825846864359551] | 5 => [0, 0, 0, -10045855693407470285622618559357455753997920, -31538035411641621276192393179817658645211616, -14746591066548924352370218339484389849478760, 474177226869310780848030227027629679687256] | 6 => [0, 0, 0, 0, 3200201030408348843224411298272719756802560, 5712205473628977645402294450342565429190640, 1306613346122016659795430231803713777728424] | 7 => [0, 0, 0, 0, 0, -517691426999331746049939781529259723998400, -408068959698429951484514295586133376802880] | 8 => [0, 0, 0, 0, 0, 0, 33498447259034448826221226833880176000400] | _ => []; (136601337813930935001 / 3814697265625000000000000000000000000000000000000000000000000000000 : Rat) * (row.getD j 0 : Rat)
  | 3 => let row : List Int := match i with | 0 => [0, 12339432263170600323949921640293434354750000000000, 19598536669398190790243785160842153307250000000000, 11528912663731775252666791958499280642500000000000, 3051866741508938656771966210916391536250000000000, 343345779764826077825535693618226176890625000000, 10692764577959876415641607763726860328125000000] | 1 => [0, -20510607969429922173459570814593450997290108000000, -51739544508888045277142876563604045902889028000000, -41708599970355790124621772846502830728703240000000, -14024880289556092493927443798721278299445140000000, -1913561557510960101425849864349538283884973250000, -70048810851247173344117318935011797000078250000] | 2 => [0, 3922240161770235298697758365277242278628064920432, 38082132378592846282584298534802908032645795716112, 52161330505897981961252900253180296376852747612960, 24603258320848847029575384575561643276212778580560, 4310725538249445944807419375036643899088267404893, 192517211480025802254492391722791625284615090313] | 3 => [0, 5017750282144258484581028044105066596119247359424, 1878470454689566853916516063822301782072752647776, -20798932723584215230349675897545081634468198434560, -19006661223137955420406145725748952421350527935200, -4844736828158248543720098043596836145393370129572, -282142741719975703341676053919577132695904149794] | 4 => [0, -761321377390577073597849185948317028695361759808, -9001644790662612261683976026349145827306816485184, -6375703471758442786610535447983487470743996765440, 3695637226002171198327709727051110308833591913600, 2506552818247217743035064040435869378478122732620, 225585961866763219107459338835060478444462089588] | 5 => [0, 0, 1182314375442495154093580762535636917687337601152, 5873035974772564714452255447884489388164351984640, 3204895786733608326351545689632488384400480057600, -45967311756560905964356612940766234382032073440, -77757399436171413892619322112159843254080977320] | 6 => [0, 0, 0, -680039518760743720836344176471654675600787197440, -1700130798912163385579292685292119416199536019200, -543817320742618406922711883156763623887983363280, -15536290082932317150318686303596504305702615120] | 7 => [0, 0, 0, 0, 176014256873489594726185845816297859343897602560, 206820893357766268457236768352402218806871670208, 23000513464494722466114487105118728303318086048] | 8 => [0, 0, 0, 0, 0, -19362011399945366847855061788245753574152478912, -6900792690143886813949628831101478093473761344] | 9 => [0, 0, 0, 0, 0, 0, 589583391262129190365117983068877939263360128] | _ => []; (3895885833 / 61035156250000000000000000000000000000000000000000000000000000 : Rat) * (row.getD j 0 : Rat)
  | _ => 0
private def cell4StageRow (s i : Nat) : Polynomial Rat := ∑ j ∈ Finset.range 7, C (cell4StageValue s i j) * X ^ j
@[simp] private theorem cell4StageRow_coeff (s i l : Nat) : (cell4StageRow s i).coeff l = if l < 7 then cell4StageValue s i l else 0 := by simpa only [cell4StageRow] using cell4FiniteRow_coeff 7 l (cell4StageValue s i)
private theorem cell4StageRow_natDegree (s i : Nat) : (cell4StageRow s i).natDegree ≤ 6 := by rw [cell4StageRow]; apply Polynomial.natDegree_sum_le_of_forall_le; intro j hj; exact (Polynomial.natDegree_mul_le_of_le (m := 0) (n := j) (Polynomial.natDegree_C _).le (Polynomial.natDegree_X_pow_le j)).trans (by simpa using (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
attribute [local simp] cell4PCoeff_coeff cell4QCoeff_coeff cell4PDerivCoeff_coeff cell4QDerivCoeff_coeff cell4PDeriv2Coeff_coeff cell4QDeriv2Coeff_coeff cell4TwoPdCoeff_coeff cell4TwoPCoeff_coeff
local macro "cell4_stage_coeff" : tactic =>
  `(tactic|
    (rw [cell4StageProductRow, cell4OuterConv_coeff, cell4ScalarConv]
     simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
     repeat rw [Finset.sum_range_succ]
     all_goals simp
     all_goals norm_num [cell4PScale, cell4QScale, cell4PNumerator, cell4QNumerator, cell4StageValue]
     all_goals ring_nf))
local macro "cell4_stage_row_commands" s:num k:num n0:ident n1:ident n2:ident n3:ident n4:ident n5:ident n6:ident row:ident : command =>
  `(
  @[simp] private theorem $n0 : (cell4StageProductRow $s $k).coeff 0 = cell4StageValue $s $k 0 := by cell4_stage_coeff
  @[simp] private theorem $n1 : (cell4StageProductRow $s $k).coeff 1 = cell4StageValue $s $k 1 := by cell4_stage_coeff
  @[simp] private theorem $n2 : (cell4StageProductRow $s $k).coeff 2 = cell4StageValue $s $k 2 := by cell4_stage_coeff
  @[simp] private theorem $n3 : (cell4StageProductRow $s $k).coeff 3 = cell4StageValue $s $k 3 := by cell4_stage_coeff
  @[simp] private theorem $n4 : (cell4StageProductRow $s $k).coeff 4 = cell4StageValue $s $k 4 := by cell4_stage_coeff
  @[simp] private theorem $n5 : (cell4StageProductRow $s $k).coeff 5 = cell4StageValue $s $k 5 := by cell4_stage_coeff
  @[simp] private theorem $n6 : (cell4StageProductRow $s $k).coeff 6 = cell4StageValue $s $k 6 := by cell4_stage_coeff
  @[simp] private theorem $row : cell4StageProductRow $s $k = cell4StageRow $s $k := by apply (Polynomial.ext_iff_natDegree_le (cell4StageProductRow_natDegree $s $k) (cell4StageRow_natDegree $s $k)).2; intro l hl; interval_cases l <;> simp
  )
cell4_stage_row_commands 0 0 cell4QQ_coeff_0_0 cell4QQ_coeff_0_1 cell4QQ_coeff_0_2 cell4QQ_coeff_0_3 cell4QQ_coeff_0_4 cell4QQ_coeff_0_5 cell4QQ_coeff_0_6 cell4QQ_row0 cell4_stage_row_commands 0 1 cell4QQ_coeff_1_0 cell4QQ_coeff_1_1 cell4QQ_coeff_1_2 cell4QQ_coeff_1_3 cell4QQ_coeff_1_4 cell4QQ_coeff_1_5 cell4QQ_coeff_1_6 cell4QQ_row1 cell4_stage_row_commands 0 2 cell4QQ_coeff_2_0 cell4QQ_coeff_2_1 cell4QQ_coeff_2_2 cell4QQ_coeff_2_3 cell4QQ_coeff_2_4 cell4QQ_coeff_2_5 cell4QQ_coeff_2_6 cell4QQ_row2 cell4_stage_row_commands 0 3 cell4QQ_coeff_3_0 cell4QQ_coeff_3_1 cell4QQ_coeff_3_2 cell4QQ_coeff_3_3 cell4QQ_coeff_3_4 cell4QQ_coeff_3_5 cell4QQ_coeff_3_6 cell4QQ_row3 cell4_stage_row_commands 0 4 cell4QQ_coeff_4_0 cell4QQ_coeff_4_1 cell4QQ_coeff_4_2 cell4QQ_coeff_4_3 cell4QQ_coeff_4_4 cell4QQ_coeff_4_5 cell4QQ_coeff_4_6 cell4QQ_row4 cell4_stage_row_commands 0 5 cell4QQ_coeff_5_0 cell4QQ_coeff_5_1 cell4QQ_coeff_5_2 cell4QQ_coeff_5_3 cell4QQ_coeff_5_4 cell4QQ_coeff_5_5 cell4QQ_coeff_5_6 cell4QQ_row5 cell4_stage_row_commands 0 6 cell4QQ_coeff_6_0 cell4QQ_coeff_6_1 cell4QQ_coeff_6_2 cell4QQ_coeff_6_3 cell4QQ_coeff_6_4 cell4QQ_coeff_6_5 cell4QQ_coeff_6_6 cell4QQ_row6 cell4_stage_row_commands 0 7 cell4QQ_coeff_7_0 cell4QQ_coeff_7_1 cell4QQ_coeff_7_2 cell4QQ_coeff_7_3 cell4QQ_coeff_7_4 cell4QQ_coeff_7_5 cell4QQ_coeff_7_6 cell4QQ_row7 cell4_stage_row_commands 0 8 cell4QQ_coeff_8_0 cell4QQ_coeff_8_1 cell4QQ_coeff_8_2 cell4QQ_coeff_8_3 cell4QQ_coeff_8_4 cell4QQ_coeff_8_5 cell4QQ_coeff_8_6 cell4QQ_row8 cell4_stage_row_commands 0 9 cell4QQ_coeff_9_0 cell4QQ_coeff_9_1 cell4QQ_coeff_9_2 cell4QQ_coeff_9_3 cell4QQ_coeff_9_4 cell4QQ_coeff_9_5 cell4QQ_coeff_9_6 cell4QQ_row9 cell4_stage_row_commands 0 10 cell4QQ_coeff_10_0 cell4QQ_coeff_10_1 cell4QQ_coeff_10_2 cell4QQ_coeff_10_3 cell4QQ_coeff_10_4 cell4QQ_coeff_10_5 cell4QQ_coeff_10_6 cell4QQ_row10
cell4_stage_row_commands 1 0 cell4TwoPdQ_coeff_0_0 cell4TwoPdQ_coeff_0_1 cell4TwoPdQ_coeff_0_2 cell4TwoPdQ_coeff_0_3 cell4TwoPdQ_coeff_0_4 cell4TwoPdQ_coeff_0_5 cell4TwoPdQ_coeff_0_6 cell4TwoPdQ_row0 cell4_stage_row_commands 1 1 cell4TwoPdQ_coeff_1_0 cell4TwoPdQ_coeff_1_1 cell4TwoPdQ_coeff_1_2 cell4TwoPdQ_coeff_1_3 cell4TwoPdQ_coeff_1_4 cell4TwoPdQ_coeff_1_5 cell4TwoPdQ_coeff_1_6 cell4TwoPdQ_row1 cell4_stage_row_commands 1 2 cell4TwoPdQ_coeff_2_0 cell4TwoPdQ_coeff_2_1 cell4TwoPdQ_coeff_2_2 cell4TwoPdQ_coeff_2_3 cell4TwoPdQ_coeff_2_4 cell4TwoPdQ_coeff_2_5 cell4TwoPdQ_coeff_2_6 cell4TwoPdQ_row2 cell4_stage_row_commands 1 3 cell4TwoPdQ_coeff_3_0 cell4TwoPdQ_coeff_3_1 cell4TwoPdQ_coeff_3_2 cell4TwoPdQ_coeff_3_3 cell4TwoPdQ_coeff_3_4 cell4TwoPdQ_coeff_3_5 cell4TwoPdQ_coeff_3_6 cell4TwoPdQ_row3 cell4_stage_row_commands 1 4 cell4TwoPdQ_coeff_4_0 cell4TwoPdQ_coeff_4_1 cell4TwoPdQ_coeff_4_2 cell4TwoPdQ_coeff_4_3 cell4TwoPdQ_coeff_4_4 cell4TwoPdQ_coeff_4_5 cell4TwoPdQ_coeff_4_6 cell4TwoPdQ_row4 cell4_stage_row_commands 1 5 cell4TwoPdQ_coeff_5_0 cell4TwoPdQ_coeff_5_1 cell4TwoPdQ_coeff_5_2 cell4TwoPdQ_coeff_5_3 cell4TwoPdQ_coeff_5_4 cell4TwoPdQ_coeff_5_5 cell4TwoPdQ_coeff_5_6 cell4TwoPdQ_row5 cell4_stage_row_commands 1 6 cell4TwoPdQ_coeff_6_0 cell4TwoPdQ_coeff_6_1 cell4TwoPdQ_coeff_6_2 cell4TwoPdQ_coeff_6_3 cell4TwoPdQ_coeff_6_4 cell4TwoPdQ_coeff_6_5 cell4TwoPdQ_coeff_6_6 cell4TwoPdQ_row6 cell4_stage_row_commands 1 7 cell4TwoPdQ_coeff_7_0 cell4TwoPdQ_coeff_7_1 cell4TwoPdQ_coeff_7_2 cell4TwoPdQ_coeff_7_3 cell4TwoPdQ_coeff_7_4 cell4TwoPdQ_coeff_7_5 cell4TwoPdQ_coeff_7_6 cell4TwoPdQ_row7 cell4_stage_row_commands 1 8 cell4TwoPdQ_coeff_8_0 cell4TwoPdQ_coeff_8_1 cell4TwoPdQ_coeff_8_2 cell4TwoPdQ_coeff_8_3 cell4TwoPdQ_coeff_8_4 cell4TwoPdQ_coeff_8_5 cell4TwoPdQ_coeff_8_6 cell4TwoPdQ_row8
cell4_stage_row_commands 2 0 cell4QdQd_coeff_0_0 cell4QdQd_coeff_0_1 cell4QdQd_coeff_0_2 cell4QdQd_coeff_0_3 cell4QdQd_coeff_0_4 cell4QdQd_coeff_0_5 cell4QdQd_coeff_0_6 cell4QdQd_row0 cell4_stage_row_commands 2 1 cell4QdQd_coeff_1_0 cell4QdQd_coeff_1_1 cell4QdQd_coeff_1_2 cell4QdQd_coeff_1_3 cell4QdQd_coeff_1_4 cell4QdQd_coeff_1_5 cell4QdQd_coeff_1_6 cell4QdQd_row1 cell4_stage_row_commands 2 2 cell4QdQd_coeff_2_0 cell4QdQd_coeff_2_1 cell4QdQd_coeff_2_2 cell4QdQd_coeff_2_3 cell4QdQd_coeff_2_4 cell4QdQd_coeff_2_5 cell4QdQd_coeff_2_6 cell4QdQd_row2 cell4_stage_row_commands 2 3 cell4QdQd_coeff_3_0 cell4QdQd_coeff_3_1 cell4QdQd_coeff_3_2 cell4QdQd_coeff_3_3 cell4QdQd_coeff_3_4 cell4QdQd_coeff_3_5 cell4QdQd_coeff_3_6 cell4QdQd_row3 cell4_stage_row_commands 2 4 cell4QdQd_coeff_4_0 cell4QdQd_coeff_4_1 cell4QdQd_coeff_4_2 cell4QdQd_coeff_4_3 cell4QdQd_coeff_4_4 cell4QdQd_coeff_4_5 cell4QdQd_coeff_4_6 cell4QdQd_row4 cell4_stage_row_commands 2 5 cell4QdQd_coeff_5_0 cell4QdQd_coeff_5_1 cell4QdQd_coeff_5_2 cell4QdQd_coeff_5_3 cell4QdQd_coeff_5_4 cell4QdQd_coeff_5_5 cell4QdQd_coeff_5_6 cell4QdQd_row5 cell4_stage_row_commands 2 6 cell4QdQd_coeff_6_0 cell4QdQd_coeff_6_1 cell4QdQd_coeff_6_2 cell4QdQd_coeff_6_3 cell4QdQd_coeff_6_4 cell4QdQd_coeff_6_5 cell4QdQd_coeff_6_6 cell4QdQd_row6 cell4_stage_row_commands 2 7 cell4QdQd_coeff_7_0 cell4QdQd_coeff_7_1 cell4QdQd_coeff_7_2 cell4QdQd_coeff_7_3 cell4QdQd_coeff_7_4 cell4QdQd_coeff_7_5 cell4QdQd_coeff_7_6 cell4QdQd_row7 cell4_stage_row_commands 2 8 cell4QdQd_coeff_8_0 cell4QdQd_coeff_8_1 cell4QdQd_coeff_8_2 cell4QdQd_coeff_8_3 cell4QdQd_coeff_8_4 cell4QdQd_coeff_8_5 cell4QdQd_coeff_8_6 cell4QdQd_row8
cell4_stage_row_commands 3 0 cell4PQ_coeff_0_0 cell4PQ_coeff_0_1 cell4PQ_coeff_0_2 cell4PQ_coeff_0_3 cell4PQ_coeff_0_4 cell4PQ_coeff_0_5 cell4PQ_coeff_0_6 cell4PQ_row0 cell4_stage_row_commands 3 1 cell4PQ_coeff_1_0 cell4PQ_coeff_1_1 cell4PQ_coeff_1_2 cell4PQ_coeff_1_3 cell4PQ_coeff_1_4 cell4PQ_coeff_1_5 cell4PQ_coeff_1_6 cell4PQ_row1 cell4_stage_row_commands 3 2 cell4PQ_coeff_2_0 cell4PQ_coeff_2_1 cell4PQ_coeff_2_2 cell4PQ_coeff_2_3 cell4PQ_coeff_2_4 cell4PQ_coeff_2_5 cell4PQ_coeff_2_6 cell4PQ_row2 cell4_stage_row_commands 3 3 cell4PQ_coeff_3_0 cell4PQ_coeff_3_1 cell4PQ_coeff_3_2 cell4PQ_coeff_3_3 cell4PQ_coeff_3_4 cell4PQ_coeff_3_5 cell4PQ_coeff_3_6 cell4PQ_row3 cell4_stage_row_commands 3 4 cell4PQ_coeff_4_0 cell4PQ_coeff_4_1 cell4PQ_coeff_4_2 cell4PQ_coeff_4_3 cell4PQ_coeff_4_4 cell4PQ_coeff_4_5 cell4PQ_coeff_4_6 cell4PQ_row4 cell4_stage_row_commands 3 5 cell4PQ_coeff_5_0 cell4PQ_coeff_5_1 cell4PQ_coeff_5_2 cell4PQ_coeff_5_3 cell4PQ_coeff_5_4 cell4PQ_coeff_5_5 cell4PQ_coeff_5_6 cell4PQ_row5 cell4_stage_row_commands 3 6 cell4PQ_coeff_6_0 cell4PQ_coeff_6_1 cell4PQ_coeff_6_2 cell4PQ_coeff_6_3 cell4PQ_coeff_6_4 cell4PQ_coeff_6_5 cell4PQ_coeff_6_6 cell4PQ_row6 cell4_stage_row_commands 3 7 cell4PQ_coeff_7_0 cell4PQ_coeff_7_1 cell4PQ_coeff_7_2 cell4PQ_coeff_7_3 cell4PQ_coeff_7_4 cell4PQ_coeff_7_5 cell4PQ_coeff_7_6 cell4PQ_row7 cell4_stage_row_commands 3 8 cell4PQ_coeff_8_0 cell4PQ_coeff_8_1 cell4PQ_coeff_8_2 cell4PQ_coeff_8_3 cell4PQ_coeff_8_4 cell4PQ_coeff_8_5 cell4PQ_coeff_8_6 cell4PQ_row8 cell4_stage_row_commands 3 9 cell4PQ_coeff_9_0 cell4PQ_coeff_9_1 cell4PQ_coeff_9_2 cell4PQ_coeff_9_3 cell4PQ_coeff_9_4 cell4PQ_coeff_9_5 cell4PQ_coeff_9_6 cell4PQ_row9
local macro "cell4_stage_zero_command" n:ident s:num k:num : command =>
  `(
  @[simp] private theorem $n : cell4StageProductRow $s $k = 0 := by rw [cell4StageProductRow, cell4OuterConv]; simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]; repeat rw [Finset.sum_range_succ]; simp [cell4TwoPdCoeff, cell4PDerivCoeff, cell4QDerivCoeff, cell4PCoeff, cell4QCoeff]
  )
cell4_stage_zero_command cell4QQ_row11_zero 0 11 cell4_stage_zero_command cell4QQ_row12_zero 0 12 cell4_stage_zero_command cell4TwoPdQ_row9_zero 1 9 cell4_stage_zero_command cell4TwoPdQ_row10_zero 1 10 cell4_stage_zero_command cell4TwoPdQ_row11_zero 1 11 cell4_stage_zero_command cell4TwoPdQ_row12_zero 1 12 cell4_stage_zero_command cell4QdQd_row9_zero 2 9 cell4_stage_zero_command cell4QdQd_row10_zero 2 10 cell4_stage_zero_command cell4QdQd_row11_zero 2 11 cell4_stage_zero_command cell4QdQd_row12_zero 2 12 cell4_stage_zero_command cell4PQ_row10_zero 3 10 cell4_stage_zero_command cell4PQ_row11_zero 3 11 cell4_stage_zero_command cell4PQ_row12_zero 3 12
local macro "cell4_signed_coeff" : tactic =>
  `(tactic|
    (all_goals (try rw [cell4SignedCurvature_coeff_formula]); all_goals (try simp only [cell4SignedOuterRow, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_mul])
     all_goals (try simp_rw [cell4OuterConv_coeff]); all_goals (try simp only [cell4ScalarConv])
     all_goals (try simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk])
     all_goals (try (repeat rw [Finset.sum_range_succ]))
     all_goals (try simp_rw [cell4Power_row_coeff])
     all_goals (try simp)
     all_goals (try norm_num [Polynomial.coeff_one, Polynomial.coeff_zero, Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow, cell4PScale, cell4QScale, cell4PNumerator, cell4QNumerator, cell4StageValue, cell4PowerCoeff, cell4PowerScale, cell4PowerNumerator])
     all_goals (try ring_nf)))
local macro "cell4_signed_row_commands" k:num n0:ident n1:ident n2:ident n3:ident n4:ident n5:ident n6:ident n7:ident n8:ident n9:ident row:ident : command =>
  `(
  @[simp] private theorem $n0 : (cell4SignedCurvature.coeff $k).coeff 0 = (X * cell4PowerRow $k).coeff 0 := by cell4_signed_coeff
  @[simp] private theorem $n1 : (cell4SignedCurvature.coeff $k).coeff 1 = (X * cell4PowerRow $k).coeff 1 := by cell4_signed_coeff
  @[simp] private theorem $n2 : (cell4SignedCurvature.coeff $k).coeff 2 = (X * cell4PowerRow $k).coeff 2 := by cell4_signed_coeff
  @[simp] private theorem $n3 : (cell4SignedCurvature.coeff $k).coeff 3 = (X * cell4PowerRow $k).coeff 3 := by cell4_signed_coeff
  @[simp] private theorem $n4 : (cell4SignedCurvature.coeff $k).coeff 4 = (X * cell4PowerRow $k).coeff 4 := by cell4_signed_coeff
  @[simp] private theorem $n5 : (cell4SignedCurvature.coeff $k).coeff 5 = (X * cell4PowerRow $k).coeff 5 := by cell4_signed_coeff
  @[simp] private theorem $n6 : (cell4SignedCurvature.coeff $k).coeff 6 = (X * cell4PowerRow $k).coeff 6 := by cell4_signed_coeff
  @[simp] private theorem $n7 : (cell4SignedCurvature.coeff $k).coeff 7 = (X * cell4PowerRow $k).coeff 7 := by cell4_signed_coeff
  @[simp] private theorem $n8 : (cell4SignedCurvature.coeff $k).coeff 8 = (X * cell4PowerRow $k).coeff 8 := by cell4_signed_coeff
  @[simp] private theorem $n9 : (cell4SignedCurvature.coeff $k).coeff 9 = (X * cell4PowerRow $k).coeff 9 := by cell4_signed_coeff
  private theorem $row : cell4SignedCurvature.coeff $k = X * cell4PowerRow $k := by have hr : (X * cell4PowerRow $k).natDegree ≤ 9 := Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_X_le (R := Rat)) (cell4PowerRow_natDegree $k); apply (Polynomial.ext_iff_natDegree_le (cell4SignedCurvature_innerDegree $k) hr).2; intro l hl; interval_cases l <;> simp
  )
cell4_signed_row_commands 0 cell4Signed_coeff_0_0 cell4Signed_coeff_0_1 cell4Signed_coeff_0_2 cell4Signed_coeff_0_3 cell4Signed_coeff_0_4 cell4Signed_coeff_0_5 cell4Signed_coeff_0_6 cell4Signed_coeff_0_7 cell4Signed_coeff_0_8 cell4Signed_coeff_0_9 cell4Signed_power_row0 cell4_signed_row_commands 1 cell4Signed_coeff_1_0 cell4Signed_coeff_1_1 cell4Signed_coeff_1_2 cell4Signed_coeff_1_3 cell4Signed_coeff_1_4 cell4Signed_coeff_1_5 cell4Signed_coeff_1_6 cell4Signed_coeff_1_7 cell4Signed_coeff_1_8 cell4Signed_coeff_1_9 cell4Signed_power_row1 cell4_signed_row_commands 2 cell4Signed_coeff_2_0 cell4Signed_coeff_2_1 cell4Signed_coeff_2_2 cell4Signed_coeff_2_3 cell4Signed_coeff_2_4 cell4Signed_coeff_2_5 cell4Signed_coeff_2_6 cell4Signed_coeff_2_7 cell4Signed_coeff_2_8 cell4Signed_coeff_2_9 cell4Signed_power_row2 cell4_signed_row_commands 3 cell4Signed_coeff_3_0 cell4Signed_coeff_3_1 cell4Signed_coeff_3_2 cell4Signed_coeff_3_3 cell4Signed_coeff_3_4 cell4Signed_coeff_3_5 cell4Signed_coeff_3_6 cell4Signed_coeff_3_7 cell4Signed_coeff_3_8 cell4Signed_coeff_3_9 cell4Signed_power_row3 cell4_signed_row_commands 4 cell4Signed_coeff_4_0 cell4Signed_coeff_4_1 cell4Signed_coeff_4_2 cell4Signed_coeff_4_3 cell4Signed_coeff_4_4 cell4Signed_coeff_4_5 cell4Signed_coeff_4_6 cell4Signed_coeff_4_7 cell4Signed_coeff_4_8 cell4Signed_coeff_4_9 cell4Signed_power_row4 cell4_signed_row_commands 5 cell4Signed_coeff_5_0 cell4Signed_coeff_5_1 cell4Signed_coeff_5_2 cell4Signed_coeff_5_3 cell4Signed_coeff_5_4 cell4Signed_coeff_5_5 cell4Signed_coeff_5_6 cell4Signed_coeff_5_7 cell4Signed_coeff_5_8 cell4Signed_coeff_5_9 cell4Signed_power_row5 cell4_signed_row_commands 6 cell4Signed_coeff_6_0 cell4Signed_coeff_6_1 cell4Signed_coeff_6_2 cell4Signed_coeff_6_3 cell4Signed_coeff_6_4 cell4Signed_coeff_6_5 cell4Signed_coeff_6_6 cell4Signed_coeff_6_7 cell4Signed_coeff_6_8 cell4Signed_coeff_6_9 cell4Signed_power_row6 cell4_signed_row_commands 7 cell4Signed_coeff_7_0 cell4Signed_coeff_7_1 cell4Signed_coeff_7_2 cell4Signed_coeff_7_3 cell4Signed_coeff_7_4 cell4Signed_coeff_7_5 cell4Signed_coeff_7_6 cell4Signed_coeff_7_7 cell4Signed_coeff_7_8 cell4Signed_coeff_7_9 cell4Signed_power_row7 cell4_signed_row_commands 8 cell4Signed_coeff_8_0 cell4Signed_coeff_8_1 cell4Signed_coeff_8_2 cell4Signed_coeff_8_3 cell4Signed_coeff_8_4 cell4Signed_coeff_8_5 cell4Signed_coeff_8_6 cell4Signed_coeff_8_7 cell4Signed_coeff_8_8 cell4Signed_coeff_8_9 cell4Signed_power_row8 cell4_signed_row_commands 9 cell4Signed_coeff_9_0 cell4Signed_coeff_9_1 cell4Signed_coeff_9_2 cell4Signed_coeff_9_3 cell4Signed_coeff_9_4 cell4Signed_coeff_9_5 cell4Signed_coeff_9_6 cell4Signed_coeff_9_7 cell4Signed_coeff_9_8 cell4Signed_coeff_9_9 cell4Signed_power_row9 cell4_signed_row_commands 10 cell4Signed_coeff_10_0 cell4Signed_coeff_10_1 cell4Signed_coeff_10_2 cell4Signed_coeff_10_3 cell4Signed_coeff_10_4 cell4Signed_coeff_10_5 cell4Signed_coeff_10_6 cell4Signed_coeff_10_7 cell4Signed_coeff_10_8 cell4Signed_coeff_10_9 cell4Signed_power_row10 cell4_signed_row_commands 11 cell4Signed_coeff_11_0 cell4Signed_coeff_11_1 cell4Signed_coeff_11_2 cell4Signed_coeff_11_3 cell4Signed_coeff_11_4 cell4Signed_coeff_11_5 cell4Signed_coeff_11_6 cell4Signed_coeff_11_7 cell4Signed_coeff_11_8 cell4Signed_coeff_11_9 cell4Signed_power_row11 cell4_signed_row_commands 12 cell4Signed_coeff_12_0 cell4Signed_coeff_12_1 cell4Signed_coeff_12_2 cell4Signed_coeff_12_3 cell4Signed_coeff_12_4 cell4Signed_coeff_12_5 cell4Signed_coeff_12_6 cell4Signed_coeff_12_7 cell4Signed_coeff_12_8 cell4Signed_coeff_12_9 cell4Signed_power_row12
private theorem cell4Signed_eq_y_mul_power :
    cell4SignedCurvature = C X * cell4Power := by
  ext k
  by_cases hk : k < 13
  · rw [Polynomial.coeff_C_mul, cell4Power_outer_coeff k hk]
    interval_cases k <;>
      simp only [cell4Signed_power_row0, cell4Signed_power_row1,
        cell4Signed_power_row2, cell4Signed_power_row3,
        cell4Signed_power_row4, cell4Signed_power_row5,
        cell4Signed_power_row6, cell4Signed_power_row7,
        cell4Signed_power_row8, cell4Signed_power_row9,
        cell4Signed_power_row10, cell4Signed_power_row11,
        cell4Signed_power_row12]
  · have hk' : 13 ≤ k := Nat.le_of_not_gt hk
    have hs : cell4SignedCurvature.coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (cell4SignedCurvature_natDegree.trans_lt (Nat.lt_of_succ_le hk'))
    have hp : (C X * cell4Power).coeff k = 0 := by
      rw [Polynomial.coeff_C_mul, cell4Power, Polynomial.finsetSum_coeff]
      simp [hk]
    rw [hs, hp]
private noncomputable def cell4Specialize (p : BivariateRat) (y : Real) : Polynomial Real := p.map (Polynomial.eval₂RingHom (algebraMap Rat Real) y)
private theorem cell4SignedCurvature_nonneg {x y : Real} (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) : 0 ≤ (cell4Specialize cell4SignedCurvature y).eval x := by
  have h := tensorBernsteinPolynomial_eval₂_nonneg (n := 8) (m := 12) (coefficient := cell4BernsteinCoefficient) cell4BernsteinCoefficient_nonneg hy.1 hy.2 hx.1 hx.2
  change 0 ≤ Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap Rat Real) y) x cell4Tensor at h
  rw [cell4Tensor_eq_power] at h
  have h' : 0 ≤ y * Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap Rat Real) y) x cell4Power := mul_nonneg hy.1 h
  simpa [cell4Specialize, Polynomial.eval₂_eq_eval_map, cell4Signed_eq_y_mul_power, Polynomial.coe_eval₂RingHom] using h'
private def cell4U (x : Real) : Real := 1 / 4 + (180001 / 500000 - 1 / 4) * x
private def cell4Span (x : Real) : Real := 2 * (575002 / 1000000 - cell4U x) - 424998 / 1000000
private def cell4N (x y : Real) : Real := 424998 / 1000000 + cell4Span x * y
private def cell4Ph (x y : Real) : Real := (-2 / 3) * (424998 / 1000000 : Real) ^ 3 - 6 * cell4N x y * (424998 / 1000000 : Real) ^ 2 + 6 * cell4N x y ^ 2 * (424998 / 1000000 : Real) + (2 / 3) * cell4N x y ^ 3
private def cell4P (x y : Real) : Real := (180001 / 500000 - 1 / 4) * cell4Span x * cell4Ph x y
private def cell4Q (x y : Real) : Real := 4 * (424998 / 1000000 : Real) * cell4U x * (1 - cell4U x) * cell4N x y * (cell4N x y + 424998 / 1000000) ^ 2
private theorem cell4Polynomial_evaluation (x y : Real) :
    (cell4Specialize cell4RationalPolynomials.1 y).eval x = cell4P x y ∧
      (cell4Specialize cell4RationalPolynomials.2 y).eval x = cell4Q x y := by
  constructor
  · rw [cell4Specialize, cell4RationalPolynomials, cell4PFull, Polynomial.eval_map]; unfold cell4PRow
    simp_rw [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X_pow]
    repeat rw [Finset.sum_range_succ]
    norm_num [cell4PScale, cell4PNumerator, cell4P, cell4Ph, cell4N, cell4Span, cell4U]
    ring_nf
  · rw [cell4Specialize, cell4RationalPolynomials, cell4QFull, Polynomial.eval_map]; unfold cell4QRow
    simp_rw [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X_pow]
    repeat rw [Finset.sum_range_succ]
    norm_num [cell4QScale, cell4QNumerator, cell4Q, cell4N, cell4Span, cell4U]
    ring_nf
private theorem cell4Factors_pos {x y : Real} (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) : 0 < cell4U x ∧ 0 < 1 - cell4U x ∧ 0 < cell4Span x ∧ 0 < cell4N x y ∧ 0 < cell4N x y + 424998 / 1000000 ∧ 0 < cell4Q x y := by
  rcases hx with ⟨hx0, hx1⟩; rcases hy with ⟨hy0, hy1⟩
  have hu : 0 < cell4U x := by norm_num [cell4U]; linarith
  have hu1 : 0 < 1 - cell4U x := by norm_num [cell4U]; linarith
  have hs : 0 < cell4Span x := by norm_num [cell4Span, cell4U]; linarith
  have hn : 0 < cell4N x y := by unfold cell4N; positivity
  have hnb : 0 < cell4N x y + 424998 / 1000000 := by positivity
  have hq : 0 < cell4Q x y := by unfold cell4Q; positivity
  exact ⟨hu, hu1, hs, hn, hnb, hq⟩
private noncomputable def cell4TightLog (r : Real) : Real := let z := (r - 1) / (r + 1); 2 * (z + z ^ 3 / (3 * (1 - z ^ 2)))
private def cell4RLower (_u : Real) : Real := 1
private def cell4RUpper (u : Real) : Real := 2 * (1 - u) / (424998 / 1000000 : Real) - 2
private def cell4ChartR (x y : Real) : Real := cell4RLower (cell4U x) + (cell4RUpper (cell4U x) - cell4RLower (cell4U x)) * y
private theorem cell4TightLog_eq_ratio {r : Real} (hr : 1 ≤ r) : cell4TightLog r = ((r - 1) * (r ^ 2 + 10 * r + 1)) / (6 * r * (r + 1)) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr; have hr1 : 0 < r + 1 := by linarith
  have hz : 1 - ((r - 1) / (r + 1)) ^ 2 = 4 * r / (r + 1) ^ 2 := by field_simp [hr1.ne']; ring
  dsimp [cell4TightLog]; rw [hz]
  field_simp [hr0.ne', hr1.ne']; ring
private theorem cell4ChartR_eq_ratio {x y : Real} (hx : x ∈ Icc (0 : Real) 1) : cell4ChartR x y = cell4N x y / (424998 / 1000000 : Real) := by
  have hu : 0 < cell4U x := by norm_num [cell4U] at hx ⊢; linarith
  dsimp [cell4ChartR, cell4RLower, cell4RUpper]
  unfold cell4N cell4Span cell4U
  field_simp [hu.ne']; ring
private theorem cell4ChartR_ge_one {x y : Real} (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) : 1 ≤ cell4ChartR x y := by
  rw [cell4ChartR_eq_ratio hx]
  have hs := (cell4Factors_pos hx hy).2.2.1
  have hnbase : (424998 / 1000000 : Real) ≤ cell4N x y := by unfold cell4N; exact le_add_of_nonneg_right (mul_nonneg hs.le hy.1)
  have hb : (0 : Real) < 424998 / 1000000 := by norm_num
  rw [le_div_iff₀ hb]
  simpa only [one_mul] using hnbase
private theorem cell4Transformed_expansion {x y : Real} (hx : x ∈ Icc (0 : Real) 1) : sectionSixFirstLowCentralLargeAboveTransformedIntegrand cell4TightLog (4 : Fin 5) x y = (180001 / 500000 - 1 / 4) * (cell4RUpper (cell4U x) - cell4RLower (cell4U x)) * (cell4TightLog (cell4ChartR x y) / (cell4U x * (1 - cell4U x) * (cell4ChartR x y + 1))) := by
  have hu : cell4U x < 1 := by norm_num [cell4U] at hx ⊢; linarith
  have hlow : (1 - cell4U x) / ((1 - cell4U x) / 3) - 2 = cell4RLower (cell4U x) := by dsimp [cell4RLower]; field_simp [ne_of_gt (sub_pos.mpr hu)]; norm_num
  have hupper : (1 - cell4U x) / ((212499 / 500000 : Real) / 2) - 2 = cell4RUpper (cell4U x) := by dsimp [cell4RUpper]; norm_num; ring
  change (180001 / 500000 - 1 / 4) * (((1 - cell4U x) / ((212499 / 500000) / 2) - 2) - ((1 - cell4U x) / ((1 - cell4U x) / 3) - 2)) * (cell4TightLog (((1 - cell4U x) / ((1 - cell4U x) / 3) - 2) + (((1 - cell4U x) / ((212499 / 500000) / 2) - 2) - ((1 - cell4U x) / ((1 - cell4U x) / 3) - 2)) * y) / (cell4U x * (1 - cell4U x) * (((1 - cell4U x) / ((1 - cell4U x) / 3) - 2) + (((1 - cell4U x) / ((212499 / 500000) / 2) - 2) - ((1 - cell4U x) / ((1 - cell4U x) / 3) - 2)) * y + 1))) = _
  rw [cell4ChartR, hlow, hupper]
private theorem cell4Transformed_eq_quotient {x y : Real}
    (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) :
    sectionSixFirstLowCentralLargeAboveTransformedIntegrand
      cell4TightLog (4 : Fin 5) x y = cell4P x y / cell4Q x y := by
  rcases cell4Factors_pos hx hy with ⟨hu, hu1, hs, hn, hnb, hq⟩
  let r := cell4N x y / (424998 / 1000000 : Real)
  have hr : 0 < r := div_pos hn (by norm_num)
  have hrc : cell4ChartR x y = r := cell4ChartR_eq_ratio hx
  have hrOne : 1 ≤ r := by rw [← hrc]; exact cell4ChartR_ge_one hx hy
  have hspan : cell4RUpper (cell4U x) - cell4RLower (cell4U x) =
      cell4Span x / (424998 / 1000000 : Real) := by
    dsimp [cell4RUpper, cell4RLower, cell4Span]
    ring_nf
  have hone : r + 1 =
      (cell4N x y + 424998 / 1000000) / (424998 / 1000000 : Real) := by
    dsimp [r]; field_simp
  have hlog : cell4TightLog r = cell4Ph x y /
      (4 * (424998 / 1000000 : Real) * cell4N x y *
        (cell4N x y + 424998 / 1000000)) := by
    rw [cell4TightLog_eq_ratio hrOne]
    dsimp [r]; unfold cell4Ph
    field_simp [hn.ne', hnb.ne']; ring
  rw [cell4Transformed_expansion hx, hrc, hspan, hlog, hone]
  field_simp [hu.ne', hu1.ne', hn.ne', hnb.ne', hq.ne']
  unfold cell4P cell4Q
  ring
private noncomputable def cell4SecondNumerator (p q : Polynomial Real) (x : Real) : Real := p.derivative.derivative.eval x * q.eval x ^ 2 - 2 * p.derivative.eval x * q.eval x * q.derivative.eval x + 2 * p.eval x * q.derivative.eval x ^ 2 - p.eval x * q.eval x * q.derivative.derivative.eval x
private theorem cell4SignedCurvature_evaluation (x y : Real) :
    (cell4Specialize cell4SignedCurvature y).eval x = cell4SecondNumerator
      (cell4Specialize cell4RationalPolynomials.1 y)
      (cell4Specialize cell4RationalPolynomials.2 y) x := by
  simp [cell4Specialize, cell4SignedCurvature, cell4Constant,
    cell4SecondNumerator, Polynomial.derivative_map, Polynomial.C_ofNat]
private theorem cell4Quotient_convexOn (p q : Polynomial Real)
    (hq : ∀ x ∈ Icc (0 : Real) 1, 0 < q.eval x)
    (hn : ∀ x ∈ Icc (0 : Real) 1, 0 ≤ cell4SecondNumerator p q x) :
    ConvexOn Real (Icc (0 : Real) 1) (fun x => p.eval x / q.eval x) := by
  let f1 := fun x : Real => (p.derivative.eval x * q.eval x -
    p.eval x * q.derivative.eval x) / q.eval x ^ 2
  let f2 := fun x : Real => cell4SecondNumerator p q x / q.eval x ^ 3
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := f1) (f'' := f2)
    (convex_Icc (0 : Real) 1)
  · intro x hx
    exact ((Polynomial.hasDerivAt p x).continuousAt.div
      (Polynomial.hasDerivAt q x).continuousAt (hq x hx).ne').continuousWithinAt
  · intro x hx
    exact (((Polynomial.hasDerivAt p x).div (Polynomial.hasDerivAt q x)
      (hq x (interior_subset hx)).ne').congr_deriv (by dsimp [f1])).hasDerivWithinAt
  · intro x hx
    have hqx := hq x (interior_subset hx)
    have hp := Polynomial.hasDerivAt p x
    have hpd := Polynomial.hasDerivAt p.derivative x
    have hq0 := Polynomial.hasDerivAt q x
    have hqd := Polynomial.hasDerivAt q.derivative x
    exact (((hpd.mul hq0).sub (hp.mul hqd)).div (hq0.pow 2)
      (pow_ne_zero 2 hqx.ne')).congr_deriv (by
        dsimp [f1, f2, cell4SecondNumerator]
        field_simp [hqx.ne']; ring) |>.hasDerivWithinAt
  · intro x hx
    exact div_nonneg (hn x (interior_subset hx))
      (pow_nonneg (hq x (interior_subset hx)).le 3)
theorem sectionSixFirstLowCentralLargeAbove_tight_convexOn_x_cell4
    (y : Real) (hy : y ∈ Icc (0 : Real) 1) :
    let tightLog : Real -> Real := fun r =>
      let z := (r - 1) / (r + 1)
      2 * (z + z ^ 3 / (3 * (1 - z ^ 2)))
    ConvexOn Real (Icc (0 : Real) 1)
      (fun x => sectionSixFirstLowCentralLargeAboveTransformedIntegrand
        tightLog (4 : Fin 5) x y) := by
  dsimp only
  let p := cell4Specialize cell4RationalPolynomials.1 y; let q := cell4Specialize cell4RationalPolynomials.2 y
  have heval (x : Real) := cell4Polynomial_evaluation x y
  have hq : ∀ x ∈ Icc (0 : Real) 1, 0 < q.eval x := by
    intro x hx; dsimp [q]; rw [(heval x).2]
    exact (cell4Factors_pos hx hy).2.2.2.2.2
  have hs : ∀ x ∈ Icc (0 : Real) 1, 0 ≤ cell4SecondNumerator p q x := by
    intro x hx; dsimp [p, q]; rw [← cell4SignedCurvature_evaluation]
    exact cell4SignedCurvature_nonneg hx hy
  refine (cell4Quotient_convexOn p q hq hs).congr ?_
  intro x hx; dsimp [p, q]; rw [(heval x).1, (heval x).2]
  exact (cell4Transformed_eq_quotient hx hy).symm
end
end PrimesRestrictedDigits
