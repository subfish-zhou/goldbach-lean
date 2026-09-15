import BuchstabSeedTightLower

namespace Wu2008DoubleSieve.GlobalLogRelationPayment
open Real SharpLogRecurrence JointLogTotalComparison TotalEndpointComparison
open GlobalSignedActualComparison (collected packet collection)
noncomputable section

/-- Chosen algebraically to annihilate the original 527/327 coefficient. -/
def shift : ℝ := 49368190687/1528065000

theorem endpoint_relation :
    log (327/200:ℝ)+log (527/327:ℝ)+log (727/527:ℝ)+log (1200/727:ℝ) =
      3*log (3/2:ℝ)+2*log (4/3:ℝ) := by
  calc
    _ = log ((327/200:ℝ)*(527/327)*(727/527)*(1200/727)) := by
      rw [← log_mul (by norm_num : (327/200:ℝ) ≠ 0) (by norm_num : (527/327:ℝ) ≠ 0)]
      rw [← log_mul (by norm_num : (327/200:ℝ)*(527/327) ≠ 0) (by norm_num : (727/527:ℝ) ≠ 0)]
      rw [← log_mul (by norm_num : (327/200:ℝ)*(527/327)*(727/527) ≠ 0) (by norm_num : (1200/727:ℝ) ≠ 0)]
    _ = log ((3/2:ℝ)^3*(4/3)^2) := by congr 1; norm_num
    _ = _ := by
      rw [log_mul (by norm_num : (3/2:ℝ)^3 ≠ 0) (by norm_num : (4/3:ℝ)^2 ≠ 0),log_pow,log_pow]
      norm_num

def zeroRelation (f : ℝ → ℝ) : ℝ :=
  f (327/200)+f (527/327)+f (727/527)+f (1200/727)-3*f (3/2)-2*f (4/3)

theorem zero_relation_log : zeroRelation log = 0 := by
  unfold zeroRelation
  linarith only [endpoint_relation]

/-- Whole signed packet after one exact zero relation, with the same arguments. -/
def repaid (L H : ℝ → ℝ) : ℝ :=
  (-266739877032261626921/1785355070677447500)*L (4/3)+
  (358245804565677612772391597/14901576789423697560495000)*H (3/2)+
  (943083088/114604875)*H (5/4)+
  (15549918691125832337/2550817852506000000)*H (727/527)+
  (12963658609426086898463268417154149083835937/982672734630224359211166378158240922977124)*H (1327/824)+
  (12963658609426086898463268417154149083835937/982672734630224359211166378158240922977124)*H (116081/103506)+
  (45711723750549248/1247524545012993)*H (6466668/6152293)+
  (-23526084706383522589366104523783786496/3729428911866529810567814389353)*L (4315543337/4281905212)+
  (47281093382566382680686050047210345/20476837392276624656401340676)*H (3728148112/3694509987)+
  (16/1)*H (26/25)+
  (20466702299/7640325000)*H (327/200)+
  (0/1)*H (527/327)+
  (37143670687/1528065000)*H (1200/727)+
  (907616/3472875)*H (1127/1000)+
  (-128/3)*L (2654/2181)+
  (-128/3)*L (5781/5308)+
  (-448/81)*L (1227/800)+
  (-18056918400/2336752783)*L (74881/66350)+
  (-18056918400/2336752783)*L (240187/198481)+
  (6140336124508242059/827319551135595000)*(H (1327/824))^2

theorem repaid_identity (f : ℝ → ℝ) :
    repaid f f = collected f f+shift*zeroRelation f := by
  unfold repaid collected shift zeroRelation
  ring

theorem repaid_log_identity : repaid log log = collected log log := by
  rw [repaid_identity,zero_relation_log,mul_zero,add_zero]

theorem repaid_payment : collected log log ≤ repaid lowerLog V := by
  rw [← repaid_log_identity]
  have h0 := log_lower (by norm_num : (1:ℝ) ≤ 4/3)
  have h1 := log_le_V (by norm_num : (1:ℝ) ≤ 3/2)
  have h2 := log_le_V (by norm_num : (1:ℝ) ≤ 5/4)
  have h3 := log_le_V (by norm_num : (1:ℝ) ≤ 727/527)
  have h4 := log_le_V (by norm_num : (1:ℝ) ≤ 1327/824)
  have h5 := log_le_V (by norm_num : (1:ℝ) ≤ 116081/103506)
  have h6 := log_le_V (by norm_num : (1:ℝ) ≤ 6466668/6152293)
  have h7 := log_lower (by norm_num : (1:ℝ) ≤ 4315543337/4281905212)
  have h8 := log_le_V (by norm_num : (1:ℝ) ≤ 3728148112/3694509987)
  have h9 := log_le_V (by norm_num : (1:ℝ) ≤ 26/25)
  have h10 := log_le_V (by norm_num : (1:ℝ) ≤ 327/200)
  have h11 := log_le_V (by norm_num : (1:ℝ) ≤ 527/327)
  have h12 := log_le_V (by norm_num : (1:ℝ) ≤ 1200/727)
  have h13 := log_le_V (by norm_num : (1:ℝ) ≤ 1127/1000)
  have h14 := log_lower (by norm_num : (1:ℝ) ≤ 2654/2181)
  have h15 := log_lower (by norm_num : (1:ℝ) ≤ 5781/5308)
  have h16 := log_lower (by norm_num : (1:ℝ) ≤ 1227/800)
  have h17 := log_lower (by norm_num : (1:ℝ) ≤ 74881/66350)
  have h18 := log_lower (by norm_num : (1:ℝ) ≤ 240187/198481)
  have hn : 0 ≤ log (1327/824:ℝ) := log_nonneg (by norm_num)
  have hs := pow_le_pow_left₀ hn h4 2
  unfold repaid
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,hs]

/-- The exact decrease is computed only after global cancellation. -/
def logGain : ℝ := (collected lowerLog V-repaid lowerLog V)/4

theorem log_gain_exact : logGain = 3777726778043961512278901500299358093344156358051393/686294661937115164357624646195177702102585784720000000 := by
  norm_num [logGain,collected,repaid,V,upperLog,lowerLog]

/-- Already consumes the genuine new Four lower bound; sixth remains the old payment. -/
def upperRational : ℝ := BuchstabSeedTightLower.upperRational-logGain

theorem actual_upper : JointHMotherPayment.unroundedCoefficient < upperRational := by
  have hr := fixedCertificate_exact
  unfold fixedCertificate classicalPayment at hr
  have hp := PsiG18Strength.psi_loss_upper
  have hg := PsiG18Strength.g18_bounds.2
  have hc := repaid_payment
  have hu := BuchstabSeedTightLower.actual_upper_real
  unfold BuchstabSeedTightLower.upperReal at hu
  rw [collection] at hu
  unfold upperRational BuchstabSeedTightLower.upperRational logGain
    retainedExtra Phase20.psiPaymentLoss at *
  linarith only [hr,hp,hg,hc,hu]

def totalGain : ℝ := logGain+BuchstabSeedTightLower.motherGain

theorem total_gain_exact : totalGain = 5303392813545236386320384564166771194294496087339276707422147357579943843633631744702783/579811931999029904023287071636134646793907458359842471856661141188675078099916550320000000 := by
  rw [totalGain,log_gain_exact,BuchstabSeedTightLower.mother_gain_exact]
  norm_num

theorem upper_substitution : upperRational = GlobalSignedActualComparison.upperRational-totalGain := by
  rw [upperRational,BuchstabSeedTightLower.upper_substitution,totalGain]
  ring

def upperRemainder : ℝ := upperRational-8*lowerLog (5000/4469)

theorem remainder_substitution : upperRemainder = GlobalSignedActualComparison.upperRemainder-totalGain := by
  rw [upperRemainder,upper_substitution,GlobalSignedActualComparison.upperRemainder]
  ring

theorem upper_rational_exact : upperRational = 48491631322352448641820884106859528728000980403059280095437805189490998156890815990674992633915741987425334390899678793596049310266503903975247829596601878143329586587698394886041884721271097246406015138532793607912957075644585010345325480398767229356260463551594363995794647710068410634150080760720653289940614083573366894029659/53406289064011724885243242720978419351649048080645446032886871965312657523628116539020127970221119170304389629022106247473196912873926232640580410358496152690486741362511019019043206914316387131134820444950649848151425751215737561734258364464328612971510154528920997308613043979802418064480560860787890100235015611753728000000000 := by
  rw [upperRational,BuchstabSeedTightLower.upper_rational_exact,log_gain_exact]
  norm_num

theorem upper_remainder_exact : upperRemainder = 90370024909799752521905205291950982836319938709420457106043292803219286719618304874292157299365713869819768998936551970972944162178672643458651361404607696620645464902411437481415412821662897326306336170912020093596150166325336115873903425008556576190471240829739831571216963455896613447413959088291476545426366231415386673486875025687/9229071011132059514094459761694044329364379393510498125345215361184021683014791437159751815226654524817545983954065048732977711045378066041032639475455381591971447308684568394778998697391577848613427927881600249759696350154134769074304001287398272730109516040370868245157937772901174263962475446259710238449252040701757173557504000000000 := by
  rw [remainder_substitution,GlobalSignedActualComparison.upperRemainder_exact,total_gain_exact]
  norm_num

theorem log_gain_size : (5504/1000000:ℝ) < logGain ∧ logGain < 5505/1000000 := by
  rw [log_gain_exact]; norm_num

theorem total_gain_size : (9146/1000000:ℝ) < totalGain ∧ totalGain < 9147/1000000 := by
  rw [total_gain_exact]; norm_num

theorem upper_rational_size : (907976/1000000:ℝ) < upperRational ∧ upperRational < 907977/1000000 := by
  rw [upper_rational_exact]; norm_num

theorem upper_remainder_size : (9791/1000000:ℝ) < upperRemainder ∧ upperRemainder < 9792/1000000 := by
  rw [upper_remainder_exact]; norm_num

theorem gain_vs_global_remainder : 0 < logGain ∧ 0 < totalGain ∧
    totalGain < GlobalSignedActualComparison.upperRemainder := by
  rw [log_gain_exact,total_gain_exact,GlobalSignedActualComparison.upperRemainder_exact]
  norm_num

/-- The lower endpoint is retained, not falsely raised by an upper-certificate gain. -/
theorem actual_Q_enclosure : GlobalSignedActualComparison.lowerRational <
    JointHMotherPayment.unroundedCoefficient ∧ JointHMotherPayment.unroundedCoefficient < upperRational :=
  ⟨GlobalSignedActualComparison.actual_lower,actual_upper⟩

theorem actual_Q_rational_bounds : (822040/1000000:ℝ) < JointHMotherPayment.unroundedCoefficient ∧
    JointHMotherPayment.unroundedCoefficient < 907977/1000000 :=
  ⟨GlobalSignedActualComparison.actual_Q_rational_bounds.1,actual_upper.trans upper_rational_size.2⟩

theorem actual_target_enclosure : -upperRemainder <
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient ∧
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient <
      GlobalSignedActualComparison.lowerRemainder := by
  have htL := log_lower (by norm_num : (1:ℝ) ≤ 5000/4469)
  constructor
  · unfold upperRemainder AnalyticTotalThreshold.target
    linarith only [actual_upper,htL]
  · exact GlobalSignedActualComparison.actual_target_enclosure.2

theorem actual_target_rational_bounds : (-9792/1000000:ℝ) <
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient ∧
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient < 76146/1000000 := by
  constructor
  · linarith only [actual_target_enclosure.1,upper_remainder_size.2]
  · exact GlobalSignedActualComparison.actual_target_rational_bounds.2

theorem rational_endpoints_straddle :
    GlobalSignedActualComparison.lowerRational < 8*lowerLog (5000/4469) ∧
    8*V (5000/4469) < upperRational := by
  refine ⟨GlobalSignedActualComparison.rational_endpoints_straddle.1,?_⟩
  rw [upper_rational_exact]
  norm_num [V,upperLog,lowerLog]

/-- Dual algebraic choice: annihilate the lower packet's positive 3/2 coefficient. -/
def lowerShift : ℝ := 2126444395638171118684/71849303201065344003

def lowerRepaid (L H : ℝ → ℝ) : ℝ :=
  (-10501274323067239070672/71849303201065344003)*H (4/3)+
  (0/1)*L (3/2)+
  (19588418/9646875)*L (5/4)+
  (-6702229973379020402681/1796232580026633600075)*H (727/527)+
  (365398004238584479892646492386144279429431651602901425776353420683374723/28866867222069965312816790192096006285293922566262394302161692882477740)*L (1327/824)+
  (12963658609426086898463268417154149083835937/982672734630224359211166378158240922977124)*L (116081/103506)+
  (45711723750549248/1247524545012993)*L (6466668/6152293)+
  (-23526084706383522589366104523783786496/3729428911866529810567814389353)*H (4315543337/4281905212)+
  (47281093382566382680686050047210345/20476837392276624656401340676)*L (3728148112/3694509987)+
  (-7352789676990745678012151/28066134062916150001171875)*H (327/200)+
  (-50065481472721826381777239/359246516005326720015000000)*H (527/327)+
  (1551649970029648366660/71849303201065344003)*L (1200/727)+
  (18196664416486466956587538550816/2203190304725340227508009122625)*(L (1327/824))^2

theorem lower_repaid_identity (f : ℝ → ℝ) : lowerRepaid f f =
    GlobalSignedActualComparison.lowerCollected f f+lowerShift*zeroRelation f := by
  unfold lowerRepaid GlobalSignedActualComparison.lowerCollected lowerShift zeroRelation
  ring

theorem lower_repaid_payment : lowerRepaid lowerLog V ≤
    GlobalSignedActualComparison.lowerCollected log log := by
  have he := lower_repaid_identity log
  rw [zero_relation_log,mul_zero,add_zero] at he
  rw [← he]
  have h0 := log_le_V (by norm_num : (1:ℝ) ≤ 4/3)
  have h1 := log_lower (by norm_num : (1:ℝ) ≤ 3/2)
  have h2 := log_lower (by norm_num : (1:ℝ) ≤ 5/4)
  have h3 := log_le_V (by norm_num : (1:ℝ) ≤ 727/527)
  have h4 := log_lower (by norm_num : (1:ℝ) ≤ 1327/824)
  have h5 := log_lower (by norm_num : (1:ℝ) ≤ 116081/103506)
  have h6 := log_lower (by norm_num : (1:ℝ) ≤ 6466668/6152293)
  have h7 := log_le_V (by norm_num : (1:ℝ) ≤ 4315543337/4281905212)
  have h8 := log_lower (by norm_num : (1:ℝ) ≤ 3728148112/3694509987)
  have h9 := log_le_V (by norm_num : (1:ℝ) ≤ 327/200)
  have h10 := log_le_V (by norm_num : (1:ℝ) ≤ 527/327)
  have h11 := log_lower (by norm_num : (1:ℝ) ≤ 1200/727)
  have hn : 0 ≤ lowerLog (1327/824:ℝ) := by norm_num [lowerLog]
  have hp := pow_le_pow_left₀ hn h4 2
  unfold lowerRepaid
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,hp]

def lowerGain : ℝ := (lowerRepaid lowerLog V-GlobalSignedActualComparison.lowerCollected lowerLog V)/4

theorem lower_gain_exact : lowerGain = 186556525724005699719144478613584106929592500064340581027/185264642209987944001603301500943194458016396472067413559000 := by
  norm_num [lowerGain,lowerRepaid,GlobalSignedActualComparison.lowerCollected,V,upperLog,lowerLog]

def lowerRational : ℝ := GlobalSignedActualComparison.lowerRational+lowerGain

theorem actual_lower : lowerRational < JointHMotherPayment.unroundedCoefficient := by
  have hr := fixedCertificate_exact
  unfold fixedCertificate classicalPayment at hr
  have hp := PsiG18Strength.two_recoveries_bounds.1
  have hc := lower_repaid_payment
  have hl := GlobalSignedActualComparison.lower_real_actual
  unfold GlobalSignedActualComparison.lowerReal at hl
  rw [GlobalSignedActualComparison.lower_collection] at hl
  unfold lowerRational GlobalSignedActualComparison.lowerRational lowerGain
    retainedExtra Phase20.psiPaymentLoss at *
  linarith only [hr,hp,hc,hl]

def lowerRemainder : ℝ := 8*V (5000/4469)-lowerRational

theorem lower_remainder_exact : lowerRemainder = 1267651610468727349805660078381667099770150638481379943968447132656674038462154365852888943014576963115293844225322947843682269939931428894211732579871540961356350032574773987775825474364613430210644177001599544725208624021445486530118555378436218561929660326781205434235169755654797045731930278432677116221902257711361839/16870954101988482270366978594812511921640929369873160877877471127519782591601261693724856750794161405222702555755605532454964102531519043046904958634533074979222444453320637367271791214337589962543271988343315255295573179511547035177034652457030069593703679795657186181735828775003366808637795850143916787124019050000000000 := by
  have h := GlobalSignedActualComparison.lowerRemainder_exact
  unfold GlobalSignedActualComparison.lowerRemainder at h
  unfold lowerRemainder lowerRational
  rw [lower_gain_exact]
  linarith only [h]

theorem lower_rational_exact : lowerRational = 737178457312247006277429827665464471465888421289512572798282220422701614801370249493948327585622323951658294097949908325221380943488184742197006527172583013492332443751251703792509982980711643275786880813453922177924605177658539990433396058093428782319699067322240690024713802345495238296580404538964049363745153/895669035764809547550475771940356081828715470730449974489253817502617843909132770864474501954744452542493512098657413083256001178109642614385355705155468435807805833354820646480042019981847945457790559688761438442303552631785007406689153310650779152139515321086497082353779440722341312198323319500760650000000000 := by
  have h := lower_remainder_exact
  unfold lowerRemainder at h
  norm_num [V,upperLog,lowerLog] at h
  linarith only [h]

theorem lower_gain_size : (1006/1000000:ℝ) < lowerGain ∧
    lowerGain < 1007/1000000 := by rw [lower_gain_exact]; norm_num

theorem improved_actual_Q_bounds : (823047/1000000:ℝ) < JointHMotherPayment.unroundedCoefficient ∧
    JointHMotherPayment.unroundedCoefficient < 907977/1000000 := by
  have hl : (823047/1000000:ℝ) < lowerRational := by rw [lower_rational_exact]; norm_num
  exact ⟨hl.trans actual_lower,actual_upper.trans upper_rational_size.2⟩

theorem improved_actual_target_bounds : (-9792/1000000:ℝ) <
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient ∧
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient < 75139/1000000 := by
  have ht := log_le_V (by norm_num : (1:ℝ) ≤ 5000/4469)
  have he : lowerRemainder < (75139/1000000:ℝ) := by rw [lower_remainder_exact]; norm_num
  refine ⟨actual_target_rational_bounds.1,?_⟩
  unfold lowerRemainder AnalyticTotalThreshold.target at *
  linarith only [actual_lower,ht,he]

theorem improved_rational_endpoints_straddle :
    lowerRational < 8*lowerLog (5000/4469) ∧ 8*V (5000/4469) < upperRational := by
  refine ⟨?_,rational_endpoints_straddle.2⟩
  rw [lower_rational_exact]
  norm_num [lowerLog]

end
end Wu2008DoubleSieve.GlobalLogRelationPayment
