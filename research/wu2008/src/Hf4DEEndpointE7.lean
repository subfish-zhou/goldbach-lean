import Hf4DECoefficients
noncomputable section
namespace Hf4DE
open Real

theorem hf4delogse7_log_0 : (3509131979/100000000000 : ℝ) ≤ log ((29/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((14/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((29/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((14/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (1754565991/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((14/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((29/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (501097807163/500000000000 : ℝ)) (u := (1002195614327/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse7_log_1 : (854721667/50000000000 : ℝ) ≤ log ((59/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((29/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((59/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((29/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (1709443337/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((29/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((59/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (1001068973029/1000000000000 : ℝ)) (u := (100106897303/100000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse7_log_2 : (2597548639/100000000000 : ℝ) ≤ log ((39/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((19/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((39/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((19/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (2597548641/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((19/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((39/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (1001624786437/1000000000000 : ℝ)) (u := (500812393219/500000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse7_log_3 : (126904643/12500000000 : ℝ) ≤ log ((99/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((49/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((99/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((49/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (1015237147/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((49/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((99/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (125079340571/125000000000 : ℝ)) (u := (1000634724569/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse7_log_4 : (1107056293/50000000000 : ℝ) ≤ log ((137/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((67/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((137/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((67/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (2214112589/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((67/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((137/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (62586548643/62500000000 : ℝ)) (u := (1001384778289/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse7_log_5 : (314567517/20000000000 : ℝ) ≤ log ((219/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((109/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ∧ log ((219/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((109/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ≤ (393209397/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((109/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (b := ((219/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (l := (1000983506817/1000000000000 : ℝ)) (u := (500491753409/500000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse7_log_6 : (267795613/100000000000 : ℝ) ≤ log ((219/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((109/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ∧ log ((219/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((109/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ≤ (8368613/3125000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((109/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (b := ((219/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (l := (500083693133/500000000000 : ℝ)) (u := (1000167386267/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse7_log_7 : (2519385539/100000000000 : ℝ) ≤ log ((157/5 : ℝ)+(-59/10 : ℝ)*TerminalE.radical)-log ((154/5 : ℝ)+(-29/5 : ℝ)*TerminalE.radical) ∧ log ((157/5 : ℝ)+(-59/10 : ℝ)*TerminalE.radical)-log ((154/5 : ℝ)+(-29/5 : ℝ)*TerminalE.radical) ≤ (1259692771/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((154/5 : ℝ)+(-29/5 : ℝ)*TerminalE.radical)) (b := ((157/5 : ℝ)+(-59/10 : ℝ)*TerminalE.radical)) (l := (1001575856321/1000000000000 : ℝ)) (u := (500787928161/500000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse7_log_8 : (918324087/50000000000 : ℝ) ≤ log ((157/5 : ℝ)+(59/10 : ℝ)*TerminalE.radical)-log ((154/5 : ℝ)+(29/5 : ℝ)*TerminalE.radical) ∧ log ((157/5 : ℝ)+(59/10 : ℝ)*TerminalE.radical)-log ((154/5 : ℝ)+(29/5 : ℝ)*TerminalE.radical) ≤ (114790511/6250000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((154/5 : ℝ)+(29/5 : ℝ)*TerminalE.radical)) (b := ((157/5 : ℝ)+(59/10 : ℝ)*TerminalE.radical)) (l := (250287141051/250000000000 : ℝ)) (u := (200229712841/200000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4determse7_term_0 : (-2432346209/100000000000 : ℝ) ≤ (TerminalESigned.coeffU)*(log ((29/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((14/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffU)*(log ((29/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((14/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-1216173103/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-34657377107/50000000000 : ℝ) ≤ (TerminalESigned.coeffU) ∧ (TerminalESigned.coeffU) ≤ (-69314754213/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_0]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (69314754213/100000000000 : ℝ) ≤ -(TerminalESigned.coeffU) ∧ -(TerminalESigned.coeffU) ≤ (34657377107/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse7_log_0 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse7_term_1 : (-1287961541/100000000000 : ℝ) ≤ (TerminalESigned.coeffThree)*(log ((59/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((29/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffThree)*(log ((59/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((29/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-643980769/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-4708994709/6250000000 : ℝ) ≤ (TerminalESigned.coeffThree) ∧ (TerminalESigned.coeffThree) ≤ (-75343915343/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_1]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (75343915343/100000000000 : ℝ) ≤ -(TerminalESigned.coeffThree) ∧ -(TerminalESigned.coeffThree) ≤ (4708994709/6250000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse7_log_1 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse7_term_2 : (-705048917/50000000000 : ℝ) ≤ (TerminalESigned.coeffOne)*(log ((39/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((19/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffOne)*(log ((39/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((19/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-176262229/12500000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-27142857143/50000000000 : ℝ) ≤ (TerminalESigned.coeffOne) ∧ (TerminalESigned.coeffOne) ≤ (-10857142857/20000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_2]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (10857142857/20000000000 : ℝ) ≤ -(TerminalESigned.coeffOne) ∧ -(TerminalESigned.coeffOne) ≤ (27142857143/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse7_log_2 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse7_term_3 : (19709233/3125000000 : ℝ) ≤ (TerminalESigned.coeffSeven)*(log ((99/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((49/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffSeven)*(log ((99/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((49/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (630695459/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (12424593809/20000000000 : ℝ) ≤ (TerminalESigned.coeffSeven) ∧ (TerminalESigned.coeffSeven) ≤ (31061484523/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_3]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse7_log_3 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse7_term_4 : (543322801/100000000000 : ℝ) ≤ (TerminalESigned.coeffFive)*(log ((137/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((67/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffFive)*(log ((137/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((67/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (543322803/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (4907815481/20000000000 : ℝ) ≤ (TerminalESigned.coeffFive) ∧ (TerminalESigned.coeffFive) ≤ (12269538703/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_4]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse7_log_4 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse7_term_5 : (590583601/25000000000 : ℝ) ≤ (TerminalESigned.minusCoeff (3/4))*(log ((219/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((109/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.minusCoeff (3/4))*(log ((219/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((109/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ≤ (236233441/10000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (150195698991/100000000000 : ℝ) ≤ (TerminalESigned.minusCoeff (3/4)) ∧ (TerminalESigned.minusCoeff (3/4)) ≤ (9387231187/6250000000 : ℝ) := by
    rw [TerminalESigned.coefficient_5]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse7_log_5 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse7_term_6 : (698520957/100000000000 : ℝ) ≤ (TerminalESigned.plusCoeff (3/4))*(log ((219/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((109/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.plusCoeff (3/4))*(log ((219/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((109/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ≤ (349260483/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (260841075681/100000000000 : ℝ) ≤ (TerminalESigned.plusCoeff (3/4)) ∧ (TerminalESigned.plusCoeff (3/4)) ≤ (130420537841/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_6]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse7_log_6 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse7_term_7 : (65527043/2500000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2))*(log ((157/5 : ℝ)+(-59/10 : ℝ)*TerminalE.radical)-log ((154/5 : ℝ)+(-29/5 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2))*(log ((157/5 : ℝ)+(-59/10 : ℝ)*TerminalE.radical)-log ((154/5 : ℝ)+(-29/5 : ℝ)*TerminalE.radical)) ≤ (655270431/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (104036547013/100000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2)) ∧ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2)) ≤ (52018273507/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_7]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse7_log_7 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse7_term_8 : (326647821/50000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2))*(log ((157/5 : ℝ)+(59/10 : ℝ)*TerminalE.radical)-log ((154/5 : ℝ)+(29/5 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2))*(log ((157/5 : ℝ)+(59/10 : ℝ)*TerminalE.radical)-log ((154/5 : ℝ)+(29/5 : ℝ)*TerminalE.radical)) ≤ (163323911/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (17784996921/50000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2)) ∧ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2)) ≤ (35569993843/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_8]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse7_log_8 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem e_cell_7_bounds : (459571/20000000 : ℝ) ≤ TerminalE.cellMass (14/5 : ℝ) (29/10 : ℝ) ∧ TerminalE.cellMass (14/5 : ℝ) (29/10 : ℝ) ≤ (8976/390625 : ℝ) := by
  have h0 := hf4determse7_term_0
  have h1 := hf4determse7_term_1
  have h2 := hf4determse7_term_2
  have h3 := hf4determse7_term_3
  have h4 := hf4determse7_term_4
  have h5 := hf4determse7_term_5
  have h6 := hf4determse7_term_6
  have h7 := hf4determse7_term_7
  have h8 := hf4determse7_term_8
  have hrat : TerminalESigned.rationalFull (29/10 : ℝ)-TerminalESigned.rationalFull (14/5 : ℝ) = (-9994366837895328143361720237383/12340329304815627959325520813524750 : ℝ) := by
    norm_num [TerminalESigned.rationalFull,TerminalE.leftArg,TerminalE.rightArg,TerminalESigned.rationalPart,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]
  rw [TerminalESigned.cellMass_collected (by norm_num : (1:ℝ) ≤ (14/5 : ℝ)) (by norm_num : (14/5 : ℝ) ≤ (29/10 : ℝ))]
  norm_num only [div_one] at hrat ⊢
  rw [hrat]
  simp only [TerminalESigned.affineLogs, TerminalESigned.coefficient_0,TerminalESigned.coefficient_1,TerminalESigned.coefficient_2,TerminalESigned.coefficient_3,TerminalESigned.coefficient_4,TerminalESigned.coefficient_5,TerminalESigned.coefficient_6,TerminalESigned.coefficient_7,TerminalESigned.coefficient_8] at *
  norm_num [TerminalESigned.leftMinus,TerminalESigned.leftPlus,TerminalESigned.rightMinus,TerminalESigned.rightPlus] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  constructor <;> linarith only [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2,h8.1,h8.2]

end Hf4DE
